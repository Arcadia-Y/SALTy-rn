#!/usr/bin/env python3
"""Shared extraction entry point: --family FAMILY (or all) --check/--write.

Clang, the frontend, profiles, intrinsic registry and declaration/ABI headers
form the trusted source bridge. Reproduction is not a correctness proof.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tempfile

from frontend import Extractor, Unsupported, require

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
OUT = ROOT / 'verification/lean/Salty/Generated'
DEFAULT_CC = '/opt/homebrew/Cellar/llvm/23.1.3_1/bin/clang'
CC = os.environ.get('EXTRACTION_CLANG') or (DEFAULT_CC if Path(DEFAULT_CC).exists() else shutil.which('clang'))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def profile_for(family, unsigned=False):
    # Each extraction owns its configuration; no family can mutate another call.
    profiles = json.loads((HERE / 'profiles.json').read_text())
    registry = json.loads((HERE / 'intrinsics.json').read_text())
    abi = json.loads((HERE / 'abi.json').read_text())
    require(family in profiles, 'unknown extraction profile: ' + family)
    common = profiles[family]
    variants = common['variants']
    require(len(variants) in (1, 2), 'profile must have one variant or a signed/unsigned pair')
    require(not unsigned or len(variants) == 2, 'profile has no unsigned variant')
    profile = {k: v for k, v in common.items() if k != 'variants'}
    profile.update(variants[int(unsigned)])
    profile['scalars'] = {name: abi['scalar_types'][name] for name in profile['scalars']}
    profile['sizeof'] = {name: abi['object_sizes'][name] for name in profile['sizeof']}
    profile['pointer_steps'] = {name: abi['object_sizes'][name[:-2]] for name in profile['pointer_steps']}
    profile['fields'] = abi['records'].get(profile['record'], {})
    profile['calls'] = {name: registry[key] for name, key in profile['calls'].items()}
    require(all(name == entry['name'] for name, entry in profile['calls'].items()), 'intrinsic registry name mismatch')
    return profile


def extract_family(family, source, side, tmp, unsigned=False, real=True, dependencies=None):
    profile = profile_for(family, unsigned)
    require(side in ('source', 'target'), 'unknown extraction side')
    name = 'test_neon' if side == 'source' else 'test_rvv'
    arch = ['--target=aarch64'] if side == 'source' else ['--target=riscv64', '-march=rv64gcv', '-mabi=lp64d']
    uncommented = re.sub(r'/\*.*?\*/|//[^\n]*', '', source, flags=re.S)
    directives = [line.strip() for line in uncommented.splitlines() if line.lstrip().startswith('#')]
    require(directives == profile[side + '_directives'], 'source directives must match profile exactly')
    stripped = re.sub(r'^\s*#[^\n]*', '', uncommented, flags=re.M)
    require(not any(token in source for token in ['%:', '??', '\\\n', '\\\r']) and '#' not in stripped
            and not re.search(r'\b_Pragma\b', uncommented), 'source preprocessor directives/pragmas/splices unsupported')
    context, interface = HERE / (family + '_context.h'), HERE / (family + '_intrinsics.h')
    # Helper interpretations are fixed independently of the family entry point.
    if profile['helpers']:
        canonical = (ROOT / 'src/verification_bw/xnn_minimal.h').read_text()
        for helper in profile['helpers']:
            pattern = r'static inline size_t ' + re.escape(helper) + r'\(size_t a, size_t b\) \{[^}]*\}'
            original, extracted = re.search(pattern, canonical), re.search(pattern, context.read_text())
            require(original and extracted and original.group() == extracted.group(), 'helper definition drift: ' + helper)
    common = [CC, *arch, '-ffreestanding', '-std=c11', '-Werror']
    if real:
        headers = '#include <stdint.h>\n#include <stddef.h>\n#include <' + ('arm_neon.h' if side == 'source' else 'riscv_vector.h') + '>\n'
        path = tmp / 'real.c'
        path.write_text(headers + '\n#include "' + str(context) + '"\n' + source)
        subprocess.run(common + ['-O2', '-c', str(path), '-o', str(tmp / 'real.o'),
                                 '-MD', '-MF', str(tmp / 'real.d')], check=True, capture_output=True)
        if dependencies is not None:
            deps = shlex.split((tmp / 'real.d').read_text().replace('\\\n', ' '))[1:]
            dependencies.update(Path(dep).resolve() for dep in deps if Path(dep).resolve() != path.resolve())
    path = tmp / 'model.c'
    path.write_text('#include "' + str(interface) + '"\n#include "' + str(context) + '"\n' + source)
    p = subprocess.run(common + ['-nostdinc', '-fsyntax-only', '-Xclang', '-ast-dump=json', str(path)], check=True, capture_output=True, text=True)
    tu = json.loads(p.stdout)
    require(tu['kind'] == 'TranslationUnitDecl', 'expected complete translation unit')
    origin = None
    allowed_headers = {str(interface), str(context)}
    for n in tu['inner']:
        loc = n.get('loc', {})
        if not loc:
            require(n.get('isImplicit'), 'unexpected location-free declaration')
            continue
        origin = loc.get('file', origin)
        if 'includedFrom' in loc:
            require(origin in allowed_headers, 'declaration from untrusted include: ' + str(origin))
        else:
            require(origin == str(path), 'unexpected main-file origin')
    main_nodes = [n for n in tu['inner'] if n.get('loc') and 'includedFrom' not in n['loc']]
    require(len(main_nodes) == 1 and main_nodes[0].get('name') == name,
            'source must contain exactly the selected function, without extra top-level declarations')
    trusted_calls = {n['id'] for n in tu['inner'] if n.get('name') in profile['calls']
                     and n['kind'] == 'FunctionDecl' and 'includedFrom' in n.get('loc', {})}
    require(len(trusted_calls) == len(profile['calls']), 'trusted interface declarations missing or duplicated')
    return Extractor(profile, trusted_calls).function(main_nodes[0], name)


def pretty(s):
    return s.replace('(.seq ', '(.seq\n  ').replace(' (.seq\n', '\n  (.seq\n')


def artifacts(family):
    outputs, sources, dependencies = {}, {}, set()
    profiles = json.loads((HERE / 'profiles.json').read_text())[family]['variants']
    require(len(profiles) in (1, 2), 'profile must have one variant or a signed/unsigned pair')
    with tempfile.TemporaryDirectory(prefix='salty-extract-') as tmp:
        for unsigned in range(len(profiles)):
            profile = profile_for(family, bool(unsigned))
            kernel, namespace = profile['kernel'], profile['namespace']
            for side, lean in [('source', 'neon'), ('target', 'rvv')]:
                relative = f'kernels/{side}/{kernel}.c'
                source = (ROOT / relative).read_text()
                model = extract_family(family, source, side, Path(tmp), bool(unsigned), dependencies=dependencies)
                sources[relative] = sha(source.encode())
                content = ('-- Generated by verification/extraction/extract.py --family ' + family + '; do not edit.\n'
                           '-- Source SHA-256: ' + sources[relative] + '\n'
                           'import Salty.Model.CByte\n\nnamespace Salty.Generated.' + namespace + '\nopen CByte\n\n'
                           'def ' + lean + ' : Stmt :=\n  ' + pretty(model) + '\n\nend Salty.Generated.' + namespace + '\n')
                outputs[OUT / (namespace + lean.title() + '.lean')] = content
    trusted = ['extract.py', 'frontend.py', 'profiles.json', 'intrinsics.json', 'abi.json',
               'extract_' + family + '.py', family + '_context.h', family + '_intrinsics.h']
    provenance = {'schema': 2, 'claim': 'AST provenance only; see separately checked Lean theorem registry',
                  'abi': 'LP64, little endian, 8-bit bytes', 'profile': family,
                  'compiler': subprocess.run([CC, '--version'], capture_output=True, text=True, check=True).stdout,
                  'flags': ['-ffreestanding', '-std=c11', '-Werror', '-nostdinc (model only)', '--target=aarch64 (NEON)', '--target=riscv64 -march=rv64gcv -mabi=lp64d (RVV)'],
                  'sources': sources, 'trusted_files': {str((HERE / n).relative_to(ROOT)): sha((HERE / n).read_bytes()) for n in trusted},
                  'models': {str(p.relative_to(ROOT)): sha(s.encode()) for p, s in outputs.items()}}
    resource = Path(subprocess.run([CC, '-print-resource-dir'], check=True, capture_output=True, text=True).stdout.strip())
    provenance['real_header_dependency_closure'] = {
        ('clang-resource/' + str(path.relative_to(resource)) if path.is_relative_to(resource)
         else str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)): sha(path.read_bytes())
        for path in sorted(dependencies)}
    outputs[HERE / (family + '_provenance.json')] = json.dumps(provenance, indent=2, sort_keys=True) + '\n'
    return outputs


def main(family=None):
    parser = argparse.ArgumentParser(description=__doc__)
    if family is None:
        parser.add_argument('--family', default='all', choices=['all', *json.loads((HERE / 'profiles.json').read_text())])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    args = parser.parse_args()
    selected = family or args.family
    families = json.loads((HERE / 'profiles.json').read_text()) if selected == 'all' else [selected]
    for family in families:
        for path, content in artifacts(family).items():
            if args.write:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            elif not path.exists() or path.read_text() != content:
                raise SystemExit('stale extraction artifact: ' + str(path.relative_to(ROOT)))
        print(f'{family}: AST-derived programs and provenance ' + ('generated' if args.write else 'reproduced'))


if __name__ == '__main__':
    main()
