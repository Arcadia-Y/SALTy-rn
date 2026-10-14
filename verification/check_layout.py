#!/usr/bin/env python3
"""Enforce the review boundary between definitions and proof implementations.

This is an architectural check, not a replacement for Lean or human semantic
review. Model and Spec must be readable without importing implementation proofs.
"""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent / 'lean'
SALTY = ROOT / 'Salty'


def code_only(text):
    """Mask nested Lean comments and string literals, preserving line positions."""
    result = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                result[i:i+2] = '  '
                depth += 1
                i += 2
                continue
            if text.startswith('-/', i):
                result[i:i+2] = '  '
                depth -= 1
                i += 2
                continue
            if text[i] != '\n':
                result[i] = ' '
            i += 1
            continue
        if string:
            if text[i] == '\\' and i + 1 < len(text):
                result[i:i+2] = '  '
                i += 2
                continue
            if text[i] == '"':
                string = False
            if text[i] != '\n':
                result[i] = ' '
            i += 1
            continue
        if text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            result[i:end] = ' ' * (end-i)
            i = end
            continue
        if text.startswith('/-', i):
            result[i:i+2] = '  '
            depth = 1
            i += 2
            continue
        if text[i] == '"':
            string = True
            result[i] = ' '
        i += 1
    return ''.join(result)


def is_definition_module(name):
    return name.startswith(('Salty.Model.', 'Salty.Spec.')) or name == 'Salty.Specifications'


def main():
    modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p
               for p in SALTY.rglob('*.lean')}
    imports, errors = {}, []
    for name, path in sorted(modules.items()):
        source = code_only(path.read_text())
        imports[name] = re.findall(r'^\s*import\s+(\S+)', source, re.M)
        for dependency in imports[name]:
            if dependency.startswith('Salty.') and dependency not in modules:
                errors.append(f'{name}: missing local module {dependency}')
        if re.search(r'\b(sorry|admit|axiom|constant)\b', source):
            errors.append(f'{name}: unproved declaration or placeholder')
        if is_definition_module(name):
            if re.search(r'\b(theorem|lemma|example|opaque)\b', source):
                errors.append(f'{name}: proof declaration in definition layer')
            for dependency in imports[name]:
                if dependency != 'Std' and not is_definition_module(dependency):
                    errors.append(f'{name}: definition layer imports {dependency}')
                if name.startswith('Salty.Model.') and dependency != 'Std' and not dependency.startswith('Salty.Model.'):
                    errors.append(f'{name}: machine model imports non-model module {dependency}')
        if name.startswith('Salty.Generated.'):
            if imports[name] != ['Salty.Model.CByte']:
                errors.append(f'{name}: generated programs must import only Model.CByte')
        if name.startswith('Salty.Proofs.'):
            if any(d.startswith('Salty.Results') for d in imports[name]):
                errors.append(f'{name}: proof implementation imports public Results')
        if not (name.startswith(('Salty.Model.', 'Salty.Spec.', 'Salty.Proofs.',
                                 'Salty.Results.', 'Salty.Generated.', 'Salty.Examples.'))
                or name in {'Salty.Specifications', 'Salty.Results'}):
            errors.append(f'{name}: module outside the documented layers')
    # Check the transitive closure too, so an added umbrella cannot hide an edge.
    def visit(name, trail):
        if name in trail:
            errors.append('import cycle: ' + ' -> '.join(trail + [name]))
            return
        for dependency in imports.get(name, []):
            if dependency.startswith('Salty.') and not is_definition_module(dependency):
                errors.append(f'{trail[0] if trail else name}: transitive proof dependency {dependency}')
            elif dependency in imports:
                visit(dependency, trail + [name])
    for name in modules:
        if is_definition_module(name):
            visit(name, [])
    if errors:
        print('\n'.join(sorted(set(errors))), file=sys.stderr)
        return 1
    definitions = sum(is_definition_module(n) for n in modules)
    print(f'Layout passed: {definitions} definition/specification modules have no proof dependencies; '
          f'{len(modules)} modules checked.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
