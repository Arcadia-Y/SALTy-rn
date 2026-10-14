#!/usr/bin/env python3
"""Reproduce registered proofs, supporting lemmas, and repair regressions."""
import os
from pathlib import Path
import platform
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'verification/lean'
BUILD = ROOT / 'verification/tests/.build'

def run(args, **kwargs):
    return subprocess.run(args, check=True, **kwargs)

run([sys.executable, str(ROOT / 'verification/check_layout.py')])
run([sys.executable, str(ROOT / 'verification/test_layout.py')])
run([sys.executable, str(ROOT / 'verification/extraction/extract.py'), '--check'])
run([sys.executable, '-m', 'unittest', 'discover', '-s', str(ROOT / 'verification/extraction'), '-p', 'test_*.py'])
run(['lake', 'build'], cwd=LEAN)
run(['lake', 'env', 'lean', 'Regression.lean'], cwd=LEAN)
run(['lake', 'exe', 'rdsum_regression'], cwd=LEAN)
audit = run(['lake', 'env', 'lean', 'Audit.lean'], cwd=LEAN, capture_output=True, text=True).stdout
print(audit, end='')
for names in re.findall(r'depends on axioms: \[([^\]]*)\]', audit):
    unexpected = {name.strip() for name in names.split(',')} - {'propext', 'Quot.sound', 'Classical.choice'}
    if unexpected: raise SystemExit(f'Unexpected proof axioms: {unexpected}')
if 'sorryAx' in audit: raise SystemExit('Incomplete Lean proof')
run([sys.executable, str(ROOT / 'verification/audit.py')])
run([sys.executable, str(ROOT / 'verification/tests/check_rvv_syntax.py')])
if platform.machine() not in ('arm64', 'aarch64'):
    raise SystemExit('Native NEON regressions require an AArch64 host; no tests silently skipped.')
BUILD.mkdir(exist_ok=True)
for name in ['repairs', 'fp_repairs', 'padding', 'transpose', 'quantized_add']:
    run([os.environ.get('CC', 'clang'), '-std=c11', '-O1', '-ffp-contract=off',
         '-fsanitize=address,undefined', str(ROOT / f'verification/tests/{name}.c'),
         '-o', str(BUILD / name)])
    run([str(BUILD / name)])
prefix = os.environ.get('CVC5_PREFIX')
if prefix:
    run([os.environ.get('CXX', 'clang++'), '-std=c++17', '-O0', '-I' + prefix + '/include',
         str(ROOT / 'verification/tests/cvc5_masked_load.cpp'), '-L' + prefix + '/lib',
         '-Wl,-rpath,' + prefix + '/lib', '-lcvc5', '-o', str(BUILD / 'cvc5_masked_load')])
    run([str(BUILD / 'cvc5_masked_load')])
else:
    print('cvc5 adapter test not run: set CVC5_PREFIX to enable it.')
print('Registered proof and supporting checks passed. Revised scope: 11 proved pairs; 25 implemented pairs remain unproved (see coverage.json).')
