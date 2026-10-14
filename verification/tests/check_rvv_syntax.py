#!/usr/bin/env python3
"""Cross-compile the edited target files with the real RVV intrinsic header."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
DEFAULT = '/opt/homebrew/Cellar/llvm/23.1.3_1/bin/clang'
CC = os.environ.get('RISCV_CLANG') or (DEFAULT if Path(DEFAULT).exists() else shutil.which('clang'))
PRELUDE = '''#include <stddef.h>
#include <stdint.h>
#include <riscv_vector.h>
#define assert(x) ((void)0)
#define XNN_OOB_READS
#define XNN_UNPREDICTABLE(x) (x)
struct xnn_f32_default_params { char unused; };
struct xnn_f32_minmax_params { struct { float min,max; } scalar; };
union xnn_qs8_mul_minmax_params { struct { int8_t a_zero_point,b_zero_point; float scale; int16_t output_zero_point; int8_t output_min,output_max; } scalar; };
struct xnn_qs8_cvt_params { struct { int16_t input_zero_point; int32_t multiplier; int16_t output_zero_point; } scalar; };
struct xnn_qs8_add_minmax_params { struct { int8_t a_zero_point,b_zero_point; int32_t bias,a_multiplier,b_multiplier,shift; int16_t output_zero_point; int8_t output_min,output_max; } scalar; };
struct xnn_qu8_add_minmax_params { struct { uint8_t a_zero_point,b_zero_point; int32_t bias,a_multiplier,b_multiplier,shift; int16_t output_zero_point; uint8_t output_min,output_max; } scalar; };
'''
NAMES = ['qu8-vadd-minmax', 'qs8-vadd-minmax', 'x32-transposec', 'f32-conv-hwc2chw', 'qs8-vmul-minmax-fp32', 'f32-dwconv-minmax', 'f32-spmm-minmax', 'f32-raddstoreexpminusmax', 'qs8-vcvt'] + ['f32-' + op for op in ['vadd', 'vsub', 'vmul', 'vdiv', 'vmin', 'vmax', 'vmulc', 'vsqrt']]
with tempfile.TemporaryDirectory(prefix='salty-rvv-') as tmp:
    for name in NAMES:
        source = Path(tmp) / (name + '.c')
        source.write_text(PRELUDE + (ROOT / 'kernels/target' / (name + '.c')).read_text())
        subprocess.run([CC, '--target=riscv64', '-march=rv64gcv', '-mabi=lp64d',
                        '-ffreestanding', '-std=c11', '-O2', '-ffp-contract=off',
                        '-Werror', '-c', str(source), '-o', str(Path(tmp) / (name + '.o'))], check=True)
print(f'real RVV headers and code generation: {len(NAMES)} repaired targets passed')
