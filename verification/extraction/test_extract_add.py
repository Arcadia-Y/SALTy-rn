#!/usr/bin/env python3
"""Regression tests for extraction fidelity, not kernel-equivalence evidence."""
from pathlib import Path
import subprocess
import tempfile
import unittest

from extract_add import ROOT, Unsupported, extract

class ExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix='salty-extraction-test-')
        cls.path = Path(cls.tmp.name)
        cls.source = {side: (ROOT / f'kernels/{side}/qs8-vadd-minmax.c').read_text() for side in ['source', 'target']}
        cls.model = {side: extract(s, side, cls.path) for side, s in cls.source.items()}

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def changed(self, side, old, new, reject=False):
        self.assertIn(old, self.source[side])
        modified = self.source[side].replace(old, new, 1)
        try:
            result = extract(modified, side, self.path)
        except (Unsupported, subprocess.CalledProcessError):
            return
        self.assertFalse(reject, 'unsupported mutation was accepted')
        self.assertNotEqual(result, self.model[side], 'semantic mutation disappeared from model')

    def test_control_and_tail(self):
        for old,new in [('batch >= 16', 'batch > 16'), ('batch -= 16', 'batch -= 8'),
                        ('batch >= (8', 'batch > (8'), ('batch & (4', 'batch & (2'),
                        ('while (batch != 0)', 'while (batch == 0)'), ('batch = 0;', 'batch = 1;')]:
            with self.subTest(old=old): self.changed('source', old, new)
        self.changed('target', 'batch > 0', 'batch >= 0')
        self.changed('target', 'batch -= vl', 'batch += vl')

    def test_dataflow_and_parameters(self):
        for old,new in [('input_a += 8', 'input_a += 4'), ('output += 4', 'output += 2'),
                        ('vld1_s8(input_b)', 'vld1_s8(input_a)'),
                        ('params->scalar.a_multiplier', 'params->scalar.b_multiplier'),
                        ('-params->scalar.shift', 'params->scalar.shift'),
                        ('vget_high_s16(vxa01234567)', 'vget_low_s16(vxa01234567)'),
                        ('vext_s8(vout01234567, vout01234567, 4)', 'vext_s8(vout01234567, vout01234567, 2)'),
                        ('vreinterpret_u32_s8(vout01234567), 0', 'vreinterpret_u32_s8(vout01234567), 1'),
                        ('vst1_lane_s8(output, vout01234567, 0);', '')]:
            with self.subTest(old=old): self.changed('source', old, new)
        self.changed('target', 'params->scalar.a_zero_point', 'params->scalar.b_zero_point')
        self.changed('target', 'vxb32, vl)', 'vxa32, vl)')
        self.changed('target', 'vacc, 0, __RISCV_VXRM_RDN', 'vacc, 1, __RISCV_VXRM_RDN')
        self.changed('target', 'vacc, 0, __RISCV_VXRM_RDN', 'vacc, 0, __RISCV_VXRM_RNU')

    def test_shift_repair_branches(self):
        for old,new in [('0u - (uint32_t)', '1u - (uint32_t)'), ('& 255u', '& 127u'),
                        ('shift_byte >= 128u', 'shift_byte > 128u'), ('? 256 : 0', '? 255 : 0'),
                        ('shift <= -32 || shift >= 32', 'shift < -32 || shift > 32'),
                        ('shift < 0', 'shift > 0'), ('(size_t)-shift', '(size_t)shift'),
                        ('__RISCV_VXRM_RNU, vl', '__RISCV_VXRM_RDN, vl'),
                        ('__riscv_vmv_v_x_i32m8(0, vl)', '__riscv_vmv_v_x_i32m8(1, vl)')]:
            with self.subTest(old=old): self.changed('target', old, new)

    def test_fail_closed(self):
        mutations = [
            ('input_a += 8;', 'input_a++;'),
            ('input_a += 8;', '*(int8_t*) input_a = 1;'),
            ('input_a += 8;', 'if (batch == 1) return;'),
            ('input_a += 8;', 'switch (batch) { case 1: break; }'),
            ('input_a += 8;', 'input_a += 8; __builtin_trap();'),
            ('int8x8_t va01234567', 'volatile int8x8_t va01234567'),
            ('int8x8_t va01234567', 'static int8x8_t va01234567'),
            ('void test_neon(', '#define vrshlq_s32 vmulq_s32\nvoid test_neon('),
        ]
        for old, new in mutations:
            with self.subTest(old=old, new=new): self.changed('source', old, new, reject=True)

    def test_reject_translation_unit_overrides(self):
        additions = [
            '\nvoid salty_assert(int condition) { __builtin_trap(); }',
            '\nint8x8_t vld1_s8(const int8_t* p) { return vld1_s8(p); }',
            '\nextern int8x8_t vld1_s8(const int8_t* p) __asm__("other_load");',
            '\nint unexpected_global;',
            '\nvoid another_function(void) {}',
            '\n_Pragma("weak salty_assert")',
        ]
        for addition in additions:
            with self.subTest(addition=addition):
                with self.assertRaises((Unsupported, subprocess.CalledProcessError)):
                    extract(self.source['source'] + addition, 'source', self.path)

    def test_reject_directive_spellings_and_includes(self):
        override = self.path / 'override.h'
        override.write_text('__asm__(".text\\n.globl salty_assert\\nsalty_assert:\\nbrk #0\\n");')
        prefixes = [f'%:include "{override}"\n', f'??=include "{override}"\n',
                    '#\\\ninclude "' + str(override) + '"\n',
                    '_Prag' + '\\\n' + 'ma("weak salty_assert")\n']
        for prefix in prefixes:
            with self.subTest(prefix=prefix):
                with self.assertRaises(Unsupported):
                    extract(prefix + self.source['source'], 'source', self.path)

    def test_nonsemantic_comment(self):
        self.assertEqual(extract('/* additional comment */\n' + self.source['source'], 'source', self.path),
                         self.model['source'])

if __name__ == '__main__':
    unittest.main()
