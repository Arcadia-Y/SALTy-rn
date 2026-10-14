#!/usr/bin/env python3
"""Regression tests for extraction fidelity, not kernel-equivalence evidence."""
from pathlib import Path
import subprocess
import tempfile
import unittest

from extract_lrelu import ROOT, Unsupported, extract

class ExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix='salty-extraction-test-')
        cls.path = Path(cls.tmp.name)
        cls.source = {side: (ROOT / f'kernels/{side}/qs8-vlrelu.c').read_text() for side in ['source', 'target']}
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

    def test_control_constants_and_operators(self):
        for old, new in [('batch >= 8', 'batch > 8'), ('batch -= 8', 'batch -= 4'),
                         ('batch & (4', 'batch & (2'), ('batch <= 7', 'batch <= 6'),
                         ('batch != 0', 'batch == 0')]:
            with self.subTest(old=old): self.changed('source', old, new)
        self.changed('target', 'batch > 0', 'batch >= 0')
        self.changed('target', 'batch -= vl', 'batch += vl')

    def test_dataflow_parameters_rounding(self):
        for old, new in [('input += 8', 'input += 4'), ('output += 4', 'output += 2'),
                         ('vld1_s8(input)', 'vld1_s8(output)'),
                         ('params->scalar.input_zero_point', 'params->scalar.output_zero_point'),
                         ('-params->scalar.positive_multiplier', 'params->scalar.positive_multiplier'),
                         ('vshlq_n_s16(vacc, 7)', 'vshlq_n_s16(vacc, 6)'),
                         ('vqaddq_s16(vacc, voutput_zero_point)', 'vqaddq_s16(vacc, vinput_zero_point)'),
                         ('vext_s8(vy, vy, 4)', 'vext_s8(vy, vy, 2)'),
                         ('vreinterpret_u32_s8(vy), 0', 'vreinterpret_u32_s8(vy), 1'),
                         ('vst1_lane_s8(output, vy, 0);', '')]:
            with self.subTest(old=old): self.changed('source', old, new)
        self.changed('target', '__riscv_vle8_v_i8m2(input, vl)', '__riscv_vle8_v_i8m2(input, 1)')
        self.changed('target', 'prod, 15, __RISCV_VXRM_RNU', 'prod, 14, __RISCV_VXRM_RNU')
        self.changed('target', 'prod, 15, __RISCV_VXRM_RNU', 'prod, 15, __RISCV_VXRM_RDN')
        self.changed('target', '(int16_t) -params->scalar.positive_multiplier', '(int8_t) -params->scalar.positive_multiplier')

    def test_selection_dataflow(self):
        self.changed('source', 'vcltq_s16(vacc, vmovq_n_s16(0))', 'vcltq_s16(vmovq_n_s16(0), vacc)')
        self.changed('source', 'vbslq_s16(vmask, vpositive_multiplier, vnegative_multiplier)',
                     'vbslq_s16(vmask, vnegative_multiplier, vpositive_multiplier)')
        self.changed('target', 'params->scalar.negative_multiplier', 'params->scalar.positive_multiplier')
        self.changed('target', 'vmerge_vxm_i16m4(vneg_mult, positive_multiplier, vmask, vl)',
                     'vmerge_vxm_i16m4(vneg_mult, negative_multiplier, vmask, vl)')
        self.changed('target', 'vwmul_vv_i32m8(vacc, vmultiplier, vl)',
                     'vwmul_vv_i32m8(vacc, vacc, vl)')

    def test_fail_closed(self):
        mutations = [
            ('input += 8;', 'input++;'),
            ('input += 8;', '*(int8_t*) input = 1;'),
            ('input += 8;', 'if (batch == 1) return;'),
            ('input += 8;', 'do { input += 8; } while (batch);'),
            ('input += 8;', 'input += 8; __builtin_trap();'),
            ('int8x8_t vx', 'volatile int8x8_t vx'),
            ('int8x8_t vx', 'static int8x8_t vx'),
            ('void test_neon(', '#define vqrdmulhq_s16 vqaddq_s16\nvoid test_neon('),
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
