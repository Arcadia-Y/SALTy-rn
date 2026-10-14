#!/usr/bin/env python3
"""Regression tests for extraction fidelity, not kernel-equivalence evidence."""
from pathlib import Path
import subprocess
import tempfile
import unittest

from extract_s8 import ROOT, Unsupported, extract

class ExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix='salty-extraction-test-')
        cls.path = Path(cls.tmp.name)
        cls.source = {side: (ROOT / f'kernels/{side}/s8-vclamp.c').read_text() for side in ['source', 'target']}
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
        for old, new in [('batch >= 64', 'batch > 64'), ('batch -= 64', 'batch -= 32'),
                         ('batch >= 8', 'batch >= 16'), ('batch & 4', 'batch & 2'),
                         ('batch != 0', 'batch == 0')]:
            with self.subTest(old=old): self.changed('source', old, new)
        self.changed('target', 'batch > 0', 'batch >= 0')
        self.changed('target', 'batch -= vl', 'batch += vl')

    def test_dataflow_and_memory(self):
        for old, new in [('input += 16', 'input += 8'), ('output += 4', 'output += 2'),
                         ('vld1q_s8(input)', 'vld1q_s8(output)'),
                         ('vmaxq_s8(vacc0, voutput_min)', 'vminq_s8(vacc0, voutput_min)'),
                         ('params->scalar.max', 'params->scalar.min'),
                         ('vext_s8(vacc, vacc, 4)', 'vext_s8(vacc, vacc, 2)'),
                         ('vreinterpret_u32_s8(vacc), 0', 'vreinterpret_u32_s8(vacc), 1'),
                         ('vst1_lane_s8(output, vacc, 0);', '')]:
            with self.subTest(old=old): self.changed('source', old, new)
        self.changed('target', '__riscv_vle8_v_i8m8(input, vl)', '__riscv_vle8_v_i8m8(input, 1)')
        self.changed('target', '(int8_t) params->scalar.min', '(int8_t) params->scalar.max')

    def test_fail_closed(self):
        mutations = [
            ('input += 16;', 'input++;'),
            ('input += 16;', '*(int8_t*) input = 1;'),
            ('input += 16;', 'if (batch == 1) return;'),
            ('input += 16;', 'do { input += 16; } while (batch);'),
            ('input += 16;', 'input += 16; __builtin_trap();'),
            ('int8x16_t vacc0', 'volatile int8x16_t vacc0'),
            ('int8x16_t vacc0', 'static int8x16_t vacc0'),
            ('void test_neon(', '#define vmaxq_s8 vminq_s8\nvoid test_neon('),
        ]
        for old, new in mutations:
            with self.subTest(old=old, new=new): self.changed('source', old, new, reject=True)

    def test_reject_translation_unit_overrides(self):
        additions = [
            '\nvoid salty_assert(int condition) { __builtin_trap(); }',
            '\nint8x16_t vld1q_s8(const int8_t* p) { return vdupq_n_s8(0); }',
            '\nextern int8x16_t vld1q_s8(const int8_t* p) __asm__("other_load");',
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
