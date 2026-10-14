#!/usr/bin/env python3
"""Packing AST fidelity checks; finite tests, not equivalence proofs."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from extract_pack import ROOT, Unsupported, extract

class ExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix='salty-pack-extraction-test-')
        cls.path = Path(cls.tmp.name)
        cls.source = {side: (ROOT / f'kernels/{side}/x32-packw-gemm-goi.c').read_text()
                      for side in ['source', 'target']}
        cls.model = {side: extract(s, side, cls.path) for side, s in cls.source.items()}

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def changed(self, side, old, new, reject=False):
        self.assertIn(old, self.source[side])
        try:
            result = extract(self.source[side].replace(old, new, 1), side, self.path)
        except (Unsupported, subprocess.CalledProcessError):
            return
        self.assertFalse(reject, 'unsupported mutation accepted')
        self.assertNotEqual(result, self.model[side], 'semantic mutation lost')

    def test_loop_and_pointer_changes(self):
        for old, new in [('n >= 2', 'n > 2'), ('k >= 2', 'k > 2'), ('k -= 2', 'k -= 1'),
                         ('--g != 0', '--g != 1'), ('while (--k)', 'while (k--)'),
                         ('weights += nc * kc', 'weights += kc'),
                         ('packed_weights + extra_bytes', 'packed_weights + kc'),
                         ('*bias++', '*bias'), ('*w0++', '*w0'),
                         ('packed_weights += 2', 'packed_weights += 1')]:
            with self.subTest(old=old): self.changed('source', old, new)
        for old, new in [('k -= vl', 'k += vl'), ('w1 += vl', 'w1 += 1'),
                         ('2 * sizeof(uint32_t)', '4 * sizeof(uint32_t)')]:
            with self.subTest(old=old): self.changed('target', old, new)

    def test_lane_and_field_order(self):
        for old, new in [('vld2_lane_u32(w0, v00, 0)', 'vld2_lane_u32(w0, v00, 1)'),
                         ('vld1_lane_u32(w1, v00.val[0], 1)', 'vld1_lane_u32(w1, v00.val[0], 0)'),
                         ('vst1_u32(packed_weights + 2, v00.val[1])', 'vst1_u32(packed_weights + 2, v00.val[0])'),
                         ('v00.val[0] = vdup_n_u32(0)', 'v00.val[0] = vdup_n_u32(1)')]:
            with self.subTest(old=old): self.changed('source', old, new)
        self.changed('target', '__riscv_vcreate_v_u32m4x2(vw0, vw1)', '__riscv_vcreate_v_u32m4x2(vw1, vw0)')
        self.changed('target', '__riscv_vle32_v_u32m1(bias, 2)', '__riscv_vle32_v_u32m1(weights, 2)')

    def test_uninitialized_tuples(self):
        for new in ['', 'if (bias != NULL) v00.val[1] = vdup_n_u32(0);',
                    'while (g == 0) { v00.val[1] = vdup_n_u32(0); }']:
            with self.subTest(new=new):
                self.changed('source', 'v00.val[1] = vdup_n_u32(0);', new, reject=True)
        self.changed('source', 'uint32x2x2_t v00;', 'uint32x2x2_t v00; v00 = vld2_lane_u32(weights, v00, 0);', reject=True)

    def test_rejected_extensions(self):
        for old, new in [('size_t k = kc;', 'static size_t k = 1;'),
                         ('const uint32_t* w0 = weights;', 'volatile const uint32_t* w0 = weights;'),
                         ('k -= vl;', 'k -= vl; __builtin_trap();'),
                         ('k -= vl;', 'if (k == 1) return;'),
                         ('*bias++', '*++bias'),
                         ('--g != 0', '--g == 0')]:
            side = 'source' if old in ('*bias++', '--g != 0') else 'target'
            with self.subTest(old=old): self.changed(side, old, new, reject=True)

    def test_preprocessor_and_overrides(self):
        self.changed('target', '#define XNN_LIKELY(x) (x)', '#define XNN_LIKELY(x) 0', reject=True)
        for side in ['source', 'target']:
            for addition in ['\nvoid salty_assert(int x) {}', '\nuint32_t injected;', '\n_Pragma("weak salty_assert")']:
                with self.subTest(side=side, addition=addition):
                    with self.assertRaises((Unsupported, subprocess.CalledProcessError)):
                        extract(self.source[side] + addition, side, self.path)
            for prefix in ['#define assert(x) ((void)0)\n', '%:define XNN_LIKELY(x) 0\n', '??=define XNN_LIKELY(x) 0\n']:
                with self.subTest(side=side, prefix=prefix):
                    with self.assertRaises(Unsupported):
                        extract(prefix + self.source[side], side, self.path)

    def test_comments(self):
        for side in ['source', 'target']:
            self.assertEqual(extract('/* unchanged */\n' + self.source[side], side, self.path), self.model[side])

if __name__ == '__main__':
    unittest.main()
