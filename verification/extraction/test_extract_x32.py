#!/usr/bin/env python3
"""Transpose AST fidelity regressions; these do not count as equivalence proofs."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from extract_x32 import ROOT, Unsupported, extract

class ExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix='salty-x32-extraction-test-')
        cls.path = Path(cls.tmp.name)
        cls.source = {side: (ROOT / f'kernels/{side}/x32-transposec.c').read_text()
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

    def test_loop_and_stride_changes(self):
        for old, new in [('bh >= 2', 'bh > 2'), ('bh -= 2', 'bh -= 1'),
                         ('block_width < 2', 'block_width > 2'),
                         ('block_width != 0', 'block_width == 0'),
                         ('tile_height * input_stride', 'tile_width * output_stride'),
                         ('o1 = o0;', 'o0 = o1;'),
                         ('round_down_po2(block_height, 2)', 'round_down_po2(block_width, 2)'),
                         ('doz(block_width, tile_width)', 'doz(block_height, tile_width)')]:
            with self.subTest(old=old): self.changed('source', old, new)
        for old, new in [('bw -= vl', 'bw += vl'), ('input += vl', 'input += 1'),
                         ('o += 1', 'o += 2'), ('bh > 0', 'bh > 1')]:
            with self.subTest(old=old): self.changed('target', old, new)

    def test_word_order_and_memory_changes(self):
        for old, new in [('v0_0.val[1]', 'v0_0.val[0]'),
                         ('vzip_u32(v1_0, v1_1)', 'vzip_u32(v1_1, v1_0)'),
                         ('vld1_u32(i0)', 'vld1_u32(i1)'),
                         ('vmov_n_u32(0)', 'vmov_n_u32(1)'),
                         ('vst1_lane_u32(o1, v1_low, 0)', 'vst1_lane_u32(o1, v1_low, 1)')]:
            with self.subTest(old=old): self.changed('source', old, new)
        self.changed('target', 'bw = 1;', 'bw = 2;')
        self.changed('target', 'block_height == 0', 'block_height == 1')
        self.changed('target', 'o, output_stride, v, vl', 'o, input_stride, v, vl')
        self.changed('target', '__riscv_vle32_v_u32m8(i, vl)', '__riscv_vle32_v_u32m8(i, 1)')

    def test_rejected_extensions(self):
        for old, new in [('o += 1;', 'o++;'),
                         ('bh -= 1;', 'bh -= 1; __builtin_trap();'),
                         ('uint32_t* o = output;', 'volatile uint32_t* o = output;'),
                         ('size_t bw = block_width;', 'static size_t bw = 1;'),
                         ('bh -= 1;', '*o = 123;'),
                         ('bh -= 1;', 'if (bh == 1) return;')]:
            with self.subTest(old=old): self.changed('target', old, new, reject=True)

    def test_rejected_overrides(self):
        additions = ['\nsize_t doz(size_t a, size_t b) { return 0; }',
                     '\nvoid salty_assert(int x) { __builtin_trap(); }',
                     '\nuint32_t injected;', '\n_Pragma("weak salty_assert")']
        for addition in additions:
            with self.subTest(addition=addition):
                with self.assertRaises((Unsupported, subprocess.CalledProcessError)):
                    extract(self.source['source'] + addition, 'source', self.path)
        for prefix in ['#define doz(a,b) 0\n', '%:include "override.h"\n', '??=include "override.h"\n']:
            with self.subTest(prefix=prefix):
                with self.assertRaises(Unsupported):
                    extract(prefix + self.source['source'], 'source', self.path)

    def test_comment_invariance(self):
        self.assertEqual(extract('/* unchanged */\n' + self.source['source'], 'source', self.path),
                         self.model['source'])

if __name__ == '__main__':
    unittest.main()
