#!/usr/bin/env python3
"""Fail-closed row-sum extraction mutations; not equivalence proofs."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from extract_rdsum import ROOT, Unsupported, extract

class RowSumExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix='salty-rdsum-mutations-')
        cls.path = Path(cls.tmp.name)
        cls.sources = {(u, side): (ROOT / f'kernels/{side}/{"qu8" if u else "qs8"}-rdsum.c').read_text()
                       for u in (False, True) for side in ('source', 'target')}
        cls.models = {key: extract(s, key[1], cls.path, key[0]) for key, s in cls.sources.items()}

    @classmethod
    def tearDownClass(cls): cls.tmp.cleanup()

    def changed(self, u, side, old, new, reject=False):
        source = self.sources[u, side]
        self.assertTrue(old in source, 'mutation anchor missing: ' + old)
        try:
            model = extract(source.replace(old, new, 1), side, self.path, u)
        except (Unsupported, subprocess.CalledProcessError):
            return
        self.assertFalse(reject, 'unsupported mutation accepted')
        self.assertNotEqual(model, self.models[u, side], 'semantic change disappeared')

    def test_loop_and_zero_substitution(self):
        for u in (False, True):
            for side in ('source', 'target'):
                for old, new in [('rows != 0', 'rows == 0'), ('7 * input_stride', '6 * input_stride'),
                                 ('current_batch > 0', 'current_batch >= 0'), ('current_batch -= 7', 'current_batch -= 6'),
                                 ('current_batch < 2', 'current_batch < 3'), ('i1 = zero', 'i1 = input'),
                                 ('i6 + input_increment', 'i5 + input_increment')]:
                    with self.subTest(u=u, side=side, old=old): self.changed(u, side, old, new)
            self.changed(u, 'source', 'min(r, 252)', 'min(r, 251)')
            self.changed(u, 'source', 'doz(r, 252)', 'doz(r, 251)')
            self.changed(u, 'source', '--num_batches', 'num_batches -= 2')
            self.changed(u, 'target', 'channels -= vl', 'channels += vl')
            self.changed(u, 'target', 'output += vl', 'output += 1')

    def test_memory_and_intrinsic_dataflow(self):
        for u in (False, True):
            c = 'u' if u else 's'; r = 'u' if u else 'i'
            self.changed(u, 'source', f'vdupq_n_{c}32(0)', f'vdupq_n_{c}32(1)')
            self.changed(u, 'source', '&i0[0]', '&i0[1]')
            self.changed(u, 'source', 'channels & 4', 'channels & 2')
            self.changed(u, 'source', f'vextq_{c}32(vacc0, vacc0, 2)', f'vextq_{c}32(vacc0, vacc0, 1)')
            self.changed(u, 'source', f'vgetq_lane_{c}32(vacc0, 0)', f'vgetq_lane_{c}32(vacc0, 1)')
            self.changed(u, 'target', f'__riscv_vle8_v_{r}8m2(i0, vl)', f'__riscv_vle8_v_{r}8m2(i1, vl)')
            self.changed(u, 'target', f'__riscv_vse32_v_{r}32m8(output, vo, vl)', f'__riscv_vse32_v_{r}32m8(output, vo, 1)')

    def test_exact_floor_composition(self):
        for u in (False, True):
            self.changed(u, 'source', 'floor((rows + 251) / 252)', 'floor((rows + 250) / 252)')
            for replacement in ['floor(0.5)', 'floor((double)rows / 252.0)', 'floor(-(double)rows)',
                                'floor((float)rows)', 'floor((rows + 251) / 252) + 0.5']:
                self.changed(u, 'source', 'floor((rows + 251) / 252)', replacement, reject=True)

    def test_definite_initialization(self):
        for u in (False, True):
            byte = 'uint8x16_t' if u else 'int8x8_t'
            name = 'vin4' if u else 'vin0'
            self.changed(u, 'source', f'{byte} {name};', f'{byte} {name} = {name};', reject=True)
            load = 'vld1q_u8' if u else 'vld1_s8'
            self.changed(u, 'source', f'{name} = {load}(&i0[0]);', '', reject=True)
            self.changed(u, 'source', f'{name} = {load}(&i0[0]);', f'if (rows > 1) {name} = {load}(&i0[0]);', reject=True)
            self.changed(u, 'source', f'{name} = {load}(&i0[0]);', f'while (rows > 1) {{ {name} = {load}(&i0[0]); rows -= 1; }}', reject=True)

    def test_unsupported_and_translation_unit_injection(self):
        for u in (False, True):
            self.changed(u, 'target', 'output += vl;', 'output++;', reject=True)
            self.changed(u, 'target', 'output += vl;', '__builtin_trap();', reject=True)
            self.changed(u, 'target', 'output += vl;', 'return;', reject=True)
            self.changed(u, 'source', 'rows != 0', '(rows = 1)', reject=True)
            for suffix in ['\nvoid salty_assert(int c) {}', '\nint extra_global;', '\nvoid extra(void) {}',
                           '\nextern double floor(double) __asm__("other");', '\n_Pragma("weak salty_assert")']:
                with self.assertRaises((Unsupported, subprocess.CalledProcessError)):
                    extract(self.sources[u, 'source'] + suffix, 'source', self.path, u)
        self.changed(True, 'target', '#define XNN_UNPREDICTABLE(x) (x)', '#define XNN_UNPREDICTABLE(x) 0', reject=True)
        for prefix in ['%:define assert(x) (void)0\n', '??=define assert(x) (void)0\n', '#\\\ndefine assert(x) (void)0\n']:
            with self.assertRaises(Unsupported): extract(prefix + self.sources[False, 'source'], 'source', self.path)

    def test_comments(self):
        for (u, side), source in self.sources.items():
            self.assertEqual(extract('/* comment */\n' + source, side, self.path, u), self.models[u, side])

if __name__ == '__main__': unittest.main()
