#!/usr/bin/env python3
"""Mutation checks of the reduction bridge; not kernel-equivalence evidence."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from extract_rsum import ROOT, Unsupported, extract

class ReductionExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix='salty-rsum-mutations-')
        cls.path = Path(cls.tmp.name)
        cls.sources = {(unsigned, side): (ROOT / f'kernels/{side}/{"qu8" if unsigned else "qs8"}-rsum.c').read_text()
                       for unsigned in (False, True) for side in ('source', 'target')}
        cls.models = {key: extract(source, key[1], cls.path, key[0]) for key, source in cls.sources.items()}

    @classmethod
    def tearDownClass(cls): cls.tmp.cleanup()

    def changed(self, unsigned, side, old, new, reject=False):
        source = self.sources[unsigned, side]
        self.assertIn(old, source)
        try:
            model = extract(source.replace(old, new, 1), side, self.path, unsigned)
        except (Unsupported, subprocess.CalledProcessError):
            return
        self.assertFalse(reject, 'unsupported mutation accepted')
        self.assertNotEqual(model, self.models[unsigned, side], 'semantic change disappeared')

    def test_loop_control(self):
        for unsigned in (False, True):
            for old, new in [('batch >= 2048', 'batch > 2048'), ('batch -= 2048', 'batch -= 1024'),
                             ('current_batch = 2048', 'current_batch = 1024'),
                             ('current_batch -= 16', 'current_batch -= 8'), ('batch >= 16', 'batch > 16'),
                             ('input += 16', 'input += 8'), ('batch < 2048', 'batch < 2047')]:
                with self.subTest(unsigned=unsigned, old=old): self.changed(unsigned, 'source', old, new)
            self.changed(unsigned, 'target', 'batch > 0', 'batch >= 0')
            self.changed(unsigned, 'target', 'batch -= vl', 'batch += vl')

    def test_dataflow(self):
        for unsigned in (False, True):
            c = 'u' if unsigned else 's'
            r = 'u' if unsigned else 'i'
            for old, new in [(f'vmovq_n_{c}32(0)', f'vmovq_n_{c}32(1)'),
                             (f'vmulq_{c}8(vt, vonemask)', f'vmulq_{c}8(vt, vt)'),
                             ('16 - batch', '15 - batch'), ('*output += vacc;', '*output += vacc; *output += vacc;')]:
                with self.subTest(unsigned=unsigned, old=old): self.changed(unsigned, 'source', old, new)
            self.changed(unsigned, 'target', f'__riscv_vmv_v_x_{r}32m8(0, vlmax)', f'__riscv_vmv_v_x_{r}32m8(1, vlmax)')
            self.changed(unsigned, 'target', '(vacc, vacc, vt32, vl)', '(vacc, vt32, vt32, vl)')
            seed = 'red' if unsigned else 'vres'
            self.changed(unsigned, 'target', f'(vacc, {seed}, vlmax)', f'(vacc, {seed}, 1)')
            self.changed(unsigned, 'target', f'__riscv_vmv_v_x_{r}32m1(0,', f'__riscv_vmv_v_x_{r}32m1(1,')

    def test_immutable_table(self):
        for unsigned in (False, True):
            for old, new in [('1, 1, 1, 1', '2, 1, 1, 1'), ('static const', 'static'),
                             ('[32]', '[33]'), ('XNN_ALIGN(16)', 'XNN_ALIGN(8)'),
                             ('static const', 'const'), ('input += 16;', 'input = onemask_table;')]:
                with self.subTest(unsigned=unsigned, old=old): self.changed(unsigned, 'source', old, new, reject=True)

    def test_fixed_architecture_branch(self):
        for unsigned in (False, True):
            for old, new in [('#if XNN_ARCH_ARM64', '#if 0'), ('#else', '#elif 1'),
                             ('#endif', '#endif\n#define assert(x) (void)0')]:
                self.changed(unsigned, 'source', old, new, reject=True)
            # AArch32 code is intentionally outside this extraction's scope.
            source = self.sources[unsigned, 'source']
            alternate = source.replace('vacc_lo, vacc_lo', 'vacc_lo, unsupported_a32_name')
            self.assertEqual(extract(alternate, 'source', self.path, unsigned), self.models[unsigned, 'source'])

    def test_unsupported_syntax(self):
        for unsigned in (False, True):
            for old, new in [('input += 16;', 'input++;'), ('input += 16;', 'return;'),
                             ('input += 16;', '__builtin_trap();'), ('*output += vacc;', '*output -= vacc;'),
                             ('*output += vacc;', '*output = vacc;'), ('*output += vacc;', 'output[1] += vacc;')]:
                self.changed(unsigned, 'source', old, new, reject=True)
            self.changed(unsigned, 'target', '_tu(vacc, vacc, vt32, vl)', '(vacc, vt32, vl)', reject=True)

    def test_translation_unit_injection(self):
        for unsigned in (False, True):
            for suffix in ['\nvoid salty_assert(int c) {}', '\nint extra_global;', '\nvoid extra(void) {}',
                           '\n_Pragma("weak salty_assert")', '\nextern void salty_assert(int) __asm__("other");']:
                with self.subTest(unsigned=unsigned, suffix=suffix):
                    with self.assertRaises((Unsupported, subprocess.CalledProcessError)):
                        extract(self.sources[unsigned, 'source'] + suffix, 'source', self.path, unsigned)

    def test_directive_spellings(self):
        for prefix in ['%:define assert(x) (void)0\n', '??=define assert(x) (void)0\n',
                       '#\\\ndefine assert(x) (void)0\n', '_Prag' + '\\\n' + 'ma("weak salty_assert")\n']:
            with self.assertRaises(Unsupported):
                extract(prefix + self.sources[False, 'source'], 'source', self.path)

    def test_comment_fidelity(self):
        for (unsigned, side), source in self.sources.items():
            self.assertEqual(extract('/* comment */\n' + source, side, self.path, unsigned), self.models[unsigned, side])

if __name__ == '__main__': unittest.main()
