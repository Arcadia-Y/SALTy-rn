"""Cross-profile isolation and shared lowering regressions."""
from pathlib import Path
import tempfile
import subprocess
import unittest
from unittest.mock import patch
from extract import ROOT, profile_for, extract_family, Unsupported
from frontend import Extractor


class SharedFrontendTests(unittest.TestCase):
    def test_configuration_is_not_shared_mutable_state(self):
        first = profile_for('qs8')
        first['calls']['vld1_s8']['primitive'] = 'wrong'
        first['features'].append('scalar_store')
        second = profile_for('qs8')
        self.assertEqual(second['calls']['vld1_s8']['primitive'], 'load8')
        self.assertNotIn('scalar_store', second['features'])
        self.assertNotIn('floor', second['calls'])
        self.assertIn('floor', profile_for('rdsum')['calls'])

    def test_capabilities_do_not_leak_between_families(self):
        loop = {'kind': 'DoStmt', 'inner': []}
        with self.assertRaisesRegex(Unsupported, 'statement not admitted'):
            Extractor(profile_for('qs8'), set()).stmt(loop)
        with self.assertRaisesRegex(Unsupported, 'do while arity'):
            Extractor(profile_for('pack'), set()).stmt(loop)
        vector = {'kind': 'DeclStmt', 'inner': [
            {'kind': 'VarDecl', 'id': 'v', 'name': 'v', 'type': {'qualType': 'int16x8_t'}}]}
        with self.assertRaisesRegex(Unsupported, 'uninitialized declaration'):
            Extractor(profile_for('qs8'), set()).stmt(vector)
        self.assertEqual(Extractor(profile_for('rdsum'), set()).stmt(vector), '.skip')

    def test_signedness_and_parameter_layouts_are_explicit(self):
        signed, unsigned = profile_for('add'), profile_for('uadd')
        self.assertEqual(signed['fields']['output_min'], ['int8_t', 'param8', '22'])
        self.assertEqual(unsigned['fields']['output_min'], ['uint8_t', 'paramU8', '22'])
        self.assertEqual(profile_for('rdsum', True)['word'], 'uint32_t')
        with self.assertRaises(Unsupported):
            profile_for('qs8', True)

    def test_extra_variants_fail_closed(self):
        data = {'qs8': {'variants': [{}, {}, {}]}}
        with patch('extract.json.loads', side_effect=[data, {}, {}]):
            with self.assertRaisesRegex(Unsupported, 'one variant or a signed/unsigned pair'):
                profile_for('qs8')

    def test_packing_rejects_unsequenced_local_pointer_use(self):
        source = (ROOT / 'kernels/source/x32-packw-gemm-goi.c').read_text()
        self.assertIn('*packed_weights = *bias++;', source)
        source = source.replace('*packed_weights = *bias++;', '*packed_weights = *packed_weights++;', 1)
        with tempfile.TemporaryDirectory(prefix='salty-front-') as tmp:
            with self.assertRaises((Unsupported, subprocess.CalledProcessError)):
                extract_family('pack', source, 'source', Path(tmp), real=False)

    def test_postincrement_requires_its_own_capability(self):
        profile = profile_for('pack')
        profile['features'].remove('scalar_postincrement')
        source = (ROOT / 'kernels/source/x32-packw-gemm-goi.c').read_text()
        with tempfile.TemporaryDirectory(prefix='salty-front-') as tmp:
            with patch('extract.profile_for', return_value=profile):
                with self.assertRaisesRegex(Unsupported, 'load-postincrement unsupported'):
                    extract_family('pack', source, 'source', Path(tmp), real=False)

    def test_distinct_extractions_do_not_reuse_local_state(self):
        source = (ROOT / 'kernels/target/qs8-vcvt.c').read_text()
        with tempfile.TemporaryDirectory(prefix='salty-front-') as tmp:
            one = extract_family('qs8', source, 'target', Path(tmp), real=False)
            other = (ROOT / 'kernels/target/qu8-rdsum.c').read_text()
            extract_family('rdsum', other, 'target', Path(tmp), unsigned=True, real=False)
            self.assertEqual(one, extract_family('qs8', source, 'target', Path(tmp), real=False))


if __name__ == '__main__':
    unittest.main()
