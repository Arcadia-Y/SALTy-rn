#!/usr/bin/env python3
"""Focused regression tests for the definition/proof dependency boundary."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_layout


class LayoutTests(unittest.TestCase):
    def check_tree(self, files):
        with tempfile.TemporaryDirectory(prefix='salty-layout-') as folder:
            root = Path(folder)
            for module, source in files.items():
                path = root.joinpath(*module.split('.')).with_suffix('.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            with patch.object(check_layout, 'ROOT', root), patch.object(check_layout, 'SALTY', root / 'Salty'):
                with contextlib.redirect_stderr(io.StringIO()), contextlib.redirect_stdout(io.StringIO()):
                    return check_layout.main()

    def test_definition_graph_and_comments(self):
        self.assertEqual(self.check_tree({
            'Salty.Model.Memory': 'import Std\n/- theorem fake /- nested -/ sorry -/\ndef label := "axiom"\n',
            'Salty.Spec.Example': 'import Salty.Model.Memory\n-- import Salty.Proofs.Hidden\ndef Domain := True\n',
        }), 0)

    def test_proof_dependency_is_rejected(self):
        self.assertEqual(self.check_tree({
            'Salty.Model.Memory': 'import Salty.Proofs.Core.Memory\n',
            'Salty.Proofs.Core.Memory': 'import Std\n',
            'Salty.Spec.Example': 'import Salty.Model.Memory\n',
        }), 1)

    def test_model_cannot_depend_on_kernel_specification(self):
        self.assertEqual(self.check_tree({
            'Salty.Model.Machine': 'import Salty.Model.Operations\n',
            'Salty.Model.Operations': 'import Salty.Spec.Lane\n',
            'Salty.Spec.Lane': 'import Std\ndef lane := 0\n',
        }), 1)

    def test_proof_command_is_rejected(self):
        self.assertEqual(self.check_tree({'Salty.Spec.Example': 'import Std\ntheorem hidden : True := by trivial\n'}), 1)

    def test_placeholder_and_missing_import_are_rejected(self):
        self.assertEqual(self.check_tree({'Salty.Proofs.Example': 'import Salty.Model.Missing\ntheorem hidden : True := by sorry\n'}), 1)

    def test_generated_programs_cannot_import_proofs(self):
        self.assertEqual(self.check_tree({
            'Salty.Proofs.Core.Memory': 'import Std\n',
            'Salty.Generated.Example': 'import Salty.Proofs.Core.Memory\n',
        }), 1)


if __name__ == '__main__':
    unittest.main()
