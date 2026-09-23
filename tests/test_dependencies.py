"""Reject Bertini installations that import but cannot run our driver."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from bae_bertini.config import check_dependencies
from bae_bertini.paths import PYTHON


class DependencyTests(unittest.TestCase):
    def test_importable_package_without_continuation_api_is_rejected(self):
        with tempfile.TemporaryDirectory(prefix='incompatible bertini ') as folder:
            package = Path(folder) / 'bertini'
            package.mkdir()
            (package / '__init__.py').write_text('')
            with patch.dict(os.environ, {'PYTHONPATH': folder}):
                imported = subprocess.run(
                    [str(PYTHON), '-c', 'import bertini'],
                    capture_output=True, text=True, timeout=20)
                self.assertEqual(imported.returncode, 0, imported.stderr)
                issues = check_dependencies(require_wolfram=False)
        self.assertEqual(len(issues), 1)
        self.assertIn("No module named 'bertini.function_tree'", issues[0])
        self.assertIn('bertini2==2.0.2', issues[0])


if __name__ == '__main__':
    unittest.main()
