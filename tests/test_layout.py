"""Verify maintained commands and independently extracted source bundles."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'src'))

spec = importlib.util.spec_from_file_location('build_distribution', ROOT / 'scripts/build_distribution.py')
distribution = importlib.util.module_from_spec(spec)
spec.loader.exec_module(distribution)


class LayoutTests(unittest.TestCase):
    def test_old_bash_selects_homebrew_and_preserves_arguments(self):
        old_bash = os.environ.get('BATCH_TEST_OLD_BASH', '/bin/bash')
        version = subprocess.check_output([old_bash, '-c', 'echo "$BASH_VERSION"'], text=True)
        if tuple(map(int, version.split('.')[:2])) >= (4, 3):
            self.skipTest('Set BATCH_TEST_OLD_BASH to Bash 3.2 to exercise the macOS fallback.')
        modern_bash = shutil.which('bash')
        probe = subprocess.run([modern_bash, '-c',
            '((BASH_VERSINFO[0] > 4 || (BASH_VERSINFO[0] == 4 && BASH_VERSINFO[1] >= 3)))'])
        if probe.returncode:
            self.skipTest('A modern Bash on PATH is needed to test re-execution.')
        with tempfile.TemporaryDirectory(prefix='batch shell ') as temporary:
            folder = Path(temporary)
            script = folder / 'submit_run_single_jobs.sh'
            shutil.copy(ROOT / 'scripts/paths.sh', folder)
            apple_bash = folder / 'opt/homebrew/bin/bash'
            intel_bash = folder / 'usr/local/bin/bash'
            source = (ROOT / 'scripts/submit_run_single_jobs.sh').read_text()
            script.write_text(source.replace('/opt/homebrew/bin/bash', str(apple_bash))
                                    .replace('/usr/local/bin/bash', str(intel_bash)))
            old_bin = folder / 'bin'
            old_bin.mkdir()
            (old_bin / 'bash').symlink_to(old_bash)
            env = dict(os.environ, PATH=str(old_bin) + ':/usr/bin:/bin')
            for candidate in (apple_bash, intel_bash):
                candidate.parent.mkdir(parents=True)
                candidate.symlink_to(modern_bash)
                result = subprocess.run([old_bash, str(script), '--help'], env=env,
                                        capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn('Usage:', result.stdout)
                candidate.unlink()
            result = subprocess.run([old_bash, str(script), '--help'], env=env,
                                    capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 1)
            self.assertIn('brew install bash', result.stderr)
            self.assertNotIn('declare:', result.stderr)

    def test_bundle_is_relocatable_and_excludes_local_state(self):
        with tempfile.TemporaryDirectory(prefix='bertini bundle ') as temporary:
            folder = Path(temporary)
            output = folder / 'bundle.zip'
            distribution.build_distribution(output)
            with zipfile.ZipFile(output) as archive:
                names = archive.namelist()
                self.assertFalse(any('/workspace/' in n or '/.venv/' in n or '__pycache__' in n for n in names))
                self.assertFalse(any('all_SYT_{5,4,3,2,1}.csv' in n for n in names))
                manifest = json.loads(archive.read('BAE_Bertini/PACKAGE_MANIFEST.json'))
                self.assertEqual(set(manifest['sha256']),
                                 {n.removeprefix('BAE_Bertini/') for n in names
                                  if not n.endswith('/PACKAGE_MANIFEST.json')})
                for name, digest in manifest['sha256'].items():
                    self.assertEqual(hashlib.sha256(archive.read('BAE_Bertini/' + name)).hexdigest(), digest)
                archive.extractall(folder)
            project = folder / 'BAE_Bertini'
            env = dict(os.environ, PYTHONPATH=str(project / 'src'))
            env.pop('BAE_BERTINI_ROOT', None)
            check = subprocess.run([sys.executable, '-c',
                'from bae_bertini.paths import ROOT, REFERENCES; '
                'from bae_bertini.results import read_results; '
                'from bae_bertini.config import Configuration; '
                'print(ROOT); '
                'assert read_results(REFERENCES / "all_SYT_{3,2,1}.csv")[0]; '
                'assert "wolfram/RunSingle.wl" in Configuration().command()[0][-2]'],
                cwd=folder, env=env, capture_output=True, text=True, timeout=15)
            self.assertEqual(check.returncode, 0, check.stderr)
            self.assertEqual(check.stdout.strip(), str(project))
            for command in (
                [sys.executable, str(project / 'scripts/continue_lambda0_to_zero.py'), '--help'],
                [sys.executable, '-m', 'bae_bertini.roots', '--help'],
                ['bash', str(project / 'scripts/submit_run_single_jobs.sh'), '--help'],
                ['bash', str(project / 'scripts/crosscheck.sh'), '--help'],
            ):
                with self.subTest(command=command):
                    result = subprocess.run(command, cwd=folder, env=env, capture_output=True, text=True, timeout=15)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
