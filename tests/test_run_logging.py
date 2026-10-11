"""Studio lifecycle events, parallel batch status, and numbered tableaux."""
import json
from dataclasses import replace
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from bae_bertini.config import Configuration
from bae_bertini.jobs import LogEntry, RunManager, Snapshot, TableauState, failure_hint
from streamlit.testing.v1 import AppTest

TABLEAUX = ['{{1,3,6,7},{2,5},{4}}', '{{1,3,4,7},{2,5},{6}}',
            '{{1,2,3,4},{5,6},{7}}', '{{1,2,3,5},{4,7},{6}}', '{{1,3,4,5},{2,7},{6}}']


def wait_until(predicate, seconds=10):
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline:
        if predicate():
            return
        time.sleep(.02)
    raise AssertionError('Timed out waiting for the calculation state.')


class LoggingTests(unittest.TestCase):
    def test_actionable_and_unknown_diagnostics(self):
        for text, expected in [('declare: -A: invalid option', 'brew install bash'),
                               ('Wolfram executable not found', 'WOLFRAM_KERNEL'),
                               ('Backend timed out', 'Backend timeout'),
                               ('tracking failed', 'precision')]:
            self.assertIn(expected, failure_hint(text))
        self.assertEqual(failure_hint('unrecognized diagnostic 123'), 'unrecognized diagnostic 123')

    def test_raw_stderr_is_neutral_and_start_failure_is_saved(self):
        with tempfile.TemporaryDirectory() as folder:
            manager = RunManager()
            manager.start([sys.executable, '-c',
                'import sys; print("ordinary stderr", file=sys.stderr); print("stdout text")'], {}, Path(folder))
            wait_until(lambda: not manager.snapshot().running)
            state = manager.snapshot()
            backend = [entry for entry in state.entries if entry.source == 'backend']
            self.assertTrue(backend)
            self.assertTrue(all(entry.level == 'RAW' for entry in backend))
            self.assertTrue(any(entry.level == 'INFO' for entry in state.entries))
            saved = state.log_path.read_text()
            self.assertIn('ordinary stderr\n', saved)
            manager.start(['/does/not/exist/studio-worker'], {}, Path(folder))
            wait_until(lambda: not manager.snapshot().running)
            state = manager.snapshot()
            self.assertTrue(any(entry.level == 'ERROR' for entry in state.entries))
            self.assertIn('Could not run calculation', state.log_path.read_text())

    def test_concurrent_journal_appends_are_complete(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / 'events.jsonl'
            env = dict(os.environ, BAE_STUDIO_EVENTS_FILE=str(path), PYTHONPATH=str(ROOT / 'src'))
            command = [sys.executable, '-c',
                'from bae_bertini.run_events import emit; import sys; '
                '[emit(dict(writer=sys.argv[1], n=n, message="x"*10000)) for n in range(20)]']
            workers = [subprocess.Popen(command + [str(index)], env=env) for index in range(4)]
            for worker in workers:
                self.assertEqual(worker.wait(timeout=10), 0)
            records = [json.loads(line) for line in path.read_text().splitlines()]
            self.assertEqual(len(records), 80)
            self.assertEqual(len({(r['writer'], r['n']) for r in records}), 80)

    def test_partial_and_malformed_events_do_not_break_collection(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            script = folder / 'submit_run_single_jobs.sh'
            script.write_text('''import os, time
from bae_bertini.run_events import emit
emit(dict(kind='total', total=1))
emit(dict(kind='queued', entry_id=1, tableau='{{1}}', status='queued'))
with open(os.environ['BAE_STUDIO_EVENTS_FILE'], 'a') as stream:
    stream.write('broken json\\n{"kind":')
    stream.flush()
    time.sleep(.2)
    stream.write('"bogus"}\\n')
emit(dict(kind='started', entry_id=1, tableau='{{1}}', status='running'))
emit(dict(kind='finished', entry_id=1, tableau='{{1}}', status='failed', exit_code='bad'))
emit(dict(kind='finished', entry_id=1, tableau='{{1}}', status='succeeded', exit_code=0))
''')
            manager = RunManager()
            manager.start([sys.executable, str(script)], {'PYTHONPATH': str(ROOT / 'src')}, folder)
            wait_until(lambda: not manager.snapshot().running)
            state = manager.snapshot()
            self.assertEqual(state.counts['succeeded'], 1)
            warnings = [entry for entry in state.entries if entry.level == 'WARNING']
            self.assertEqual(len(warnings), 3)
            self.assertIn('broken json', state.log_path.read_text())
            before = tuple(state.entries)
            manager.snapshot()
            self.assertEqual(manager.snapshot().entries, before)


class BatchStatusTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='studio batch ')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for directory in ('scripts', 'src', 'wolfram'):
            shutil.copytree(ROOT / directory, self.root / directory)
        (self.root / '.venv').symlink_to(ROOT / '.venv', target_is_directory=True)
        self.kernel = self.root / 'fake-kernel'
        self.kernel.write_text(f'#!{sys.executable}\n' + '''import os, sys, time
from pathlib import Path
from bae_bertini.results import write_table, FIELDS
tableau = ''.join(sys.argv[-1].split())
code = 1 if tableau == os.environ.get('FAKE_FAIL_TABLEAU') else 0
delay = float(os.environ.get('FAKE_DELAY', '.15'))
print('ordinary stdout: ' + tableau, flush=True)
time.sleep(.01 if code else delay)
print('tracking failed' if code else 'ordinary stderr', file=sys.stderr, flush=True)
path = Path(os.environ['BERTINI_RESULT_SYT_DIR']) / (tableau + '.csv')
row = dict(RunID=tableau, Tableau=tableau, YoungDiagram='{4,2,1}', SucceededQ='false' if code else 'true',
           FailureReason='TrackingFailed' if code else 'None', TimingSeconds=delay, BetheRoots='{{1}}')
write_table(path, FIELDS, [row])
raise SystemExit(code)
''')
        self.kernel.chmod(0o755)
        self.listing = self.root / 'input tableaux.txt'
        self.env = dict(BAE_BERTINI_ROOT=str(self.root), WOLFRAM_KERNEL=str(self.kernel),
                        BERTINI_RESULT_SYT_DIR=str(self.root / 'results'),
                        PYTHONPATH=str(self.root / 'src'))
        self.manager = RunManager()
        self.addCleanup(self.manager.close)

    def start(self, tableaux, *options, **env):
        self.listing.write_text('# input\n\n' + '\n'.join(tableaux) + '\n')
        args = ['bash', str(self.root / 'scripts/submit_run_single_jobs.sh'),
                '--list', str(self.listing), '-j', '2', *options]
        self.manager.start(args, dict(self.env, **env), self.root / 'logs')

    def finish(self):
        wait_until(lambda: not self.manager.snapshot().running, 15)
        return self.manager.snapshot()

    def test_parallel_failure_duplicate_and_resume(self):
        self.start([TABLEAUX[0], TABLEAUX[1], TABLEAUX[0]], FAKE_FAIL_TABLEAU=TABLEAUX[1])
        state = self.finish()
        self.assertEqual(state.code, 1, state.output)
        self.assertEqual(state.total, 3)
        self.assertEqual([r.entry_id for r in state.tableaux], [1, 2, 3])
        self.assertEqual([r.status for r in state.tableaux], ['succeeded', 'failed', 'skipped'])
        self.assertEqual(state.counts['pending'], 0)
        self.assertEqual(state.counts['failed'], 1)
        self.assertEqual(state.tableaux[2].reason, 'Duplicate input entry')
        self.assertIn('tracking failed', state.tableaux[1].reason)
        self.assertIn('ordinary stderr', Path(state.tableaux[0].stderr_path).read_text())
        finish_order = [json.loads(line)['entry_id'] for line in self.manager.job.event_path.read_text().splitlines()
                        if json.loads(line)['kind'] == 'finished']
        self.assertEqual(finish_order, [2, 1])
        self.assertIn('Failed jobs: 1', state.output)
        self.start(TABLEAUX[:2])
        state = self.finish()
        self.assertEqual(state.code, 0, state.output)
        self.assertEqual(state.counts['skipped'], 2)
        self.assertEqual([r.reason for r in state.tableaux], ['Previously solved', 'Previously failed'])

    def test_worker_output_is_live_and_saved_with_duration(self):
        self.start(TABLEAUX[:1], FAKE_DELAY='1.5')
        wait_until(lambda: any('ordinary stdout:' in entry.message
                              for entry in self.manager.snapshot().entries))
        self.assertTrue(self.manager.snapshot().running)
        state = self.finish()
        worker = [entry for entry in state.entries if entry.source.startswith('entry 1 ')]
        self.assertTrue(any(entry.source == 'entry 1 stdout' for entry in worker))
        self.assertTrue(any(entry.source == 'entry 1 stderr' for entry in worker))
        self.assertTrue(all(entry.level == 'RAW' for entry in worker))
        saved = state.log_path.read_text()
        self.assertIn('ordinary stdout:', saved)
        self.assertIn('ordinary stderr', saved)
        self.assertRegex(saved, r'Entry 1 succeeded \(\d+\.\d{3} s\)')

    def test_partition_keeps_original_input_positions(self):
        self.start(TABLEAUX, '--part', '2', '--parts', '3')
        state = self.finish()
        self.assertEqual(state.code, 0, state.output)
        self.assertEqual(state.total, 2)
        self.assertEqual([r.entry_id for r in state.tableaux], [3, 4])
        self.assertEqual(state.counts['succeeded'], 2)

    def test_stop_marks_active_and_remaining_entries(self):
        self.start(TABLEAUX, FAKE_DELAY='30')
        wait_until(lambda: self.manager.snapshot().counts['running'] == 2)
        # A new browser reads the same server-owned state; no UI drains these events.
        self.assertEqual(len(self.manager.snapshot().tableaux), 5)
        self.manager.stop()
        state = self.finish()
        self.assertTrue(state.cancelled)
        self.assertEqual(state.counts['cancelled'], 2)
        self.assertEqual(state.counts['not_run'], 3)
        self.assertEqual(state.counts['running'], 0)
        self.assertEqual(state.counts['pending'], 0)

    def test_cli_without_events_and_dry_run(self):
        self.start(TABLEAUX[:2], '--dry-run')
        state = self.finish()
        self.assertEqual(state.code, 0, state.output)
        self.assertIsNone(state.total)
        self.assertFalse(self.manager.job.event_path.exists())
        env = dict(os.environ, **self.env)
        env.pop('BAE_STUDIO_EVENTS_FILE', None)
        result = subprocess.run(['bash', str(self.root / 'scripts/submit_run_single_jobs.sh'),
            '--list', str(self.listing), '--no-logs'], env=env, capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Submitted: 2', result.stdout)

    def test_merge_failure_does_not_change_worker_status(self):
        stage = self.root / 'workspace/runs/batch-results/{4,2,1}'
        stage.mkdir(parents=True)
        (stage / 'broken.csv').write_text('Incomplete,header\n1,2\n')
        self.start(TABLEAUX[:1])
        state = self.finish()
        self.assertEqual(state.code, 1)
        self.assertEqual(state.counts['succeeded'], 1)
        self.assertEqual(state.counts['failed'], 0)
        self.assertTrue(state.issues)
        self.assertIn('merge failed', state.issues[0])


class LiveUITests(unittest.TestCase):
    def test_terminal_and_full_log_download(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            log = folder / 'ui-test.log'
            log.write_text('full untouched backend log\n')
            entries = (LogEntry('2026-10-06T10:00:00+02:00', 'INFO', 'studio', 'run started'),
                       LogEntry('2026-10-06T10:00:01+02:00', 'RAW', 'backend',
                                'Initial calculation:\n+---+---+\n| 1 | 3 |\n+---+---+\n'
                                '| 2 |\n+---+\nSubtableau complete: 1.250 s'),
                       LogEntry('2026-10-06T10:00:02+02:00', 'ERROR', 'studio', 'boom failure'))
            state = Snapshot(True, False, None, 1, '', log, str(folder), entries=entries)
            with patch('bae_bertini.jobs.RunManager.snapshot', return_value=state) as snapshot, \
                 patch('bae_bertini.config.load_config', return_value=Configuration(output=str(folder))):
                app = AppTest.from_file(str(ROOT / 'streamlit_app.py')).run(timeout=20)
                self.assertFalse(app.exception)
                self.assertFalse(app.get('html'))
                self.assertFalse(app.get('progress'))
                self.assertFalse(any(widget.label in ('Log severity', 'Inspect tableau') for widget in app.selectbox))
                terminal = next(code.value for code in app.code if 'Initial calculation:' in code.value)
                self.assertIn('| 1 | 3 |', terminal)
                self.assertIn('Subtableau complete: 1.250 s', terminal)
                self.assertIn('boom failure', terminal)
                snapshot.return_value = replace(state, running=False, code=0)
                app.run()
                app.checkbox(key='prepare_log_' + str(log)).check().run()
                self.assertEqual(len(app.get('download_button')), 1)
                self.assertEqual(log.read_text(), 'full untouched backend log\n')
                self.assertFalse(app.exception)

    def test_single_tableau_is_shown_and_finishes(self):
        with tempfile.TemporaryDirectory() as folder:
            manager = RunManager()
            manager.start([sys.executable, '-c', 'print("single run")', TABLEAUX[0]], {}, Path(folder))
            wait_until(lambda: not manager.snapshot().running)
            state = manager.snapshot()
            self.assertEqual(state.total, 1)
            self.assertEqual(state.tableaux[0].tableau, TABLEAUX[0])
            self.assertEqual(state.tableaux[0].status, 'succeeded')
            self.assertEqual(state.counts['succeeded'], 1)


if __name__ == '__main__':
    unittest.main()
