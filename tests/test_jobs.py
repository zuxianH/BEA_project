"""Configuration and background job integration checks."""
import json
import os
from pathlib import Path
import signal
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from bae_bertini.config import BATCH, MODES, Configuration, load_config, parse_shape
from bae_bertini.paths import ROOT, RESULTS, REFERENCES, local_path
from bae_bertini.jobs import Job
from bae_bertini.results import read_results


class InputTests(unittest.TestCase):
    def test_saved_paths_migrate_without_changing_numerical_settings(self):
        with tempfile.TemporaryDirectory() as directory:
            state = Path(directory)
            settings = dict(BATCH, DEFAULT_PRECISION='200')
            (state / 'settings.json').write_text(json.dumps({
                'mode': MODES[4], 'input': str(ROOT / 'Result_SYT/all_SYT_{3,2,1}.csv'),
                'output': str(ROOT / 'Result_SYT_desktop'), 'settings': settings,
            }))
            with patch('bae_bertini.config.STATE', state):
                config = load_config()
            self.assertEqual(config.output, str(RESULTS / 'desktop'))
            self.assertEqual(config.settings, settings)
            args, env = config.command()
            self.assertIn('bae_bertini.flip_checks', args)
            self.assertIn(str(REFERENCES / 'all_SYT_{3,2,1}.csv'), args)
            self.assertEqual(env['BERTINI_RESULT_SYT_DIR'], str(RESULTS / 'desktop'))
            external = state / 'Result_SYT_desktop'
            self.assertEqual(local_path(external), external)

    def test_tableau_validation(self):
        self.assertEqual(parse_shape('[[1, 3], [2]]', True), '{{1,3},{2}}')
        for value in ['{{1,2},{2}}', '{{1,2},{4}}', '{{2,3},{1}}', '{{1},{2,3}}',
                      '{{1,3,2}}', '{{1}, {}}', '{{1}};Run["bad"]']:
            with self.subTest(value=value), self.assertRaises(ValueError):
                parse_shape(value, True)

    def test_single_script_settings_and_destination(self):
        config = Configuration()
        args, env = config.command()
        self.assertEqual(args[-1], '{{1,3},{2}}')
        self.assertEqual(env['BERTINI_MAX_STEP_SIZE'], '1/200')
        self.assertEqual(env['BERTINI_RESULT_SYT_DIR'], env['CROSSCHECK_RESULT_SYT_DIR'])

    def test_reverse_continuation_command(self):
        args, env = Configuration(mode=MODES[5], input='[[1,3],[2]]', tolerance='1e-8').command()
        self.assertEqual(args[1:], ['-m', 'bae_bertini.reverse_check', '--tolerance', '1e-8', '{{1,3},{2}}'])
        self.assertEqual(env['BERTINI_INITIAL_LAMBDA'], BATCH['INITIAL_LAMBDA'])

    def test_reverse_continuation_returns_to_start(self):
        from bae_bertini.reverse_check import reverse_check
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'initial_data.csv'
            source.write_text('syt,lambda0,var,Initialvar,expression\n"{{1}}",4,x,2,x**2 - h\n')
            lines, passed = reverse_check(source, '1', '1e-6')
        self.assertTrue(passed)
        self.assertIn('Path=lambda 4 -> 1 -> 4', lines)

    def test_batch_partitions_and_rerun(self):
        args, _ = Configuration(mode=MODES[1], input='{3,2,1}', jobs='2', partition='3', parts='9', rerun=True).command()
        self.assertIn('--rerun-existing', args)
        self.assertEqual(args[args.index('--part') + 1], '3')
        with self.assertRaises(ValueError):
            Configuration(mode=MODES[1], input='{3,2,1}', partition='10', parts='9').command()

    def test_bad_numerical_settings_rejected(self):
        for key, value in [('TRACKING_TOLERANCE', 'nan'), ('MAX_STEP_SIZE', '0'),
                           ('INITIAL_LAMBDA', '1; Quit[]'), ('MAX_NUM_STEPS', '1.5'),
                           ('MAX_PRECISION', '20'), ('PREDICTOR', 'MadeUp')]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                Configuration(settings=dict(BATCH, **{key: value})).command()

    def test_list_files_are_validated(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'tableaux with spaces.txt'
            source.write_text('{{1,3},{2}}\n{{1,2},{3}}\n')
            args, _ = Configuration(mode=MODES[2], input=str(source)).command()
            self.assertEqual(args[args.index('--list') + 1], str(source))
            source.write_text('{{1,3},{2}}\n{{1,2},{4}}\n')
            with self.assertRaisesRegex(ValueError, 'line 2'):
                Configuration(mode=MODES[2], input=str(source)).command()

    def test_read_preview_is_bounded(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'results.csv'
            source.write_text('Tableau,SucceededQ\na,true\nb,false\nc,true\n')
            rows, truncated = read_results(source, 2)
            self.assertEqual(len(rows), 2)
            self.assertTrue(truncated)


class ProcessTests(unittest.TestCase):
    def test_output_exit_status_and_log(self):
        with tempfile.TemporaryDirectory() as directory:
            job = Job([sys.executable, '-c', 'print("calculation output"); raise SystemExit(7)'], {}, Path(directory))
            job.start()
            self.assertTrue(job.done.wait(5))
            events = list(job.events.queue)
            self.assertIn(('done', 7), events)
            self.assertIn('calculation output', job.log_path.read_text())

    def test_cancellation_terminates_descendants(self):
        with tempfile.TemporaryDirectory() as directory:
            pidfile = Path(directory) / 'child.pid'
            # The descendant ignores TERM; stopping must also kill it after the parent exits.
            script = ('import subprocess,sys,time; '
                      'p=subprocess.Popen([sys.executable,"-c",'
                      '"import signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); time.sleep(60)"]); '
                      f'open({str(pidfile)!r},"w").write(str(p.pid)); time.sleep(60)')
            job = Job([sys.executable, '-c', script], {}, Path(directory))
            job.start()
            deadline = time.monotonic() + 5
            while not pidfile.exists() and time.monotonic() < deadline:
                time.sleep(.02)
            self.assertTrue(pidfile.exists())
            child = int(pidfile.read_text())
            try:
                job.cancel()
                self.assertTrue(job.done.wait(8))
                stat = Path(f'/proc/{child}/stat')
                self.assertTrue(not stat.exists() or stat.read_text().split()[2] == 'Z')
            finally:
                try:
                    os.kill(child, signal.SIGKILL)
                except ProcessLookupError:
                    pass

    def test_cancel_before_start_does_not_launch(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / 'started'
            job = Job([sys.executable, '-c', f'open({str(marker)!r},"w").close()'], {}, Path(directory))
            job.cancel()
            job.start()
            self.assertTrue(job.done.wait(5))
            self.assertFalse(marker.exists())


if __name__ == '__main__':
    unittest.main()
