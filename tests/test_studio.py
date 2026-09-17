"""Browser interactions and server-owned job lifecycle, without a solver run."""
import csv
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from bae_bertini.config import Configuration, MODES
from bae_bertini.paths import ROOT
from bae_bertini.jobs import RunManager
from bae_bertini.ui.plots import root_figure
from streamlit.testing.v1 import AppTest


class PlotTests(unittest.TestCase):
    def test_complex_levels_and_flip_overlay(self):
        figure, omitted = root_figure('{{1.25`40 + 2*I, -3*^-2},{4}}', '{{-1.25-2*I},{-4}}', True)
        self.assertEqual(omitted, 0)
        self.assertEqual(len(figure.data), 4)
        self.assertEqual(list(figure.data[0].x), [-1.25, .03])
        self.assertEqual(list(figure.data[0].y), [-2, 0])
        self.assertEqual(figure.data[2].marker.symbol, 'x')
        self.assertEqual(figure.layout.yaxis.scaleanchor, 'x')

    def test_nonfinite_and_invalid_roots(self):
        figure, omitted = root_figure('{1e999, 2}')
        self.assertEqual(omitted, 1)
        self.assertEqual(list(figure.data[0].x), [2])
        self.assertFalse(root_figure('{}')[0].data)
        with self.assertRaises(ValueError):
            root_figure('not roots')


class RuntimeTests(unittest.TestCase):
    def wait_for_finish(self, manager):
        deadline = time.monotonic() + 8
        while manager.snapshot().running and time.monotonic() < deadline:
            time.sleep(.02)
        self.assertFalse(manager.snapshot().running)

    def test_drain_without_browser_and_retain_exit_status(self):
        manager = RunManager()
        with tempfile.TemporaryDirectory() as folder:
            manager.start([sys.executable, '-c', 'for i in range(3000): print(i)'], {}, Path(folder))
            self.wait_for_finish(manager)
            state = manager.snapshot()
            self.assertEqual(state.code, 0)
            self.assertEqual(len(manager.lines), 2000)
            self.assertIn('2999', state.output)
            self.assertIn('\n0\n', state.log_path.read_text())
            self.assertTrue(manager.job.events.empty())

    def test_duplicate_start_and_stop(self):
        manager = RunManager()
        with tempfile.TemporaryDirectory() as folder:
            manager.start([sys.executable, '-c', 'import time; time.sleep(60)'], {}, Path(folder))
            try:
                with self.assertRaisesRegex(ValueError, 'already running'):
                    manager.start([sys.executable, '-c', 'pass'], {}, Path(folder))
                manager.stop()
                self.wait_for_finish(manager)
                self.assertTrue(manager.snapshot().cancelled)
            finally:
                manager.close()


class BrowserTests(unittest.TestCase):
    def setUp(self):
        self.folder = tempfile.TemporaryDirectory()
        self.addCleanup(self.folder.cleanup)
        self.path = Path(self.folder.name) / 'results.csv'
        with self.path.open('w') as handle:
            writer = csv.DictWriter(handle, fieldnames=['Tableau', 'SucceededQ', 'BetheRoots'])
            writer.writeheader()
            writer.writerow(dict(Tableau='{{1,3},{2}}', SucceededQ='True', BetheRoots='{{1+2*I},{3}}'))
            writer.writerow(dict(Tableau='{{1,2},{3}}', SucceededQ='False', BetheRoots='bad roots'))
        config = Configuration(output=self.folder.name)
        patcher = patch('bae_bertini.config.load_config', return_value=config)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.app = AppTest.from_file(str(ROOT / 'streamlit_app.py')).run(timeout=20)
        self.assertFalse(self.app.exception)

    def button(self, label):
        return next(b for b in self.app.button if b.label == label)

    def test_modes_preserve_hidden_fields_and_numerical_settings(self):
        app = self.app
        app.selectbox(key='mode').select(MODES[1]).run()
        app.text_input(key='jobs').set_value('3').run()
        app.text_input(key='setting_WORKING_PRECISION').set_value('200').run()
        for mode in (MODES[3], MODES[0], MODES[2], MODES[4], MODES[1]):
            app.selectbox(key='mode').select(mode).run()
            self.assertFalse(app.exception, mode)
        self.assertEqual(app.text_input(key='jobs').value, '3')
        self.assertEqual(app.text_input(key='setting_WORKING_PRECISION').value, '200')

    def test_bad_input_never_launches(self):
        self.app.text_input(key='input_' + MODES[0]).set_value('{{1,1},{2}}').run()
        with patch('bae_bertini.jobs.RunManager.start') as start:
            self.button('Run calculation').click().run()
            start.assert_not_called()
        self.assertFalse(self.app.exception)
        self.assertTrue(any('exactly once' in e.value for e in self.app.error))

    def test_results_comparison_and_unparseable_row(self):
        app = self.app
        self.assertEqual(len(app.get('plotly_chart')), 1)
        next(c for c in app.checkbox if c.label == 'Compare with another result').check().run()
        self.assertFalse(app.exception)
        self.assertEqual(len(app.get('plotly_chart')), 1)
        app.selectbox(key='a_row_' + str(self.path)).select(1).run()
        self.assertFalse(app.exception)
        self.assertTrue(any('Root plot unavailable' in w.value for w in app.warning))
        next(c for c in app.checkbox if c.label == 'Prepare full CSV download').check().run()
        self.assertEqual(len(app.get('download_button')), 1)
        self.assertFalse(app.exception)

    def test_prepared_csv_is_read_once_and_refreshes_after_replacement(self):
        app = self.app
        read_bytes = Path.read_bytes
        reads = []
        def read(path):
            if path == self.path:
                reads.append(path)
            return read_bytes(path)
        with patch.object(Path, 'read_bytes', read):
            next(c for c in app.checkbox if c.label == 'Prepare full CSV download').check().run()
            app.run()
            self.assertEqual(len(reads), 1)
            with self.path.open('a') as handle:
                handle.write('"{{1}}",True,{}\n')
            app.run()
            self.assertEqual(len(reads), 2)
        self.assertFalse(app.exception)

    def test_run_and_stop_controls_survive_reruns(self):
        with patch('bae_bertini.config.check_dependencies', return_value=[]), \
             patch('bae_bertini.config.save_config'), \
             patch('bae_bertini.config.Configuration.command', return_value=(
                 [sys.executable, '-c', 'import time; print("started", flush=True); time.sleep(60)'],
                 {'BERTINI_RESULT_SYT_DIR': self.folder.name})), \
             patch('bae_bertini.jobs.STATE', Path(self.folder.name)):
            self.button('Run calculation').click().run()
            try:
                self.assertFalse(self.app.exception)
                self.app.run()
                self.assertTrue(self.button('Run calculation').disabled)
                self.button('Stop calculation').click().run()
                deadline = time.monotonic() + 8
                while time.monotonic() < deadline:
                    self.app.run()
                    if not self.button('Run calculation').disabled:
                        break
                    time.sleep(.05)
                self.assertFalse(self.app.exception)
                self.assertFalse(self.button('Run calculation').disabled)
            finally:
                # Shared resource persists across AppTest browser reruns too.
                if not self.button('Stop calculation').disabled:
                    self.button('Stop calculation').click().run()


if __name__ == '__main__':
    unittest.main()
