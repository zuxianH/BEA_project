"""Run with .venv/bin/python -m unittest discover -s tests -v."""

import csv
from fractions import Fraction
from decimal import Decimal as D
import multiprocessing
import os
from pathlib import Path
import random
import signal
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from bae_bertini import flip_checks as fast
from bae_bertini import crosscheck
from bae_bertini import continuation
from bae_bertini import results as merger
from validate_reference_results import root_error


class ComplexText:
    def __init__(self, real, imaginary="0"):
        self.text = f"({real}, {imaginary})"

    def __repr__(self):
        return self.text


class NumericalTests(unittest.TestCase):
    def test_expression_literals_preserve_precision_and_source_offsets(self):
        decimal = '1.234567890123456789012345678901234567890123456789'
        for newline in ('\n', '\r\n', '\r'):
            expression = f'(α * {decimal}`48 +{newline} 2.5*^-40 - 7/3)'
            with self.subTest(newline=repr(newline)), \
                 patch.object(continuation, 'rational', side_effect=Fraction):
                result = continuation.parse_expression(expression, {'α': Fraction(2)})
                self.assertEqual(result, 2 * Fraction(decimal) + Fraction('2.5e-40') - Fraction(7, 3))

    def test_expression_large_literals_do_not_round_through_float(self):
        with patch.object(continuation, 'rational', side_effect=Fraction):
            self.assertEqual(continuation.parse_expression('1e400 + 1e-400', {}),
                             Fraction('1e400') + Fraction('1e-400'))
            self.assertEqual(continuation.parse_expression('-(+x)**3 / 2', {'x': Fraction(3)}),
                             Fraction(-27, 2))

    def test_real_export_preserves_digits_and_checks_imaginary_part(self):
        decimal = "1.234567890123456789012345678901234567890123456789"
        self.assertEqual(continuation.bertini_complex_real_text(ComplexText(decimal, "1e-40")), decimal)
        for value in [ComplexText("1", "0.1"), ComplexText("NaN"), ComplexText("1", "Infinity")]:
            with self.assertRaises(ValueError):
                continuation.bertini_complex_real_text(value)

    def test_failed_atomic_export_keeps_previous_file(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "output.csv"
            output.write_text("previous complete result\n")
            with self.assertRaises(ValueError):
                continuation.write_legacy_result(output, ["a", "b"], [ComplexText("1"), ComplexText("2", "3")])
            self.assertEqual(output.read_text(), "previous complete result\n")
            self.assertEqual(list(Path(directory).iterdir()), [output])
            continuation.write_legacy_result(output, ["a"], [ComplexText("1.123456789012345678901234567890")])
            with output.open() as handle:
                self.assertEqual(next(csv.DictReader(handle))["b_final_value"], "1.123456789012345678901234567890")

    def test_failed_tracker_does_not_publish_an_endpoint(self):
        from types import SimpleNamespace
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "output.csv"
            args = SimpleNamespace(output_dir=None, output=output, lambda_column="lambda0",
                parameter_symbol="h", target="0", path_symbol="t", tracking_tolerance=1e-12,
                infinite_tolerance=1e8, max_precision=None, max_num_steps=None,
                initial_step_size=None, max_step_size=None, max_newton_iterations=None, predictor=None)
            system = unittest.mock.Mock()
            with patch.object(continuation, "load_problem", return_value=([], [], "1", system, [])), \
                 patch.object(continuation, "continue_parameter", return_value=("Failed", [], [])):
                with self.assertRaises(SystemExit):
                    continuation.run_one(Path(directory)/"input.csv", args)
            self.assertFalse(output.exists())

    def test_optimized_distances_equal_original_definition(self):
        rng = random.Random(123)
        for m, n in [(1, 1), (3, 6), (6, 3), (8, 8)]:
            for _ in range(8):
                a = [(D(rng.randrange(-1000, 1000))/97, D(rng.randrange(-1000, 1000))/89) for _ in range(m)]
                b = [(D(rng.randrange(-1000, 1000))/101, D(rng.randrange(-1000, 1000))/83) for _ in range(n)]
                def directed(left, right):
                    return max(min(((x[0]-y[0])**2+(x[1]-y[1])**2).sqrt() for y in right) for x in left)
                expected = max(directed(a, b), directed(b, a))
                self.assertEqual(fast.hausdorff_distance(a, b), expected)
                self.assertEqual(crosscheck.hausdorff_distance(a, b), expected)
        self.assertEqual(fast.hausdorff_distance([], []), 0)
        self.assertEqual(fast.hausdorff_distance([], [(D(0), D(0))]), D("Infinity"))

    def test_reference_comparison_respects_levels_and_multiplicity(self):
        self.assertEqual(root_error("{{0, 1, 1}, {2}}", "{{1, 0, 1}, {2}}"), 0)
        self.assertGreater(root_error("{{0, 0, 1}, {2}}", "{{0, 1, 1}, {2}}"), 0)
        self.assertGreater(root_error("{{0, 1, 2}, {3}}", "{{0, 1, 3}, {2}}"), 0)


def hold_lock(aggregate, ready):
    with merger.result_lock(aggregate):
        ready.set()
        time.sleep(30)


def concurrent_merge(stage, aggregate, failures):
    merger.merge_results(stage, "{2,1}", aggregate, failures)


class MergeTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.stage = self.root / "staged"
        self.stage.mkdir()
        self.aggregate = self.root / "aggregate.csv"
        self.failures = self.root / "fail.txt"

    def row(self, tableau="{{1,2},{3}}", success="true", run="one"):
        return dict(RunID=run, Tableau=tableau, YoungDiagram="{2,1}", SucceededQ=success,
                    FailureReason="None" if success == "true" else "failed", TimingSeconds="1", BetheRoots="{{1}}",
                    Diagnostic="line one\nline two\twith tab")

    def write(self, path, row):
        merger.write_table(path, list(row), [row])

    def merge(self):
        return merger.merge_results(self.stage, "{2,1}", self.aggregate, self.failures)

    def test_resume_noop_and_failure_retry(self):
        self.write(self.stage / "a.csv", self.row(success="false"))
        self.assertTrue(self.merge())
        with self.failures.open(newline="") as handle:
            self.assertEqual(next(csv.DictReader(handle, delimiter="\t"))["Diagnostic"], self.row()["Diagnostic"])
        before = self.aggregate.stat().st_mtime_ns
        self.assertFalse(self.merge())
        self.assertEqual(self.aggregate.stat().st_mtime_ns, before)
        self.write(self.stage / "a.csv", self.row(run="retry"))
        self.merge()
        with self.aggregate.open() as handle:
            rows = list(csv.DictReader(handle))
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["RunID"], "retry")
        with self.failures.open() as handle:
            self.assertEqual(list(csv.DictReader(handle, delimiter="\t")), [])

    def test_malformed_stage_cannot_overwrite_aggregate(self):
        self.write(self.aggregate, self.row())
        before = self.aggregate.read_bytes()
        broken = self.stage / "broken.csv"
        broken.write_text("RunID,Tableau\npartial\n")
        with self.assertRaises(ValueError):
            self.merge()
        self.assertEqual(self.aggregate.read_bytes(), before)
        self.assertTrue(broken.exists())

    def test_interrupted_merge_is_resumable(self):
        snapshot = self.stage / "a.csv"
        self.write(snapshot, self.row())
        writer = merger.write_table
        def fail_second_write(path, *args, **kwargs):
            if path == self.failures:
                raise OSError("simulated disk error")
            return writer(path, *args, **kwargs)
        with patch.object(merger, "write_table", side_effect=fail_second_write):
            with self.assertRaises(OSError):
                self.merge()
        self.assertTrue(snapshot.exists())
        self.merge()
        self.assertFalse(snapshot.exists())

    def test_lock_released_after_killed_writer(self):
        ready = multiprocessing.Event()
        proc = multiprocessing.Process(target=hold_lock, args=(self.aggregate, ready))
        proc.start()
        try:
            self.assertTrue(ready.wait(5))
            with self.assertRaises(TimeoutError):
                with merger.result_lock(self.aggregate, timeout=0.1):
                    pass
            os.kill(proc.pid, signal.SIGKILL)
            proc.join(5)
            with merger.result_lock(self.aggregate, timeout=1):
                pass
        finally:
            if proc.is_alive():
                proc.kill()
            proc.join()

    def test_concurrent_mergers_preserve_both_batches(self):
        other = self.root / "other"
        other.mkdir()
        self.write(self.stage / "a.csv", self.row())
        self.write(other / "b.csv", self.row(tableau="{{1,3},{2}}"))
        processes = [multiprocessing.Process(target=concurrent_merge, args=(p, self.aggregate, self.failures))
                     for p in (self.stage, other)]
        for proc in processes:
            proc.start()
        for proc in processes:
            proc.join(10)
            self.assertEqual(proc.exitcode, 0)
        with self.aggregate.open() as handle:
            self.assertEqual(len(list(csv.DictReader(handle))), 2)

    def test_launcher_batches_merges_and_resumes_without_rewriting(self):
        project = self.root / "project"
        project.mkdir()
        source = Path(__file__).resolve().parents[1]
        for directory in ["scripts", "src", "wolfram"]:
            shutil.copytree(source / directory, project / directory)
        (project / ".venv").symlink_to(source / ".venv", target_is_directory=True)
        kernel = project / "fake-kernel"
        kernel.write_text(f"#!{sys.executable}\n" + '''import os, sys, time
from pathlib import Path
from bae_bertini.results import write_table
time.sleep(0.05)
tableau = sys.argv[-1]
path = Path(os.environ['BERTINI_RESULT_SYT_DIR']) / (tableau + '.csv')
path.parent.mkdir(parents=True, exist_ok=True)
row = dict(RunID=tableau, Tableau=tableau, YoungDiagram='{3,2,1}', SucceededQ='true',
           FailureReason='None', TimingSeconds='0.05', BetheRoots='{{1},{0}}')
write_table(path, list(row), [row])
''')
        kernel.chmod(0o755)
        reference = source / "data/references/all_SYT_{3,2,1}.csv"
        with reference.open() as handle:
            tableaux = [r["Tableau"] for r in csv.DictReader(handle)]
        listing = project / "tableaux.txt"
        listing.write_text("\n".join(tableaux) + "\n")
        env = dict(os.environ, WOLFRAM_KERNEL=str(kernel), RESULT_MERGE_EVERY="100",
                   RESULT_MERGE_INTERVAL="60", BERTINI_RESULT_SYT_DIR=str(project / "results"))
        command = ["bash", str(project / "scripts/submit_run_single_jobs.sh"), "--yd", "{3,2,1}",
                   "--list", str(listing), "-j", "2", "--no-logs"]
        proc = subprocess.run(command, env=env, capture_output=True, text=True, timeout=15)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertEqual(proc.stdout.count("Updated aggregate:"), 1)
        aggregate = project / "results/all_SYT_{3,2,1}.csv"
        with aggregate.open() as handle:
            self.assertEqual(len(list(csv.DictReader(handle))), len(tableaux))
        before = aggregate.stat().st_mtime_ns
        proc = subprocess.run(command, env=env, capture_output=True, text=True, timeout=15)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("Submitted: 0", proc.stdout)
        self.assertEqual(aggregate.stat().st_mtime_ns, before)


if __name__ == "__main__":
    unittest.main()
