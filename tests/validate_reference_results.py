#!/usr/bin/env python3
"""Rerun every reference tableau in isolation and compare roots within each level.

Example: python3 tests/validate_reference_results.py --output-dir /tmp/bertini-check
Requires WolframKernel and the project's Bertini virtual environment.
"""

import argparse
import concurrent.futures
import csv
from decimal import Decimal, localcontext
import hashlib
import itertools
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from bae_bertini.flip_checks import parse_roots


def root_levels(text):
    """Keep nesting levels separate; flattening can conceal misplaced roots."""
    groups = []
    depth = 0
    start = None
    for index, char in enumerate(text.strip()):
        if char == "{":
            depth += 1
            if depth == 2:
                start = index
        elif char == "}":
            if depth == 2:
                groups.append(parse_roots(text.strip()[start:index + 1]))
            depth -= 1
    if depth or not groups:
        raise ValueError(f"Invalid nested roots: {text}")
    return groups


def root_error(expected, actual):
    """Independent one-to-one comparison, including multiplicity, for small cases."""
    # ThreadPool workers have their own Decimal context (28 digits by default).
    with localcontext() as context:
        context.prec = 100
        return _root_error(expected, actual)


def _root_error(expected, actual):
    left, right = root_levels(expected), root_levels(actual)
    if [len(g) for g in left] != [len(g) for g in right]:
        return Decimal("Infinity")
    errors = []
    for a, b in zip(left, right):
        if len(a) > 8:
            raise ValueError("This exhaustive reference comparator supports <= 8 roots per level")
        errors.append(min(
            (max(((x[0]-y[0])**2 + (x[1]-y[1])**2).sqrt()
                 for x, y in zip(a, order)) if a else Decimal(0))
            for order in itertools.permutations(b)
        ))
    return max(errors, default=Decimal(0))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-dir", type=Path, default=ROOT)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--tolerance", default="1e-8")
    parser.add_argument("--limit", type=int)
    parser.add_argument("references", nargs="*", type=Path, default=[
        ROOT / "data/references/all_SYT_{3,2,1}.csv",
        ROOT / "data/references/all_SYT_{4,2,1}.csv",
    ])
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=False)
    project = args.project_dir.resolve()
    tolerance = Decimal(args.tolerance)
    hashes = {str(p.resolve()): hashlib.sha256(p.read_bytes()).hexdigest() for p in args.references}
    cases = []
    for path in args.references:
        with path.open(newline="") as handle:
            for row in csv.DictReader(handle):
                if row["SucceededQ"].lower() == "true":
                    cases.append((path.name, row))
    if args.limit:
        cases = cases[:args.limit]
    settings = {
        "BERTINI_INITIAL_LAMBDA": "500", "BERTINI_TARGET_LAMBDA": "0",
        "BERTINI_WORKING_PRECISION": "100", "BERTINI_DEFAULT_PRECISION": "100",
        "BERTINI_TRACKING_TOLERANCE": "1e-12", "BERTINI_INFINITE_TOLERANCE": "1e30",
        "BERTINI_MAX_PRECISION": "1200", "BERTINI_MAX_NUM_STEPS": "500000",
        "BERTINI_MAX_STEP_SIZE": "1/200", "BERTINI_MAX_NEWTON_ITERATIONS": "4",
        "BERTINI_PREDICTOR": "RKCashKarp45", "BERTINI_CLEANUP_RUNS": "1",
    }

    def run_case(index, case):
        reference, expected = case
        case_dir = output / f"case-{index:03d}"
        case_dir.mkdir()
        results = case_dir / "results"
        env = dict(os.environ, **settings, BERTINI_RESULT_SYT_DIR=str(results))
        started = time.perf_counter()
        with (case_dir / "stdout.log").open("w") as out, (case_dir / "stderr.log").open("w") as err:
            try:
                proc = subprocess.run([
                    os.environ.get("WOLFRAM_KERNEL", "WolframKernel"), "-noprompt", "-script",
                    str(project / "wolfram/RunSingle.wl"), expected["Tableau"],
                ], cwd=project, env=env, stdout=out, stderr=err, timeout=180)
                code = proc.returncode
            except subprocess.TimeoutExpired:
                code = 124
        actual_rows = []
        for path in results.glob("*.csv"):
            with path.open(newline="") as handle:
                actual_rows.extend(csv.DictReader(handle))
        actual = next((r for r in actual_rows if r.get("Tableau") == expected["Tableau"]), {})
        error = Decimal("Infinity")
        if code == 0 and actual.get("SucceededQ", "").lower() == "true":
            error = root_error(expected["BetheRoots"], actual["BetheRoots"])
        record = {
            "case": index, "reference": reference, "tableau": expected["Tableau"],
            "exit_code": code, "max_root_error": str(error), "passed": error <= tolerance,
            "wall_seconds": time.perf_counter() - started,
            "solver_seconds": actual.get("TimingSeconds"),
        }
        print(json.dumps(record), flush=True)
        return record

    started = time.perf_counter()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(run_case, i, case) for i, case in enumerate(cases, 1)]
        records = [f.result() for f in futures]
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in hashes.items())
    summary = {
        "project": str(project), "reference_sha256": hashes, "settings": settings,
        "tolerance": str(tolerance), "passed": sum(r["passed"] for r in records),
        "total": len(records), "wall_seconds": time.perf_counter()-started, "cases": records,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"Passed {summary['passed']}/{summary['total']}; report: {output / 'summary.json'}")
    return 0 if summary["passed"] == summary["total"] and records else 1


if __name__ == "__main__":
    raise SystemExit(main())
