#!/usr/bin/env python3
"""Solve an SYT, then track its lambda0 -> target endpoint back to lambda0.

The returned solution is compared with the original lambda0 start point by the
symmetric Hausdorff distance of the variable values, as complex point sets.
"""
from __future__ import annotations

import argparse
import csv
from decimal import Decimal
import os
from pathlib import Path
import re
import subprocess
import sys
import uuid

import bertini

from .continuation import bertini_complex_text, continue_parameter, load_problem
from .crosscheck import decimal_number, hausdorff_distance, point_distance
from .paths import RUNS, WOLFRAM


def complex_parts(value) -> tuple[Decimal, Decimal]:
    real, imaginary = re.fullmatch(r"\(([^,]+),\s*([^,]+)\)", bertini_complex_text(value).strip()).groups()
    return Decimal(real), Decimal(imaginary)


def points(vector) -> list[tuple[Decimal, Decimal]]:
    return [complex_parts(vector[index]) for index in range(len(vector))]


def setting(name, cast=str, default=None):
    value = os.environ.get("BERTINI_" + name, "").strip()
    return cast(value) if value else default


def track(system, start_point):
    status, endpoint, _ = continue_parameter(
        system, start_point,
        tracking_tolerance=setting("TRACKING_TOLERANCE", float, 1e-8),
        infinite_tolerance=setting("INFINITE_TOLERANCE", float, 1e8),
        max_precision=setting("MAX_PRECISION", int),
        max_num_steps=setting("MAX_NUM_STEPS", int),
        initial_step_size=setting("INITIAL_STEP_SIZE"),
        max_step_size=setting("MAX_STEP_SIZE"),
        max_newton_iterations=setting("MAX_NEWTON_ITERATIONS", int),
        predictor=setting("PREDICTOR"),
    )
    if str(status) != "Success":
        raise SystemExit(f"Bertini path tracking failed: {status}")
    return endpoint


def reverse_check(input_path: Path, target: str, tolerance: str) -> tuple[list[str], bool]:
    """Track input_path from its lambda0 to target and back; return report lines."""
    precision = setting("DEFAULT_PRECISION", int)
    if precision is not None:
        bertini.default_precision(precision)
    options = dict(lambda_column="lambda0", parameter_symbol="h", path_symbol="t")
    rows, names, start_lambda, system, start = load_problem(input_path, target_value=target, **options)
    forward = track(system, start)
    *_, reverse_system, _ = load_problem(input_path, target_value=start_lambda, lambda_start=target, **options)
    returned = track(reverse_system, forward)

    original, back = points(start), points(returned)
    distance = hausdorff_distance(original, back)
    largest = max(point_distance(a, b) for a, b in zip(original, back))
    limit = decimal_number(tolerance)
    passed = distance <= limit
    lines = [
        f"SYT={rows[0].get('syt', '')}",
        f"Path=lambda {start_lambda} -> {target} -> {start_lambda}",
        'Comparison="Hausdorff[Solution[lambda0], Reverse[Forward[Solution[lambda0]]]]"',
        f"VariableCount={len(names)}",
        f"Distance={distance:.20E}",
        f"MaxVariableDifference={largest:.20E}",
        f"Tolerance={limit}",
        f"Passed={passed}",
    ]
    saved = input_path.with_name("output.csv")
    if saved.is_file():
        with saved.open(newline="", encoding="utf-8") as stream:
            values = [(decimal_number(row["b_final_value"]), Decimal(0)) for row in csv.DictReader(stream)]
        # Confirms the reverse leg started from the solution the workflow saved.
        lines.insert(4, f"ForwardVsSavedSolution={hausdorff_distance(points(forward), values):.20E}")
    return lines, passed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("syt")
    parser.add_argument("--tolerance", default="1e-5")
    args = parser.parse_args()

    work = RUNS / f"reverse-{uuid.uuid4().hex[:8]}"
    environment = dict(os.environ, BERTINI_WORK_DIR=str(work / "forward"))
    kernel = os.environ.get("WOLFRAM_KERNEL", "WolframKernel")
    print(f"Running SYT forward: {args.syt}", flush=True)
    code = subprocess.run([kernel, "-noprompt", "-script", str(WOLFRAM / "RunSingle.wl"), args.syt],
                          env=environment).returncode
    if code:
        print(f"Forward run failed. Work directory: {work}", file=sys.stderr)
        return code
    input_path = work / "forward" / "saved_data" / "initial_data.csv"
    print(f"Tracking the solution back to lambda0 from {input_path}", flush=True)
    lines, passed = reverse_check(input_path, os.environ.get("BERTINI_TARGET_LAMBDA", "0"), args.tolerance)
    report = "\n".join(lines) + "\n"
    (work / "reverse_report.txt").write_text(report, encoding="utf-8")
    print(report + f"Work directory: {work}")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
