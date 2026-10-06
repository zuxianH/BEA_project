#!/usr/bin/env python3
"""Solve an SYT, then track its lambda0 -> target solution back to lambda0.

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

from .crosscheck import decimal_number, hausdorff_distance, parse_roots, point_distance
from .paths import PYTHON, RUNS, SCRIPTS, WOLFRAM

# Forwarded to the continuation driver exactly as RunSingle.wl does for the forward leg.
SETTINGS = ('TRACKING_TOLERANCE', 'INFINITE_TOLERANCE', 'DEFAULT_PRECISION', 'MAX_PRECISION',
            'MAX_NUM_STEPS', 'INITIAL_STEP_SIZE', 'MAX_STEP_SIZE', 'MAX_NEWTON_ITERATIONS', 'PREDICTOR')


def bertini_complex(text: str) -> tuple[Decimal, Decimal]:
    real, imaginary = re.fullmatch(r"\(([^,]+),\s*([^,]+)\)", text.strip()).groups()
    return Decimal(real), Decimal(imaginary)


def track_back(rows, solution, start_lambda, target, work: Path):
    """Continue the saved target solution to start_lambda; return (roots or None, status)."""
    reverse_input, reverse_output = work / 'reverse_input.csv', work / 'reverse_output.csv'
    with reverse_input.open('w', newline='', encoding='utf-8') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(dict(row, lambda0=target, Initialvar=solution[row['var']]) for row in rows)
    command = [str(PYTHON), str(SCRIPTS / 'continue_lambda0_to_zero.py'), str(reverse_input),
               '--output', str(reverse_output), '--target', start_lambda]
    for name in SETTINGS:
        value = os.environ.get('BERTINI_' + name, '').strip()
        if value:
            command += ['--' + name.lower().replace('_', '-'), value]
    timeout = float(os.environ.get('BERTINI_TIMEOUT') or 900)
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, f'Timeout after {timeout:g} seconds'
    (work / 'reverse.log').write_text(result.stdout + result.stderr, encoding='utf-8')
    if result.returncode:
        return None, (result.stderr.strip().splitlines() or [f'exit code {result.returncode}'])[-1]
    with reverse_output.open(newline='', encoding='utf-8') as stream:
        return [bertini_complex(row['final_value']) for row in csv.DictReader(stream)], 'Success'


def reverse_check(input_path: Path, target: str, tolerance: str, work: Path) -> tuple[list[str], bool]:
    """Compare the lambda0 start point with the saved target solution tracked back to lambda0."""
    with input_path.open(newline='', encoding='utf-8') as stream:
        rows = list(csv.DictReader(stream))
    with (input_path.parent / 'output.csv').open(newline='', encoding='utf-8') as stream:
        solution = {row['var']: row['b_final_value'] for row in csv.DictReader(stream)}
    start_lambda = rows[0]['lambda0']
    returned, status = track_back(rows, solution, start_lambda, target, work)
    limit = decimal_number(tolerance)
    lines = [
        f"SYT={rows[0].get('syt', '')}",
        f"Path=lambda {start_lambda} -> {target} -> {start_lambda}",
        'Comparison="Hausdorff[Solution[lambda0], Reverse[Forward[Solution[lambda0]]]]"',
        f"VariableCount={len(rows)}",
        f"ReverseStatus={status}",
    ]
    passed = False
    if returned is not None:
        original = [parse_roots(row['Initialvar'])[0] for row in rows]
        distance = hausdorff_distance(original, returned)
        largest = max(point_distance(a, b) for a, b in zip(original, returned))
        passed = distance <= limit
        lines += [f"Distance={distance:.20E}", f"MaxVariableDifference={largest:.20E}"]
    return lines + [f"Tolerance={limit}", f"Passed={passed}"], passed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('syt')
    parser.add_argument('--tolerance', default='1e-5')
    args = parser.parse_args()

    work = RUNS / f'reverse-{uuid.uuid4().hex[:8]}'
    environment = dict(os.environ, BERTINI_WORK_DIR=str(work / 'forward'))
    kernel = os.environ.get('WOLFRAM_KERNEL', 'WolframKernel')
    print(f'Running SYT forward: {args.syt}', flush=True)
    code = subprocess.run([kernel, '-noprompt', '-script', str(WOLFRAM / 'RunSingle.wl'), args.syt],
                          env=environment).returncode
    if code:
        print(f'Forward run failed. Work directory: {work}', file=sys.stderr)
        return code
    input_path = work / 'forward' / 'saved_data' / 'initial_data.csv'
    print(f'Tracking the target solution back to lambda0 from {input_path}', flush=True)
    lines, passed = reverse_check(input_path, os.environ.get('BERTINI_TARGET_LAMBDA', '0'),
                                  args.tolerance, work)
    report = '\n'.join(lines) + '\n'
    (work / 'reverse_report.txt').write_text(report, encoding='utf-8')
    print(report + f'Work directory: {work}')
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
