#!/usr/bin/env python3
"""Fast evacuation flip-distance checks for aggregate Bethe-root CSV files."""

from __future__ import annotations

import argparse
import ast
import csv
import re
import shutil
import time
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Any


PRECISION_RE = re.compile(r"`(?:\d+(?:\.\d*)?|\.\d+)?")
getcontext().prec = 100


def input_form_key(value: str) -> str:
    return "".join(value.split())


def mathematica_list_to_python(text: str) -> Any:
    return ast.literal_eval(text.replace("{", "[").replace("}", "]"))


def parse_tableau(text: str) -> list[list[int]]:
    value = mathematica_list_to_python(text)
    if not (
        isinstance(value, list)
        and all(isinstance(row, list) and all(isinstance(x, int) for x in row) for row in value)
    ):
        raise ValueError(f"not a tableau: {text}")
    return value


def tableau_to_input_form(tableau: list[list[int]]) -> str:
    rows = [", ".join(str(value) for value in row) for row in tableau]
    return "{" + ", ".join("{" + row + "}" for row in rows) + "}"


def evacuate_tableau(tableau: list[list[int]]) -> list[list[int]]:
    """Schuetzenberger evacuation using successive jeu de taquin slides."""
    shape = [len(row) for row in tableau]
    working = {
        (row_index, column_index): value
        for row_index, row in enumerate(tableau)
        for column_index, value in enumerate(row)
    }
    n = len(working)
    evacuated: dict[tuple[int, int], int] = {}

    for step in range(1, n + 1):
        hole = min(working, key=working.__getitem__)
        del working[hole]

        while True:
            candidates = [
                position
                for position in ((hole[0], hole[1] + 1), (hole[0] + 1, hole[1]))
                if position in working
            ]
            if not candidates:
                break
            next_hole = min(candidates, key=working.__getitem__)
            working[hole] = working[next_hole]
            del working[next_hole]
            hole = next_hole

        evacuated[hole] = n - step + 1
        working = {position: value - 1 for position, value in working.items()}

    return [
        [evacuated[(row_index, column_index)] for column_index in range(row_length)]
        for row_index, row_length in enumerate(shape)
    ]


def decimal_number(text: str) -> Decimal:
    return Decimal(text.replace("*10^", "E").replace("*^", "E"))


def parse_root(text: str) -> tuple[Decimal, Decimal]:
    text = text.replace(" ", "")
    if "I" not in text:
        return decimal_number(text), Decimal(0)

    core = text.replace("*I", "").replace("I", "")
    separator = None
    for index, character in enumerate(core[1:], start=1):
        if character in "+-" and core[index - 1] not in "Ee^":
            separator = index

    if separator is None:
        real_text, imaginary_text = "0", core
    else:
        real_text, imaginary_text = core[:separator], core[separator:]
    if imaginary_text in {"", "+", "-"}:
        imaginary_text += "1"
    return decimal_number(real_text), decimal_number(imaginary_text)


def parse_roots(text: str) -> list[tuple[Decimal, Decimal]]:
    converted = PRECISION_RE.sub("", text.strip())
    converted = converted.replace("{", "").replace("}", "")
    return [parse_root(token.strip()) for token in converted.split(",") if token.strip()]


def point_distance(left: tuple[Decimal, Decimal], right: tuple[Decimal, Decimal]) -> Decimal:
    real_delta = left[0] - right[0]
    imaginary_delta = left[1] - right[1]
    return (real_delta * real_delta + imaginary_delta * imaginary_delta).sqrt()


def hausdorff_distance(
    left: list[tuple[Decimal, Decimal]],
    right: list[tuple[Decimal, Decimal]],
) -> Decimal:
    if not left or not right:
        if not left and not right:
            return Decimal(0)
        return Decimal("Infinity")

    def directed(source, target):
        return max(min(point_distance(a, b) for b in target) for a in source)

    return max(directed(left, right), directed(right, left))


def aggregate_file_from_argument(argument: str, result_dir: Path) -> Path:
    path = Path(argument)
    if path.exists() or argument.endswith(".csv"):
        return path
    yd_key = input_form_key(argument)
    return result_dir / f"all_SYT_{yd_key}.csv"


def load_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        return [
            row
            for row in reader
            if row.get("Tableau") and row.get("SucceededQ", "").lower() == "true"
        ]


def deletion_report_keys(report: dict[str, str]) -> set[str]:
    """Rows to remove when a real jump/malformed pair is reported."""
    if report.get("Reason") not in {
        "DistanceAboveTolerance",
        "RootCountMismatch",
    } and not report.get("Reason", "").startswith("RootParseError:"):
        return set()

    keys = {input_form_key(report["SYT"])}
    flip_syt = report.get("FlipSYT", "")
    if flip_syt:
        keys.add(input_form_key(flip_syt))
    return keys


def delete_tableau_rows(path: Path, delete_keys: set[str]) -> tuple[int, int, Path]:
    backup_path = path.with_name(
        f"{path.name}.bak-{time.strftime('%Y%m%d-%H%M%S')}"
    )
    shutil.copy2(path, backup_path)

    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        fieldnames = reader.fieldnames
        if fieldnames is None:
            raise ValueError(f"CSV has no header: {path}")
        all_rows = list(reader)

    kept_rows = [
        row
        for row in all_rows
        if input_form_key(row.get("Tableau", "")) not in delete_keys
    ]

    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(kept_rows)

    return len(all_rows), len(all_rows) - len(kept_rows), backup_path


def comparison_rows(
    rows: list[dict[str, str]],
    *,
    tolerance: Decimal,
    all_directions: bool,
) -> tuple[list[dict[str, str]], dict[str, int]]:
    rows_by_tableau = {input_form_key(row["Tableau"]): row for row in rows}
    reports: list[dict[str, str]] = []
    seen_pairs: set[tuple[str, str]] = set()
    counts = {
        "compared": 0,
        "passed": 0,
        "failed": 0,
        "missing_flip": 0,
        "root_count_mismatch": 0,
        "parse_errors": 0,
    }

    for index, row in enumerate(rows, start=1):
        try:
            syt = parse_tableau(row["Tableau"])
            flip_syt = evacuate_tableau(syt)
            syt_key = input_form_key(row["Tableau"])
            flip_text = tableau_to_input_form(flip_syt)
            flip_key = input_form_key(flip_text)
        except Exception as exc:
            counts["parse_errors"] += 1
            reports.append(
                {
                    "Index": str(index),
                    "SYT": row.get("Tableau", ""),
                    "FlipSYT": "",
                    "FlipFoundQ": "False",
                    "RootCount": "",
                    "FlipRootCount": "",
                    "Distance": "",
                    "SameRootsQ": "False",
                    "Reason": f"ParseError: {exc}",
                }
            )
            continue

        pair_key = tuple(sorted((syt_key, flip_key)))
        if not all_directions and pair_key in seen_pairs:
            continue
        seen_pairs.add(pair_key)

        flip_row = rows_by_tableau.get(flip_key)
        if flip_row is None:
            counts["missing_flip"] += 1
            reports.append(
                {
                    "Index": str(index),
                    "SYT": row["Tableau"],
                    "FlipSYT": flip_text,
                    "FlipFoundQ": "False",
                    "RootCount": "",
                    "FlipRootCount": "",
                    "Distance": "",
                    "SameRootsQ": "False",
                    "Reason": "FlipSYTNotFound",
                }
            )
            continue

        try:
            roots = parse_roots(row.get("BetheRoots", ""))
            flip_roots = [
                (-real, -imaginary)
                for real, imaginary in parse_roots(flip_row.get("BetheRoots", ""))
            ]
        except Exception as exc:
            counts["parse_errors"] += 1
            reports.append(
                {
                    "Index": str(index),
                    "SYT": row["Tableau"],
                    "FlipSYT": flip_row["Tableau"],
                    "FlipFoundQ": "True",
                    "RootCount": "",
                    "FlipRootCount": "",
                    "Distance": "",
                    "SameRootsQ": "False",
                    "Reason": f"RootParseError: {exc}",
                }
            )
            continue

        counts["compared"] += 1

        if len(roots) != len(flip_roots):
            counts["root_count_mismatch"] += 1
            reports.append(
                {
                    "Index": str(index),
                    "SYT": row["Tableau"],
                    "FlipSYT": flip_row["Tableau"],
                    "FlipFoundQ": "True",
                    "RootCount": str(len(roots)),
                    "FlipRootCount": str(len(flip_roots)),
                    "Distance": "",
                    "SameRootsQ": "False",
                    "Reason": "RootCountMismatch",
                }
            )
            continue

        distance = hausdorff_distance(roots, flip_roots)
        same_roots = distance <= tolerance
        counts["passed" if same_roots else "failed"] += 1
        if not same_roots:
            reports.append(
                {
                    "Index": str(index),
                    "SYT": row["Tableau"],
                    "FlipSYT": flip_row["Tableau"],
                    "FlipFoundQ": "True",
                    "RootCount": str(len(roots)),
                    "FlipRootCount": str(len(flip_roots)),
                    "Distance": f"{distance:.20E}",
                    "SameRootsQ": "False",
                    "Reason": "DistanceAboveTolerance",
                }
            )

    return reports, counts


def write_report(path: Path, reports: list[dict[str, str]]) -> None:
    fieldnames = [
        "Index",
        "SYT",
        "FlipSYT",
        "FlipFoundQ",
        "RootCount",
        "FlipRootCount",
        "Distance",
        "SameRootsQ",
        "Reason",
    ]
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(reports)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Check Bethe roots against negated Schuetzenberger evacuation roots "
            "without using Mathematica."
        )
    )
    parser.add_argument(
        "csv_or_yd",
        help="Aggregate CSV path, or Young diagram like '{10,6}' for Result_SYT/all_SYT_{10,6}.csv.",
    )
    parser.add_argument("--result-dir", type=Path, default=Path("Result_SYT"))
    parser.add_argument("--tolerance", default="1e-5")
    parser.add_argument("--output", type=Path, help="Write failing/missing comparisons to this CSV.")
    parser.add_argument("--all-directions", action="store_true", help="Check T and Evac(T) separately.")
    parser.add_argument("--limit", type=int, default=20, help="Number of failing rows to print. Default: 20.")
    parser.add_argument(
        "--delete-jumps",
        action="store_true",
        help=(
            "Rewrite the aggregate CSV and delete both tableaux in each failed "
            "distance/root-count orbit. A timestamped .bak file is always written first."
        ),
    )
    return parser


def main() -> int:
    args = build_parser().parse_args()
    started = time.perf_counter()
    csv_path = aggregate_file_from_argument(args.csv_or_yd, args.result_dir)
    tolerance = decimal_number(args.tolerance)

    rows = load_rows(csv_path)
    reports, counts = comparison_rows(
        rows,
        tolerance=tolerance,
        all_directions=args.all_directions,
    )
    elapsed = time.perf_counter() - started

    output_path = args.output
    if output_path is None and reports:
        output_path = csv_path.with_name(csv_path.stem + "_false_flip_distances.csv")
    if output_path is not None:
        write_report(output_path, reports)

    delete_keys: set[str] = set()
    if args.delete_jumps:
        for report in reports:
            delete_keys.update(deletion_report_keys(report))

    print(f"File={csv_path}")
    print(f"SuccessfulRows={len(rows)}")
    print(f"ComparedOrbits={counts['compared']}")
    print(f"Passed={counts['passed']}")
    print(f"Failed={counts['failed']}")
    print(f"MissingFlip={counts['missing_flip']}")
    print(f"RootCountMismatch={counts['root_count_mismatch']}")
    print(f"ParseErrors={counts['parse_errors']}")
    print(f"Tolerance={tolerance}")
    print(f"Seconds={elapsed:.3f}")
    if output_path is not None:
        print(f"Report={output_path}")

    if args.delete_jumps:
        if delete_keys:
            before_count, deleted_count, backup_path = delete_tableau_rows(csv_path, delete_keys)
            print(f"DeleteJumps=True")
            print(f"DeletedRows={deleted_count}")
            print(f"RowsBeforeDelete={before_count}")
            print(f"RowsAfterDelete={before_count - deleted_count}")
            print(f"Backup={backup_path}")
        else:
            print("DeleteJumps=True")
            print("DeletedRows=0")

    for report in reports[: max(args.limit, 0)]:
        print(
            "FalseFlipDistance"
            f"[Index={report['Index']}, Distance={report['Distance'] or report['Reason']}, "
            f"SYT={report['SYT']}, FlipSYT={report['FlipSYT']}]"
        )
    if len(reports) > args.limit:
        print(f"... {len(reports) - args.limit} more rows in {output_path}")

    return 0 if not reports else 1


if __name__ == "__main__":
    raise SystemExit(main())
