#!/usr/bin/env python3
"""Compare Bethe roots of an SYT with the negated roots of its KKR flip."""

from __future__ import annotations

import argparse
import csv
import re
from decimal import Decimal, getcontext
from pathlib import Path


PRECISION_RE = re.compile(r"`(?:\d+(?:\.\d*)?|\.\d+)?")
getcontext().prec = 100


def tableau_key(text: str) -> str:
    return "".join(text.split())


def decimal_number(text: str) -> Decimal:
    text = text.replace("*10^", "E").replace("*^", "E")
    return Decimal(text)


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


def load_results(result_dir: Path) -> dict[str, tuple[dict[str, str], Path]]:
    results: dict[str, tuple[dict[str, str], Path]] = {}
    for path in result_dir.glob("*.csv"):
        with path.open(newline="", encoding="utf-8") as handle:
            for row in csv.DictReader(handle):
                tableau = row.get("Tableau", "")
                if tableau:
                    results[tableau_key(tableau)] = (row, path)
    return results


def point_distance(
    left: tuple[Decimal, Decimal], right: tuple[Decimal, Decimal]
) -> Decimal:
    real_delta = left[0] - right[0]
    imaginary_delta = left[1] - right[1]
    return (real_delta * real_delta + imaginary_delta * imaginary_delta).sqrt()


def hausdorff_distance(
    left: list[tuple[Decimal, Decimal]],
    right: list[tuple[Decimal, Decimal]],
) -> Decimal:
    """Symmetric Hausdorff distance between two finite complex root sets."""
    if not left or not right:
        if not left and not right:
            return Decimal(0)
        return Decimal("Infinity")

    def directed(source, target):
        return max(min(point_distance(a, b) for b in target) for a in source)

    return max(directed(left, right), directed(right, left))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("result_dir", type=Path)
    parser.add_argument("syt")
    parser.add_argument("flip_syt")
    parser.add_argument("tolerance")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()

    results = load_results(args.result_dir)
    original = results.get(tableau_key(args.syt))
    flipped = results.get(tableau_key(args.flip_syt))
    if original is None or flipped is None:
        missing = "original" if original is None else "flipped"
        raise SystemExit(f"Missing {missing} result CSV in {args.result_dir}")

    original_row, _ = original
    flipped_row, _ = flipped
    if original_row.get("SucceededQ", "").lower() != "true":
        raise SystemExit("Original Bertini result did not succeed")
    if flipped_row.get("SucceededQ", "").lower() != "true":
        raise SystemExit("Flipped Bertini result did not succeed")

    roots = parse_roots(original_row["BetheRoots"])
    flipped_roots = [(-real, -imaginary) for real, imaginary in parse_roots(flipped_row["BetheRoots"])]
    distance = hausdorff_distance(roots, flipped_roots)
    tolerance = decimal_number(args.tolerance)
    passed = distance <= tolerance

    lines = [
        f"SYT={original_row['Tableau']}",
        f"FlipSYT={flipped_row['Tableau']}",
        'Comparison="Hausdorff[Roots[SYT], -Roots[FlipSYT]]"',
        f"RootCount={len(roots)}",
        f"FlipRootCount={len(flipped_roots)}",
        "FlipFoundQ=True",
        f"Distance={distance:.20E}",
        f"Tolerance={tolerance}",
        f"Passed={passed}",
    ]
    report = "\n".join(lines) + "\n"
    if args.report:
        args.report.write_text(report, encoding="utf-8")
    print(report, end="")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
