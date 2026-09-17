#!/usr/bin/env python3
"""Plot Bethe roots from the GoodRoots CSV files.

The CSVs store roots in Mathematica syntax.  Flat root lists are plotted as a
single Bethe level; nested root lists are plotted as separate levels.
"""

from __future__ import annotations

import argparse
import ast
import csv
import html
import math
import re
from collections import defaultdict
from pathlib import Path
from typing import Any


PRECISION_RE = re.compile(r"`[0-9.]*")
SVG_COLORS = (
    "#1f77b4",
    "#d62728",
    "#2ca02c",
    "#9467bd",
    "#ff7f0e",
    "#17becf",
)


def mathematica_to_python(text: str) -> str:
    """Convert the subset of Mathematica syntax used in BetheRoots to Python."""
    converted = text.strip()
    converted = PRECISION_RE.sub("", converted)
    converted = converted.replace("*^", "e")
    converted = converted.replace("{", "[")
    converted = converted.replace("}", "]")
    converted = converted.replace("*I", "j")
    converted = converted.replace("I", "1j")
    return converted


def is_number(value: Any) -> bool:
    return isinstance(value, (int, float, complex))


def extract_levels(value: Any) -> list[list[complex]]:
    """Return one list of complex roots per detected Bethe level."""
    if is_number(value):
        return [[complex(value)]]

    if not isinstance(value, list):
        return []

    if all(is_number(item) for item in value):
        return [[complex(item) for item in value]]

    levels: list[list[complex]] = []
    for item in value:
        levels.extend(extract_levels(item))
    return levels


def parse_roots(text: str) -> list[list[complex]]:
    if not text or text in {"{}", "None"}:
        return []

    python_expr = mathematica_to_python(text)
    try:
        value = ast.literal_eval(python_expr)
    except (SyntaxError, ValueError) as exc:
        raise ValueError(f"could not parse BetheRoots value: {text[:120]}") from exc

    return extract_levels(value)


def read_root_levels(
    csv_path: Path,
    *,
    row_number: int | None = None,
    max_rows: int | None = None,
) -> tuple[list[list[complex]], int, int]:
    """Read roots from one CSV.

    Args:
        csv_path: CSV file to read.
        row_number: Optional 1-based data row to plot.
        max_rows: Optional cap on successful rows read.

    Returns:
        ``(levels, rows_read, skipped_rows)``.
    """
    levels: list[list[complex]] = []
    rows_read = 0
    skipped_rows = 0

    with csv_path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        for index, row in enumerate(reader, start=1):
            if row_number is not None and index != row_number:
                continue

            if row.get("SucceededQ", "").lower() != "true":
                skipped_rows += 1
                continue

            row_levels = parse_roots(row.get("BetheRoots", ""))
            if not row_levels:
                skipped_rows += 1
                continue

            while len(levels) < len(row_levels):
                levels.append([])

            for level_index, roots in enumerate(row_levels):
                levels[level_index].extend(roots)

            rows_read += 1

            if row_number is not None or (max_rows is not None and rows_read >= max_rows):
                break

    return levels, rows_read, skipped_rows


def finite_roots(roots: list[complex]) -> list[complex]:
    return [
        root
        for root in roots
        if math.isfinite(root.real) and math.isfinite(root.imag)
    ]


def nonempty_finite_levels(levels: list[list[complex]]) -> list[list[complex]]:
    nonempty_levels = [finite_roots(level) for level in levels if level]
    if not nonempty_levels:
        raise ValueError("no finite roots found")
    return nonempty_levels


def shared_bounds(levels: list[list[complex]], plot_width: float, plot_height: float) -> tuple[float, float, float, float]:
    all_roots = [root for level in levels for root in level]
    min_x = min(root.real for root in all_roots)
    max_x = max(root.real for root in all_roots)
    min_y = min(root.imag for root in all_roots)
    max_y = max(root.imag for root in all_roots)

    pad_x = max((max_x - min_x) * 0.08, 0.1)
    pad_y = max((max_y - min_y) * 0.08, 0.1)
    min_x -= pad_x
    max_x += pad_x
    min_y -= pad_y
    max_y += pad_y

    x_span = max(max_x - min_x, 1e-9)
    y_span = max(max_y - min_y, 1e-9)
    target_ratio = plot_width / plot_height
    current_ratio = x_span / y_span

    if current_ratio > target_ratio:
        wanted_y_span = x_span / target_ratio
        center_y = (min_y + max_y) / 2
        min_y = center_y - wanted_y_span / 2
        max_y = center_y + wanted_y_span / 2
    else:
        wanted_x_span = y_span * target_ratio
        center_x = (min_x + max_x) / 2
        min_x = center_x - wanted_x_span / 2
        max_x = center_x + wanted_x_span / 2

    return min_x, max_x, min_y, max_y


def tick_values(low: float, high: float, count: int = 5) -> list[float]:
    if count <= 1:
        return [(low + high) / 2]
    step = (high - low) / (count - 1)
    return [low + step * index for index in range(count)]


def format_tick(value: float) -> str:
    return f"{value:.2g}"


def allocate_marker_budgets(levels: list[list[complex]], max_points: int) -> list[int]:
    """Distribute a total SVG marker budget proportionally across levels."""
    max_points = max(max_points, len(levels))
    total_points = sum(len(level) for level in levels)
    if total_points <= max_points:
        return [len(level) for level in levels]

    exact_budgets = [
        max_points * len(level) / total_points
        for level in levels
    ]
    budgets = [max(1, math.floor(budget)) for budget in exact_budgets]

    while sum(budgets) > max_points:
        largest = max(
            (index for index, budget in enumerate(budgets) if budget > 1),
            key=lambda index: budgets[index],
        )
        budgets[largest] -= 1

    remaining = max_points - sum(budgets)
    allocation_order = sorted(
        range(len(levels)),
        key=lambda index: exact_budgets[index] - math.floor(exact_budgets[index]),
        reverse=True,
    )
    for index in allocation_order[:remaining]:
        budgets[index] += 1

    return budgets


def aggregate_roots(
    roots: list[complex],
    marker_budget: int,
    bounds: tuple[float, float, float, float],
    plot_width: float,
    plot_height: float,
) -> list[tuple[complex, int]]:
    """Combine roots in screen-space cells to keep large SVGs responsive."""
    if len(roots) <= marker_budget:
        return [(root, 1) for root in roots]

    min_x, max_x, min_y, max_y = bounds
    aspect_ratio = plot_width / plot_height
    grid_columns = max(1, math.floor(math.sqrt(marker_budget * aspect_ratio)))
    grid_rows = max(1, marker_budget // grid_columns)

    cells: dict[tuple[int, int], list[float]] = defaultdict(
        lambda: [0.0, 0.0, 0.0]
    )
    for root in roots:
        column = min(
            grid_columns - 1,
            math.floor((root.real - min_x) / (max_x - min_x) * grid_columns),
        )
        row = min(
            grid_rows - 1,
            math.floor((root.imag - min_y) / (max_y - min_y) * grid_rows),
        )
        cell = cells[(column, row)]
        cell[0] += root.real
        cell[1] += root.imag
        cell[2] += 1

    return [
        (complex(sum_real / count, sum_imag / count), int(count))
        for sum_real, sum_imag, count in cells.values()
    ]


def plot_levels_svg(
    csv_path: Path,
    levels: list[list[complex]],
    rows_read: int,
    output_path: Path,
    *,
    marker_size: float,
    max_points: int,
) -> None:
    nonempty_levels = nonempty_finite_levels(levels)
    panel_count = len(nonempty_levels)
    columns = min(panel_count, 3)
    rows = math.ceil(panel_count / columns)

    panel_width = 520
    panel_height = 430
    margin_left = 58
    margin_right = 22
    margin_top = 54
    margin_bottom = 52
    plot_width = panel_width - margin_left - margin_right
    plot_height = panel_height - margin_top - margin_bottom
    title_height = 42
    width = panel_width * columns
    height = title_height + panel_height * rows
    bounds = shared_bounds(nonempty_levels, plot_width, plot_height)
    min_x, max_x, min_y, max_y = bounds
    radius = max(1.0, math.sqrt(marker_size) * 0.42)
    total_roots = sum(len(level) for level in nonempty_levels)
    marker_budgets = allocate_marker_budgets(nonempty_levels, max_points)
    aggregated = total_roots > max_points

    def sx(value: float, origin_x: float) -> float:
        return origin_x + margin_left + (value - min_x) / (max_x - min_x) * plot_width

    def sy(value: float, origin_y: float) -> float:
        return origin_y + margin_top + (max_y - value) / (max_y - min_y) * plot_height

    pieces = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="white"/>',
        '<style>text{font-family:Arial,sans-serif;fill:#222}.label{font-size:13px}.tick{font-size:11px;fill:#555}.title{font-size:18px;font-weight:700}.subtitle{font-size:14px;font-weight:700}.grid{stroke:#d7d7d7;stroke-width:1}.axis{stroke:#555;stroke-width:1.3}.frame{fill:none;stroke:#888;stroke-width:1}</style>',
        f'<text class="title" x="{width / 2:.1f}" y="27" text-anchor="middle">'
        f'{html.escape(csv_path.name)}: {rows_read} successful rows'
        f'{" (density view)" if aggregated else ""}</text>',
    ]

    x_ticks = tick_values(min_x, max_x)
    y_ticks = tick_values(min_y, max_y)

    for level_index, roots in enumerate(nonempty_levels, start=1):
        column = (level_index - 1) % columns
        row = (level_index - 1) // columns
        origin_x = column * panel_width
        origin_y = title_height + row * panel_height
        plot_x = origin_x + margin_left
        plot_y = origin_y + margin_top
        color = SVG_COLORS[(level_index - 1) % len(SVG_COLORS)]

        pieces.append(
            f'<text class="subtitle" x="{origin_x + panel_width / 2:.1f}" y="{origin_y + 25:.1f}" text-anchor="middle">'
            f'Level {level_index}</text>'
        )
        pieces.append(
            f'<rect class="frame" x="{plot_x:.1f}" y="{plot_y:.1f}" width="{plot_width:.1f}" height="{plot_height:.1f}"/>'
        )

        for tick in x_ticks:
            x = sx(tick, origin_x)
            pieces.append(f'<line class="grid" x1="{x:.1f}" y1="{plot_y:.1f}" x2="{x:.1f}" y2="{plot_y + plot_height:.1f}"/>')
            pieces.append(f'<text class="tick" x="{x:.1f}" y="{plot_y + plot_height + 18:.1f}" text-anchor="middle">{format_tick(tick)}</text>')

        for tick in y_ticks:
            y = sy(tick, origin_y)
            pieces.append(f'<line class="grid" x1="{plot_x:.1f}" y1="{y:.1f}" x2="{plot_x + plot_width:.1f}" y2="{y:.1f}"/>')
            pieces.append(f'<text class="tick" x="{plot_x - 8:.1f}" y="{y + 4:.1f}" text-anchor="end">{format_tick(tick)}</text>')

        if min_x <= 0 <= max_x:
            x_zero = sx(0, origin_x)
            pieces.append(f'<line class="axis" x1="{x_zero:.1f}" y1="{plot_y:.1f}" x2="{x_zero:.1f}" y2="{plot_y + plot_height:.1f}"/>')
        if min_y <= 0 <= max_y:
            y_zero = sy(0, origin_y)
            pieces.append(f'<line class="axis" x1="{plot_x:.1f}" y1="{y_zero:.1f}" x2="{plot_x + plot_width:.1f}" y2="{y_zero:.1f}"/>')

        pieces.append(f'<text class="label" x="{origin_x + panel_width / 2:.1f}" y="{origin_y + panel_height - 15:.1f}" text-anchor="middle">Re(root)</text>')
        pieces.append(
            f'<text class="label" x="{origin_x + 16:.1f}" y="{origin_y + margin_top + plot_height / 2:.1f}" '
            'text-anchor="middle" transform="rotate(-90 '
            f'{origin_x + 16:.1f} {origin_y + margin_top + plot_height / 2:.1f})">Im(root)</text>'
        )

        rendered_roots = aggregate_roots(
            roots,
            marker_budgets[level_index - 1],
            bounds,
            plot_width,
            plot_height,
        )
        for root, count in rendered_roots:
            density = math.log2(count) if count > 1 else 0.0
            rendered_radius = radius * min(2.5, 1.0 + density * 0.18)
            opacity = min(0.92, 0.55 + density * 0.08)
            pieces.append(
                f'<circle cx="{sx(root.real, origin_x):.2f}" cy="{sy(root.imag, origin_y):.2f}" '
                f'r="{rendered_radius:.2f}" fill="{color}" fill-opacity="{opacity:.2f}"/>'
            )

    pieces.append("</svg>")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text("\n".join(pieces), encoding="utf-8")


def plot_levels_matplotlib(
    csv_path: Path,
    levels: list[list[complex]],
    rows_read: int,
    output_path: Path,
    *,
    marker_size: float,
    show: bool,
) -> None:
    try:
        import matplotlib.pyplot as plt
    except ModuleNotFoundError as exc:
        raise SystemExit(
            "matplotlib is required for PNG/PDF plotting. Install it with:\n"
            "  python3 -m pip install matplotlib\n"
            "Or use the dependency-free SVG output:\n"
            "  python3 visualize_roots.py --all --format svg"
        ) from exc

    nonempty_levels = nonempty_finite_levels(levels)

    panel_count = len(nonempty_levels)
    columns = min(panel_count, 3)
    rows = math.ceil(panel_count / columns)
    fig_width = 5.2 * columns
    fig_height = 4.6 * rows
    fig, axes = plt.subplots(rows, columns, figsize=(fig_width, fig_height), squeeze=False)

    min_x, max_x, min_y, max_y = shared_bounds(nonempty_levels, 1.0, 1.0)

    for level_index, roots in enumerate(nonempty_levels, start=1):
        axis = axes[(level_index - 1) // columns][(level_index - 1) % columns]
        axis.scatter(
            [root.real for root in roots],
            [root.imag for root in roots],
            s=marker_size,
            alpha=0.55,
            linewidths=0,
        )
        axis.axhline(0, color="0.35", linewidth=0.8)
        axis.axvline(0, color="0.35", linewidth=0.8)
        axis.set_xlim(min_x, max_x)
        axis.set_ylim(min_y, max_y)
        axis.set_aspect("equal", adjustable="box")
        axis.grid(True, alpha=0.25)
        axis.set_xlabel("Re(root)")
        axis.set_ylabel("Im(root)")
        axis.set_title(f"Level {level_index}")

    for empty_index in range(panel_count, rows * columns):
        axes[empty_index // columns][empty_index % columns].axis("off")

    fig.suptitle(f"{csv_path.name}: {rows_read} successful rows", fontsize=13)
    fig.tight_layout()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_path, dpi=220)

    if show:
        plt.show()
    else:
        plt.close(fig)


def plot_levels(
    csv_path: Path,
    levels: list[list[complex]],
    rows_read: int,
    output_path: Path,
    *,
    marker_size: float,
    svg_max_points: int,
    show: bool,
) -> None:
    if output_path.suffix.lower() == ".svg":
        plot_levels_svg(
            csv_path,
            levels,
            rows_read,
            output_path,
            marker_size=marker_size,
            max_points=svg_max_points,
        )
        if show:
            print(f"saved SVG plot to {output_path}")
        return

    plot_levels_matplotlib(
        csv_path,
        levels,
        rows_read,
        output_path,
        marker_size=marker_size,
        show=show,
    )


def default_output_path(csv_path: Path, outdir: Path, suffix: str, image_format: str) -> Path:
    safe_stem = csv_path.stem.replace("{", "").replace("}", "").replace(",", "_")
    return outdir / f"{safe_stem}{suffix}.{image_format}"


def discover_csvs() -> list[Path]:
    return sorted(Path.cwd().glob("*.csv"))


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Visualize Mathematica-style Bethe roots stored in CSV files."
    )
    parser.add_argument(
        "csv_files",
        nargs="*",
        type=Path,
        help="CSV files to plot. If omitted, use --all to plot every CSV in the directory.",
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Plot every CSV file in the current directory.",
    )
    parser.add_argument(
        "--outdir",
        type=Path,
        default=Path("plots"),
        help="Directory for generated figures. Default: plots",
    )
    parser.add_argument(
        "--format",
        choices=("png", "pdf", "svg"),
        default="svg",
        help="Output image format. SVG needs no third-party packages. Default: svg",
    )
    parser.add_argument(
        "--row",
        type=int,
        help="Plot only one 1-based data row from each CSV.",
    )
    parser.add_argument(
        "--max-rows",
        type=int,
        help="Plot only the first N successful rows from each CSV.",
    )
    parser.add_argument(
        "--marker-size",
        type=float,
        default=10.0,
        help="Scatter marker size. Default: 10",
    )
    parser.add_argument(
        "--svg-max-points",
        type=int,
        default=50_000,
        help=(
            "Maximum SVG markers before roots are combined into density cells. "
            "Default: 50000"
        ),
    )
    parser.add_argument(
        "--show",
        action="store_true",
        help="Open an interactive plot window after saving.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Parse inputs and print counts without importing matplotlib or writing plots.",
    )
    return parser


def main() -> None:
    args = build_parser().parse_args()
    if args.svg_max_points < 1:
        raise SystemExit("--svg-max-points must be at least 1")

    csv_files = list(args.csv_files)
    if args.all:
        csv_files.extend(discover_csvs())

    csv_files = sorted(dict.fromkeys(csv_files))
    if not csv_files:
        raise SystemExit("No CSV files provided. Use --all or pass one or more CSV paths.")

    suffix = f"_row_{args.row}" if args.row is not None else ""
    for csv_path in csv_files:
        levels, rows_read, skipped_rows = read_root_levels(
            csv_path,
            row_number=args.row,
            max_rows=args.max_rows,
        )
        counts = ", ".join(
            f"level {index}: {len(level)}"
            for index, level in enumerate(levels, start=1)
        )

        if args.dry_run:
            print(
                f"{csv_path}: rows={rows_read}, skipped={skipped_rows}, "
                f"levels={len(levels)}, roots=({counts})"
            )
            continue

        output_path = default_output_path(csv_path, args.outdir, suffix, args.format)
        plot_levels(
            csv_path,
            levels,
            rows_read,
            output_path,
            marker_size=args.marker_size,
            svg_max_points=args.svg_max_points,
            show=args.show,
        )
        print(f"wrote {output_path}")


if __name__ == "__main__":
    main()
