"""Interactive root plots; the source CSV retains its full precision."""
import csv
import math
from pathlib import Path

import plotly.graph_objects as go

from bae_bertini.roots import parse_roots

COLORS = ('#2563eb', '#e45756', '#059669', '#8b5cf6', '#d97706', '#0891b2')


def root_figure(roots, comparison=None, negate=False, revision=None):
    figure = go.Figure()
    omitted = 0
    datasets = [(roots, '−A' if negate else 'A', -1 if negate else 1, 'circle')]
    if comparison is not None:
        datasets.append((comparison, 'B', 1, 'x'))
    for text, name, sign, symbol in datasets:
        for index, level in enumerate(parse_roots(text)):
            finite = [sign * z for z in level if math.isfinite(z.real) and math.isfinite(z.imag)]
            omitted += len(level) - len(finite)
            if not finite:
                continue
            figure.add_trace(go.Scatter(
                x=[z.real for z in finite], y=[z.imag for z in finite], mode='markers',
                name=f'{name} · Level {index + 1}',
                marker=dict(size=10, symbol=symbol, color=COLORS[index % len(COLORS)]),
                hovertemplate='Re: %{x:.12g}<br>Im: %{y:.12g}<extra>%{fullData.name}</extra>',
            ))
    format_root_figure(figure, revision)
    return figure, omitted


def all_roots_figure(path, revision=None):
    """Stream every CSV row and group finite roots by level, retaining tableau labels."""
    levels = {}
    counts = dict(total=0, plotted=0, failed=0, invalid=0, omitted=0)
    with Path(path).open(newline='', encoding='utf-8-sig') as stream:
        for row_number, row in enumerate(csv.DictReader(stream), 1):
            counts['total'] += 1
            if row.get('SucceededQ', '').strip().lower() not in {'true', '1', 'yes'}:
                counts['failed'] += 1
                continue
            try:
                parsed = parse_roots(row.get('BetheRoots', ''))
            except (ValueError, TypeError, OverflowError):
                counts['invalid'] += 1
                continue
            has_roots = False
            for index, level in enumerate(parsed):
                for z in level:
                    if not (math.isfinite(z.real) and math.isfinite(z.imag)):
                        counts['omitted'] += 1
                        continue
                    x, y, labels = levels.setdefault(index, ([], [], []))
                    x.append(z.real)
                    y.append(z.imag)
                    labels.append([row.get('Tableau', '(no tableau)'), row_number])
                    has_roots = True
            counts['plotted' if has_roots else 'invalid'] += 1
    figure = go.Figure()
    for index, (x, y, labels) in sorted(levels.items()):
        figure.add_trace(go.Scattergl(
            x=x, y=y, customdata=labels, mode='markers', name=f'Level {index + 1}',
            marker=dict(size=8, opacity=0.7, color=COLORS[index % len(COLORS)]),
            hovertemplate='Tableau: %{customdata[0]}<br>CSV row: %{customdata[1]}'
                          '<br>Re: %{x:.12g}<br>Im: %{y:.12g}<extra>%{fullData.name}</extra>',
        ))
    format_root_figure(figure, revision)
    return figure, counts


def format_root_figure(figure, revision):
    figure.update_layout(
        template='plotly_white', height=510, margin=dict(l=20, r=20, t=30, b=20),
        xaxis_title='Real part', yaxis_title='Imaginary part',
        legend=dict(orientation='h', y=1.12), uirevision=revision,
    )
    figure.update_xaxes(zeroline=True, zerolinecolor='#94a3b8', constrain='domain')
    figure.update_yaxes(zeroline=True, zerolinecolor='#94a3b8', scaleanchor='x', scaleratio=1)
