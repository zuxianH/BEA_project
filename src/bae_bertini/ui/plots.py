"""Interactive root plots; the source CSV retains its full precision."""
import math

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
    figure.update_layout(
        template='plotly_white', height=510, margin=dict(l=20, r=20, t=30, b=20),
        xaxis_title='Real part', yaxis_title='Imaginary part',
        legend=dict(orientation='h', y=1.12), uirevision=revision,
    )
    figure.update_xaxes(zeroline=True, zerolinecolor='#94a3b8', constrain='domain')
    figure.update_yaxes(zeroline=True, zerolinecolor='#94a3b8', scaleanchor='x', scaleratio=1)
    return figure, omitted
