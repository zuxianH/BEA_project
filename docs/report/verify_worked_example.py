#!/usr/bin/env python3
"""Reproduce report Section 8 using SymPy and mpmath, independently of Bertini.

From the repository root:
    python3 docs/report/verify_worked_example.py

Requires sympy and mpmath; reads saved references and writes only to stdout.
The fixed-step calculation illustrates this tableau, not a general path tracker.
"""

import csv
import itertools
from pathlib import Path
import sys

import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from bae_bertini.flip_checks import evacuate_tableau, tableau_to_input_form
from bae_bertini.roots import parse_roots

u, parameter = sp.symbols("u Lambda")
TABLEAU = [[1, 2, 6], [3, 4], [5]]


def casoratian(functions):
    """Centered determinant, expanded without symbolic division pivots."""
    size = len(functions)
    matrix = [
        [sp.expand(f.subs(u, u + sp.I * (sp.Rational(size + 1, 2) - j)))
         for j in range(1, size + 1)]
        for f in functions
    ]
    determinant = 0
    for permutation in itertools.permutations(range(size)):
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(size) for j in range(i + 1, size))
        determinant += (-1) ** inversions * sp.prod(
            matrix[i][permutation[i]] for i in range(size))
    return sp.expand(determinant)


def monic_casoratian(functions):
    polynomial = sp.Poly(casoratian(functions), u)
    return sp.expand(polynomial.as_expr() / polynomial.LC())


def matching_error(left, right):
    assert len(left) == len(right)
    return min(max(abs(a - b) for a, b in zip(left, permutation))
               for permutation in itertools.permutations(right))


def exact_checks():
    radical = sp.sqrt(15)
    elementary = [u**5 - 2*radical*u**4/3 - 7*radical*u**2/3 - 2*radical/3,
                  u**3 + radical*u**2/3 + 2*radical/15, u]
    assert sp.Poly(casoratian(elementary), u).LC() == -16*sp.I
    assert monic_casoratian(elementary) == u**6
    q = {(0, 0): u**6,
         (1, 0): u**3 + radical*u**2/6 + u/4 - radical/40,
         (2, 0): u,
         (0, 1): u**3 - radical*u**2/30 - 5*u/12 - radical/120,
         (1, 1): u + radical/9,
         (0, 2): u - 2*radical/15}
    for node in ((3, 0), (3, 1), (2, 1), (2, 2), (1, 2), (1, 3), (0, 3)):
        q[node] = sp.Integer(1)
    assert monic_casoratian(elementary[1:]) == q[1, 0]
    shape = [3, 2, 1]
    degree = lambda a, s: sum(max(length - s, 0) for length in shape[a:])
    for a, length in enumerate(shape):
        for s in range(length):
            residual = casoratian([q[a, s], q[a+1, s+1]]) - (
                sp.I * (degree(a, s) - degree(a+1, s+1))
                * q[a+1, s] * q[a, s+1])
            assert sp.expand(residual) == 0, (a, s, residual)
    physical = [q[0, 0], q[1, 0], q[2, 0], sp.Integer(1)]
    for level in (1, 2):
        above, current, below = physical[level-1:level+2]
        numerator = (
            above.subs(u, u+sp.I/2) * below.subs(u, u+sp.I/2)
            * current.subs(u, u-sp.I)
            + above.subs(u, u-sp.I/2) * below.subs(u, u-sp.I/2)
            * current.subs(u, u+sp.I))
        assert sp.rem(sp.expand(numerator), current, u, extension=radical) == 0
    assert evacuate_tableau(TABLEAU) == [[1, 2, 4], [3, 6], [5]]
    exact_roots = [[complex(z) for z in sp.nroots(q[1, 0], n=40)], [0j]]
    with (ROOT / "data/references/all_SYT_{3,2,1}.csv").open() as handle:
        saved = {row["Tableau"]: row for row in csv.DictReader(handle)}
    row = saved[tableau_to_input_form(TABLEAU)]
    assert row["SucceededQ"].lower() == "true"
    actual = parse_roots(row["BetheRoots"])
    assert len(actual) == len(exact_roots)
    assert max(matching_error(a, b) for a, b in zip(actual, exact_roots)) < 1e-12
    print("Exact determinant, six QQ cells, two BAE remainders, and saved tableau: PASS")
    return exact_roots


def numerical_growth(tableau, exact_roots):
    # ponytail: Fixed steps cover these two tableaux; use AMP tracking for other shapes.
    mp.mp.dps = 60
    previous = [u**2]
    for site in range(3, 7):
        shape = [sum(entry <= site for entry in row) for row in tableau]
        shape = [length for length in shape if length]
        height = len(shape)
        degrees = [length + height - a - 1 for a, length in enumerate(shape)]
        elementary, groups = [], []
        for a, degree in enumerate(degrees):
            powers = [j for j in range(degree-1, -1, -1) if j not in degrees]
            variables = sp.symbols(" ".join(f"b{a}_{j}" for j in powers), seq=True)
            elementary.append(u**degree + sum(x*u**j for x, j in zip(variables, powers)))
            groups.append(list(variables))
        variables = sum(groups, [])
        q = [monic_casoratian(elementary[a:]) for a in range(height)]
        vacuum_residual = sp.expand(q[0] - u**(site-1)*(u-parameter))
        equations = [vacuum_residual.coeff(u, j) for j in range(site-1, -1, -1)]
        evaluate = sp.lambdify([variables, parameter], equations, "mpmath", cse=True)
        row, column = next((r, c) for r, entries in enumerate(tableau, 1)
                           for c, entry in enumerate(entries, 1) if entry == site)
        targets = []
        for a in range(height):
            old = previous[a] if a < len(previous) else sp.Integer(1)
            if a < row:
                weight = sp.prod(sp.Rational(shape[j-1] + row-column-j,
                                             shape[j-1] + row-column-j+1)
                                 for j in range(1, a+1))
                targets.append(sp.expand(old * (u-weight*parameter)))
            else:
                targets.append(old)
        # Invert nested minors from the last row upwards to prepare a seed.
        seed = {}
        for a in range(height-1, -1, -1):
            difference = (q[a]-targets[a]).subs(parameter, 30).subs(seed)
            matrix, rhs = sp.linear_eq_to_matrix(sp.Poly(difference, u).all_coeffs(), groups[a])
            keep = [i for i in range(matrix.rows)
                    if any(matrix[i, j] != 0 for j in range(matrix.cols))]
            matrix, rhs = matrix[keep, :], rhs[keep, :]
            matrix = mp.matrix([[mp.mpf(str(sp.N(x, 65))) for x in entries]
                                for entries in matrix.tolist()])
            rhs = mp.matrix([mp.mpf(str(sp.N(x, 65))) for x in rhs])
            values, _ = mp.qr_solve(matrix, rhs)
            seed.update({x: sp.Float(str(value), 65) for x, value in zip(groups[a], values)})
        point = tuple(mp.mpf(str(seed[x])) for x in variables)
        point = mp.findroot(lambda *x: evaluate(x, 30), point, tol=mp.mpf("1e-50"), maxsteps=60)
        for step in range(1, 601):
            value = mp.mpf(30) * (600-step) / 600
            point = mp.findroot(lambda *x: evaluate(x, value), tuple(point),
                                tol=mp.mpf("1e-50"), maxsteps=40)
        residual = max(abs(value) for value in evaluate(point, 0))
        assert residual < mp.mpf("2e-50"), (site, residual)
        substitution = dict(zip(variables, [sp.Float(str(x), 60) for x in point]))
        previous = [sp.Poly(poly.subs(substitution), u).as_expr() for poly in q]
        roots = [[complex(z) for z in sp.nroots(poly, n=30, maxsteps=300)]
                 for poly in previous[1:]]
        print(f"n={site}, shape={shape}, roots={roots}, residual={mp.nstr(residual, 5)}")
    assert len(roots) == len(exact_roots)
    assert max(matching_error(a, b) for a, b in zip(roots, exact_roots)) < 1e-12
    print("Sequential branch agrees with the exact six-box solution: PASS")


if __name__ == "__main__":
    roots = exact_checks()
    numerical_growth(TABLEAU, roots)
    print("Independent continuation of the evacuated tableau:")
    numerical_growth(evacuate_tableau(TABLEAU), [[-z for z in level] for level in roots])
