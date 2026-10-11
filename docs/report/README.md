# Technical report

[BAE_Bertini_Report.pdf](BAE_Bertini_Report.pdf) is the compiled report;
[BAE_Bertini_Report.tex](BAE_Bertini_Report.tex) is its editable source.

Sections 2–6 develop the conventions, degree and normalization formulas,
Wronskian gauges, marked points, asymptotic starts, rigged configurations,
and numerical continuation. Section 7 is the `(2,1)` warm-up. Section 8
solves the tableau `{{1,2,6},{3,4},{5}}` of shape `(3,2,1)`, including every
vacuum coefficient equation, growth step, exact endpoint polynomial,
QQ cell, cubic root, and evacuation check. All six figures are native TikZ.

Build from the repository root with a TeX installation containing TikZ:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/bae-report-build docs/report/BAE_Bertini_Report.tex
cp /tmp/bae-report-build/BAE_Bertini_Report.pdf docs/report/BAE_Bertini_Report.pdf
```

The independent example check uses SymPy and mpmath. These are optional
report verification tools, not new dependencies of the production solver.
For an isolated environment:

```bash
python3 -m venv /tmp/bae-report-check
/tmp/bae-report-check/bin/python -m pip install sympy mpmath
/tmp/bae-report-check/bin/python docs/report/verify_worked_example.py
```

The script checks the exact determinant, all six QQ cells, two polynomial
BAE remainders, and the saved roots for the selected tableau. It then
reproduces both that tableau's and its evacuated partner's growth using
60-digit Newton correction, starting each nontrivial step at `Lambda=30`
and decreasing by `0.05`. It asserts endpoint residuals below `2e-50` and
agreement of final roots with the exact polynomials within `1e-12`.
It writes only to stdout and leaves saved reference files unchanged.

This fixed-step calculation is an illustrative independent check of these
two examples. The production continuation still uses Wolfram/Bertini.
Saved-reference comparisons and independently calculated results are
identified separately in the report; the checked reference CSV does not
contain the evacuated partner.
