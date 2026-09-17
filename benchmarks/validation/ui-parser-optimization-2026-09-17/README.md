# Parser and interface optimization validation

This pass changes literal extraction in the Python expression parser, removes
unused evaluation-history collection from `MyFindRoot`, and stops the Streamlit
live-log timer when no calculation is running. Log and CSV downloads are prepared
on request and reused within the browser session until file metadata changes.
Numerical precision, goals, tolerances, predictors, and step sizes are unchanged.
The parser and refinement edits also apply to the nested sharing copy.

## Parser benchmark

The input `data/initial_data_70.csv` contains 18 equations and 55,218 expression
characters. At 100-digit Bertini precision, seven interleaved measurements of
`load_problem` gave these medians:

| Implementation | Seconds |
| --- | ---: |
| Original literal extraction | 0.278872 |
| UTF-8 lines encoded once | 0.042230 |

This is a **6.60× speedup for loading this problem**, not an end-to-end solver
speedup. Loading includes CSV reading, expression conversion, system construction,
and initial-point construction. Both implementations returned identical variable
names, initial-point representations, and system evaluation representations at
the initial point for path parameter values 0, 0.5, and 1.

Raw measurements are in `parser-benchmark.json`. Reproduce from the project root:

```bash
.venv/bin/python validation/ui-parser-optimization-2026-09-17/benchmark_parser.py
```

`parser_before.py` preserves the former parser solely for this benchmark.

## Validation

- All 31 Python regression tests passed, including exact decimal extraction,
  Unicode byte offsets, LF/CRLF/CR line endings, very large/small literals,
  download reuse/invalidation, and run/stop interactions.
- `tests/test_precision.wl` and `tests/test_asymptotic_start.wl` passed.
- One representative tableau from each of `{3,2,1}` and `{4,2,1}` passed the
  numerical reference comparison, using one-to-one matching within each level
  at tolerance `1e-8`. Maximum differences were `4.69175e-17` and `1.37342e-14`.
  Reference SHA-256 checksums were unchanged. Successful results and settings
  are in `numerical-unrestricted/summary.json` and
  `numerical-421-unrestricted/summary.json`.
- Initial restricted-environment numerical runs failed before completing their
  first stage; an isolated copy of the original code failed the same way.
  Rerunning the revised code outside that restriction passed both references.
  The failed attempts are retained in the other `numerical*` directories for
  traceability.

Root agreement with stored references is not a certification of 100-digit root
accuracy. Persistent workers, symbolic/prefix caching, database-backed results,
streamed downloads, and numerical parameter tuning were not implemented in this
pass. Prepared downloads still occupy memory while retained in the session.

Streamlit behavior follows its official [fragment documentation](https://docs.streamlit.io/develop/api-reference/execution-flow/st.fragment)
and [download documentation](https://docs.streamlit.io/develop/api-reference/widgets/st.download_button).
