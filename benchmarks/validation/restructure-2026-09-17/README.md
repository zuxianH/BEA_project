# Repository reorganization validation

The maintained implementations now live under `src/bae_bertini/`, `wolfram/`,
and `scripts/`. Legacy command/import paths forward to these implementations.
Data and runtime directories were relocated with compatibility links; the old
sharing copy and ZIP were archived intact. No equation, precision, predictor,
tracking tolerance, or solver iteration setting was changed in this refactor.

Validation completed:

- All 33 Python tests passed, including module-identity checks for old imports,
  batch/resume behavior, process-group cancellation, and Streamlit interactions.
- An independently extracted source bundle passed Python and shell command checks
  from a different working directory whose path included spaces. Every bundled
  file other than the manifest itself is covered by its SHA-256 manifest.
- Wolfram precision, asymptotic-start, and path-resolution checks passed. The path
  test ran from `/tmp` and checked both compatibility and canonical workflow loads.
- The `{3,2,1}` reference run in the reorganized checkout passed with maximum
  one-to-one root difference `4.69175e-17` at tolerance `1e-8`.
- The `{4,2,1}` reference run from an extracted distribution under `/tmp` passed
  with maximum root difference `1.37342e-14`. Its `.venv` linked to the installed
  interpreter/dependencies; runtime Python and Wolfram sources came from the
  extracted bundle. Records are in `numerical-relocated-421/summary.json`.
- All 17 retained reference CSV/TXT files matched their pre-move checksums in
  `docs/reference-checksums.json`, including the large local reference dataset.
- Headless Chrome rendered the Streamlit result chart and comparison overlay with
  two traces, no page errors, and no Streamlit exceptions.
- Shell syntax checks, Python dependency checks, and Git whitespace checks passed.

These representative numerical runs establish agreement at the stated tolerance;
they are not a full reference sweep. Sandbox stream restrictions delayed one
Wolfram path check; the check was also run successfully outside the sandbox.

See `docs/repository-layout.md` for the file mapping and the three differences
reconciled between the root source and the retired sharing copy.
