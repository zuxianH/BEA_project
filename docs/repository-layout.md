# Repository layout and migration

The maintained source trees are `src/bae_bertini/`, `wolfram/`, and `scripts/`.
The reorganization preserves numerical behavior and data. Commands use the
maintained locations below; root-level compatibility wrappers have been retired.

## Python responsibilities

| Module | Responsibility |
| --- | --- |
| `paths.py` | Root, source, reference-data, interpreter, and local workspace paths |
| `config.py` | Validated inputs, defaults, command construction, saved settings |
| `jobs.py` | Process groups, cancellation, bounded logs, server-owned job lifecycle |
| `continuation.py` | Bertini expression construction and continuation |
| `results.py` | Atomic result merging, locking, and bounded CSV previews |
| `flip_checks.py` | Decimal evacuation/flip checks for aggregate CSVs |
| `crosscheck.py` | Comparison of an independently calculated tableau/flip pair |
| `roots.py` | Display root parsing and existing standalone plotting/export tools |
| `ui/app.py`, `ui/plots.py` | Streamlit controls and Plotly visualization |
| `launcher.py` | Start the local Streamlit server |

Display parsing and high-precision validation remain distinct; this refactor did
not change the numerical comparison algorithms. Libraries never import code from
result folders or legacy UI packages.

`pyproject.toml` defines the editable Python package and optional UI, solver, and
notebook dependencies. Use `pip install -e '.[ui,solver]'` from the full checkout.
The Wolfram code and runtime scripts remain repository resources, so deployment
uses the full source bundle rather than a standalone Python wheel. Python, shell,
and Wolfram resolve paths from their own source locations. `BAE_BERTINI_ROOT` can
explicitly select a full checkout when needed; normally leave it unset.

## Migration map

| Previous location | Maintained location |
| --- | --- |
| `continue_lambda0_to_zero.py` | `src/bae_bertini/continuation.py` |
| `merge_syt_results.py` | `src/bae_bertini/results.py` |
| `check_flip_distances_fast.py` | `src/bae_bertini/flip_checks.py` |
| `crosscheck_compare.py` | `src/bae_bertini/crosscheck.py` |
| `desktop/core.py` | `src/bae_bertini/config.py`, `jobs.py`, `results.py` |
| `studio/runtime.py`, `studio/plots.py` | `src/bae_bertini/jobs.py`, `ui/plots.py` |
| Root `*.wl`, `solver/`, `utils/` | `wolfram/` and its subdirectories |
| Root shell launchers | `scripts/` |
| `Result_SYT/` | `data/references/` |
| `Result_SYT_desktop/` | `workspace/results/desktop/` |
| `Result_SYT_studio/` | `workspace/results/studio/` |
| `.runs/`, `logs/`, `.desktop-state/` | `workspace/runs/`, `workspace/logs/`, `workspace/state/` |
| `my_SYT/` | `data/tableaux/` |
| `data/*.csv` example inputs | `examples/continuation/` |
| `data/*_solution.csv` generated endpoints | `workspace/results/continuation/` |
| `validation/` | `benchmarks/validation/` |
| `report/` | `docs/report/` |
| `plot_bethe_roots.ipynb` | `notebooks/plot_bethe_roots.ipynb` |
| Tutorial and demonstration | `docs/homotopy-continuation.md`, `examples/` |

Retired source wrappers and duplicate packages are preserved in
`workspace/archives/legacy-layout-2026-09-17/`. The old root and `data/*.csv`
symlinks have been removed; their targets remain intact and `removed-links.json`
in that archive records each mapping. Reference folders now contain data only.
Saved UI input/output paths are translated to their current locations, without
changing numerical settings. External paths remain unchanged.

Start the interface with `python3 scripts/start_studio.py` (or the installed
`bertini-studio` command). Use `python -m bae_bertini.continuation`,
`python -m bae_bertini.results`, and `python -m bae_bertini.flip_checks` for the
Python tools, using the project environment after editable installation.
The Wolfram backend invokes `scripts/continue_lambda0_to_zero.py`, which bootstraps
the source package even in an extracted checkout. The only root Python file is
`streamlit_app.py`, the standard Streamlit entry point.

The notebook resolves inputs through `bae_bertini.paths.REFERENCES`.
Historical notebook outputs and validation reports retain their original paths
and dataset names. Select the desired CSV when opening a historical notebook in
a new checkout; not every historical selection is included in the sharing ZIP.

## Reconciliation of the nested sharing copy

Every file in the former nested `BAE_Bertini/` directory was compared with the
root copy before moving it. The only differing files were:

- `README.md`: sharing-specific documentation; superseded by generated-bundle docs.
- `run.sh`: the nested copy requested eight Newton iterations; the current root
  example requests four. The current root example is retained without changes
  to its numerical settings.
- `solver/NumericalWBE_SUSY.m`: the nested copy lacked the existing exact-start and
  failed-minimizer handling. The tested root implementation is authoritative.

`PACKAGE_MANIFEST.md` was unique to the sharing copy. All old files, including
these variants and duplicated datasets, remain intact locally under
`workspace/archives/sharing-copy-before-restructure/`. The original ZIP and the
unused `NumericalWBE_SUSY (Copy).m` are also preserved under `workspace/archives/`.
No archive contents or reference data were deleted. `reference-checksums.json`
records the pre-move SHA-256 values for all retained reference CSV/TXT files.

The obsolete nested pointer folder has also been archived. Generate a
fresh bundle with `python3 scripts/build_distribution.py`; do not edit archived
source copies. The distribution intentionally includes only the `{3,2,1}` and
`{4,2,1}` reference datasets, not the full local result collection.

## Git and generated files

`workspace/`, `dist/`, environments, caches, and the large `{5,4,3,2,1}` reference
CSV are ignored. Small reference data, source code, tests, and curated benchmark
reports remain available to version control. The many deleted old paths and added
new paths in the current diff represent moves and retired wrappers; no commit
or history rewrite was performed.
