# Bertini Bethe Continuation

Compute Bethe roots with the Wolfram SUSY Wronskian workflow and the Python/Bertini
continuation backend. Run calculations in the Streamlit interface or from the
command line.

## Start the interface

From this checkout, using the existing project environment:

```bash
.venv/bin/python -m pip install -e '.[ui]'
python3 scripts/start_studio.py
```

Open <http://localhost:8501>. The interface provides single-tableau calculations,
Young-diagram and list-file batches, flip checks, live logs, cancellation, and
interactive Plotly root comparisons. Existing saved settings are reused.

For a new environment:

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[ui,solver]'
```

Calculations also require Mathematica's `WolframKernel` on `PATH`. Set
`WOLFRAM_KERNEL` to select another executable. Viewing saved results does not
require a Wolfram kernel. Install `.[notebooks]` for notebook dependencies.

## Repository map

| Location | Purpose |
| --- | --- |
| `src/bae_bertini/` | Maintained Python implementation: settings, jobs, continuation, result tools, UI |
| `wolfram/` | Maintained Wolfram entry points, solver, and utilities |
| `scripts/` | Batch execution, crosschecks, and distribution builder |
| `examples/` | Small continuation inputs and demonstration code |
| `data/tableaux/` | Tableau lists and their generation caches |
| `data/references/` | Retained reference result datasets |
| `notebooks/` | Exploratory analysis notebooks |
| `tests/` | Python and Wolfram regression checks |
| `benchmarks/validation/` | Timing reports and numerical validation evidence |
| `docs/` | Command reference, tutorials, repository guide, research report |
| `workspace/` | Local results, run directories, logs, settings, and archives; ignored by Git |
| `dist/` | Generated sharing bundles; ignored by Git |

The root contains only this README, package configuration, and the Streamlit entry
point. Edit Python under `src/`, Wolfram code under `wolfram/`, and launch scripts
under `scripts/`. See [the repository guide](docs/repository-layout.md) for the
migration map. Retired wrappers and duplicate copies are preserved locally in
`workspace/archives/`.

## Run calculations

```bash
# A single tableau; canonical Wolfram entry point
WolframKernel -noprompt -script wolfram/RunSingle.wl '{{1,3},{2}}'

# Preview a batch, then remove --dry-run to execute it
bash scripts/submit_run_single_jobs.sh --yd '{4,2,1}' -j 2 --dry-run

# Compare a tableau with its flip
bash scripts/crosscheck.sh '{{1,3},{2}}'

# Inspect saved reference results
.venv/bin/python -m bae_bertini.flip_checks 'data/references/all_SYT_{3,2,1}.csv'
```

Use the commands above; the old root-level launchers and directory links have
been retired. Shell helpers resolve paths from the checkout rather than the
caller's working directory.

New command-line runs write to `workspace/results/`; new UI configurations use
`workspace/results/studio/`. Explicit `BERTINI_RESULT_SYT_DIR` destinations and
saved UI settings are preserved. **Open reference results** in the UI opens
`data/references/`. Older saved UI paths are translated to their new locations automatically.

The interface refreshes live status once per second during a run and stops polling
when idle. Use **Refresh run status** to pick up a run started from another tab.
Jobs continue while the server remains running. CSV previews load the first 500
rows; downloads retain the full file and precision text. Prepared downloads use
session memory and are reused until the file changes.

See [the command and numerical-settings reference](docs/usage.md) for precision,
continuation parameters, partitioning, resume behavior, and output formats.
Numerical settings and algorithms were not changed by the directory reorganization.

## Checks

```bash
.venv/bin/python -m unittest discover -s tests -v
WolframKernel -noprompt -script tests/test_precision.wl
WolframKernel -noprompt -script tests/test_asymptotic_start.wl
WolframKernel -noprompt -script tests/test_paths.wl
.venv/bin/python tests/validate_reference_results.py --limit 1 --jobs 1 \
  --output-dir workspace/validation/example 'data/references/all_SYT_{3,2,1}.csv'
```

Use a fresh output directory for numerical validation. Reference checks compare
roots one-to-one within each nesting level and preserve reference file hashes.

## Share the project

```bash
python3 scripts/build_distribution.py
```

This creates `dist/BAE_Bertini.zip` from the maintained source tree, including a
SHA-256 manifest, example inputs, tableau lists, and two small reference datasets.
It excludes the environment, run state, local archives, and large result datasets.
Extract it, create `.venv`, and install with the same editable-install command above.
There is no second source tree to maintain manually.
