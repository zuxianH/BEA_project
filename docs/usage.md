> Commands below use the maintained `src/`, `wolfram/`, and `scripts/` trees.
> Generated files belong in `workspace/`. See [repository layout](repository-layout.md).

# Bertini Bethe Continuation Jobs

## Streamlit / Plotly interface

Launch **Bertini Calculation Studio** in your browser:

```bash
.venv/bin/python -m pip install -e '.[ui]'
python3 scripts/start_studio.py
```

Open <http://localhost:8501> if a browser does not open automatically. The launcher
binds to `127.0.0.1`. You can also start it directly:

```bash
.venv/bin/python -m streamlit run streamlit_app.py --server.address=127.0.0.1
```

The sidebar provides single-tableau runs, batches by Young diagram or uploaded
list file, tableau/flip comparisons, and checks of saved aggregate CSVs. Edit
numerical settings directly, then click **Run calculation**. **Run details** shows
the validated command before execution. **Live calculation** refreshes the log
and status every second during a run, then stops polling. **Refresh run status**
connects an idle tab to a run started in another tab. **Stop calculation**
terminates the process group. Full log downloads are prepared on request.

In **Results & roots**, choose a folder, CSV, and tableau. **Open reference
results** opens the existing `data/references/` dataset. Plotly supports zoom, pan,
hover coordinates, level toggles, and SVG export from its toolbar. Enable
**Compare with another result** to overlay two rows, optionally as −A versus B.
The plot uses floating-point display values; **Full precision row** preserves
the original CSV text. Previews load at most 500 rows. Full CSV downloads are
prepared only on request because some aggregate files are large; prepared files
are reused across interactions until the file changes. Use **Refresh
results** to see newly completed files during a batch.

New installations write calculations to `workspace/results/studio/`. Existing saved
settings are stored in `workspace/state/`; older saved paths are migrated
automatically. Uploaded inputs
are stored there as well. One active calculation is shared across browser tabs
on the same server. Jobs survive page refreshes and closing the browser while
the server remains running; reconnect to monitor or stop them. Stop an active
calculation before shutting down the server. Completed outputs and pending batch
snapshots are retained after cancellation.

The interface requires Streamlit and Plotly, with no GTK, PyGObject, or Cairo
dependency. Calculations still use Mathematica's `WolframKernel` and the project's
`.venv` with Bertini. Browsing results and checking saved flips need no solver
startup. The application shortcut starts `scripts/start_studio.py`.
The shortcut template in `scripts/` contains this checkout's absolute path and
must be updated if moved. Generated sharing bundles include the interface.

Interface and job checks:

```bash
.venv/bin/python -m unittest discover -s tests -p 'test_*studio*.py' -v
.venv/bin/python -m unittest discover -s tests -p test_jobs.py -v
```

Implementation references: [Streamlit fragments](https://docs.streamlit.io/develop/api-reference/execution-flow/st.fragment)
for live updates and [Plotly axes](https://plotly.com/python/axes/) for equal-scale complex-plane plots.

This folder runs the Mathematica Bethe workflow, but uses Python/Bertini for
homotopy continuation. There is no Julia fallback in `wolfram/RunSingle.wl`; the backend
is the local script `scripts/continue_lambda0_to_zero.py`.

## Precision and batch output

Bertini coefficients are imported as decimal text and converted directly to the
requested Mathematica working precision. The real-coefficient export rejects
non-finite values and imaginary parts larger than
`tracking_tolerance * max(1, abs(real_part))`. Tracker failures do not publish a
new solution CSV. Output CSVs are published by an atomic rename.

Batch jobs save individual snapshots immediately. The launcher consolidates them
after 100 completion waits or 60 seconds at a completion, and always at the end.
Set `RESULT_MERGE_EVERY` or `RESULT_MERGE_INTERVAL` to change these defaults;
`RESULT_MERGE_EVERY=1` requests consolidation after each completion wait.
Pending snapshots remain available for resuming an interrupted batch.
`bae_bertini.results` uses a POSIX file lock that releases when the merger exits.
Its `.flock` file is intentionally retained and should not be deleted during runs.

The Bertini path skips exported symbolic Jacobians, duplicate Q-system setup,
muted diagnostic calculations, and polling after the subprocess has exited.
Tracker precision, predictor, and step-size defaults are unchanged.

## Regression checks

From the repository root:

```bash
.venv/bin/python -m unittest discover -s tests -v
WolframKernel -noprompt -script tests/test_precision.wl
WolframKernel -noprompt -script tests/test_asymptotic_start.wl
python3 tests/validate_reference_results.py --limit 1 --jobs 1 \
  --output-dir /tmp/bertini-check-321 'data/references/all_SYT_{3,2,1}.csv'
python3 tests/validate_reference_results.py --limit 1 --jobs 1 \
  --output-dir /tmp/bertini-check-421 'data/references/all_SYT_{4,2,1}.csv'
```

Choose fresh output directories. The numerical checks keep reference CSVs intact
and compare roots one-to-one within each nesting level at tolerance `1e-8`.
Generated sharing bundles include runtime sources and tests; historical validation
reports remain in `benchmarks/validation/`.

## Requirements

- Python 3 with `venv`
- `wolframscript` available on `PATH`
- A shell such as `bash`

## Install Python/Bertini

From this folder:

```bash
cd /path/to/BAE_Bertini

python3 -m venv .venv
.venv/bin/python -m pip install --upgrade pip
.venv/bin/python -m pip install -e '.[ui,solver,notebooks]'
```

Check that Bertini imports:

```bash
.venv/bin/python -c "import bertini; print('bertini import ok')"
```

The local tested setup uses `bertini2` and imports it in Python as `bertini`.

## Important Files

- `wolfram/RunSingle.wl`: main entry point for one SYT job.
- `scripts/continue_lambda0_to_zero.py`: Python/Bertini path tracker used by `wolfram/RunSingle.wl`.
- `scripts/run.sh`: example high-precision job command.
- `data/references/`: reference result directory; new jobs default to `workspace/results/`.
- `workspace/runs/`: intermediate continuation input and output CSV files.
- `workspace/runs/`: per-run logs and backend outputs.
- `notebooks/plot_bethe_roots.ipynb`: notebook for plotting `BetheRoots` and comparing `-r1` with `r2`.

## Run One SYT Job

Basic command:

```bash
wolframscript -file wolfram/RunSingle.wl '{{1,3,7},{2,5},{4,6}}'
```

For your current example:

```bash
wolframscript -file wolfram/RunSingle.wl '{{1, 2, 3, 4, 5, 10, 11, 12}, {6, 7, 8, 9, 13, 14, 15, 16}}'
```

The plain command uses these defaults:

```text
InitialLambda = 70
TargetLambda = 0
WorkingPrecision = 40
Bertini tracking tolerance = 1e-8
Bertini default precision = Automatic
Bertini max precision = Automatic
Bertini predictor = Automatic
```

## Recommended Safer Settings

For larger tableaux, use a larger starting `lambda0` and higher precision. This
was the setting that fixed the sign-flip branch mismatch in the tested pair:

```bash
BERTINI_INITIAL_LAMBDA=5070 \
BERTINI_WORKING_PRECISION=80 \
BERTINI_DEFAULT_PRECISION=80 \
BERTINI_TRACKING_TOLERANCE=1e-10 \
BERTINI_MAX_PRECISION=1200 \
BERTINI_MAX_NUM_STEPS=300000 \
BERTINI_PREDICTOR=RKCashKarp45 \
wolframscript -file wolfram/RunSingle.wl '{{1, 2, 3, 4, 5, 10, 11, 12}, {6, 7, 8, 9, 13, 14, 15, 16}}'
```

Or run the example script:

```bash
bash scripts/run.sh
```

To keep high-precision results separate:

```bash
BERTINI_RESULT_SYT_DIR=workspace/results/lambda5070 \
BERTINI_INITIAL_LAMBDA=5070 \
BERTINI_WORKING_PRECISION=80 \
BERTINI_DEFAULT_PRECISION=80 \
BERTINI_TRACKING_TOLERANCE=1e-10 \
BERTINI_MAX_PRECISION=1200 \
BERTINI_MAX_NUM_STEPS=300000 \
BERTINI_PREDICTOR=RKCashKarp45 \
wolframscript -file wolfram/RunSingle.wl '{{1,3,4,5,7,10,11,13},{2,6,8,9,12,14,15,16}}'
```

## Run Multiple SYT Jobs

`scripts/submit_run_single_jobs.sh` launches several independent `wolfram/RunSingle.wl` jobs
with a configurable local concurrency limit. It uses the recommended Bertini
settings (`lambda0 = 5070`, precision `80`, tolerance `1e-10`) by default.
Batch jobs keep only the aggregate `all_SYT_<young-diagram>.csv` in the result
directory. Per-job CSVs are staged under `workspace/runs/batch-results`, merged, and
removed automatically. The aggregate CSV is updated atomically after each
completed SYT job, so finished solutions are visible while the batch is still
running.

Generate the SYT list for a Young diagram and run at most eight jobs at once:

```bash
bash scripts/submit_run_single_jobs.sh --yd '{4,3,2,1}' -j 8
```

Use an existing list with one Mathematica-form SYT per line:

```bash
bash scripts/submit_run_single_jobs.sh --list 'data/tableaux/{4,3,2,1}.txt' -j 8
```

Preview commands without starting jobs:

```bash
bash scripts/submit_run_single_jobs.sh --yd '{4,3,2,1}' -j 8 --dry-run
```

For partitioned runs, append the partition number to the Young diagram or use
`--part`. This example runs partition 1 of 9:

```bash
bash scripts/submit_run_single_jobs.sh --yd '{5,4,3,2,1}_1' -n 9 -j 100
```

The launcher skips previously successful and failed tableaux by default. Use
`--rerun-existing` to run them again. Use `--cleanup-runs` to remove successful
`workspace/runs/syt-*` work directories after their final CSV has been saved.

It creates these index files in the selected result directory:

```text
all_SYT_<young-diagram>.csv
fail_<young-diagram>.txt
```

If SYT generation is interrupted, the launcher records the lock owner and
automatically removes a lock whose local owner process is no longer running.
Locks created on another host are reclaimed after six hours by default; set
`SYT_LOCK_STALE_SECONDS` to change that interval.

## Runtime Settings

`wolfram/RunSingle.wl` reads these environment variables:

| Variable | Meaning | Default |
| --- | --- | --- |
| `BERTINI_INITIAL_LAMBDA` | Starting `lambda0` value | `70` |
| `BERTINI_TARGET_LAMBDA` | Target `lambda0` value | `0` |
| `BERTINI_WORKING_PRECISION` | Mathematica working precision for generated data | `40` |
| `BERTINI_TRACKING_TOLERANCE` | Bertini tracker tolerance | `1e-8` |
| `BERTINI_INFINITE_TOLERANCE` | Bertini infinite endpoint tolerance | `1e8` |
| `BERTINI_DEFAULT_PRECISION` | Bertini default multiprecision digits | not passed |
| `BERTINI_MAX_PRECISION` | AMPTracker maximum precision digits | not passed |
| `BERTINI_MAX_NUM_STEPS` | Maximum path-tracking steps | not passed |
| `BERTINI_INITIAL_STEP_SIZE` | Initial path step size, for example `1/100` | not passed |
| `BERTINI_PREDICTOR` | Predictor, for example `RKCashKarp45` | not passed |
| `BERTINI_RESULT_SYT_DIR` | Directory for final SYT CSVs | `workspace/results` |
| `BERTINI_TIMEOUT` | Backend timeout in seconds | `900` |

## Outputs

Each successful job writes a final CSV in the result directory. For example:

```text
workspace/results/{{1, 2, 3, 4, 5, 10, 11, 12}, {6, 7, 8, 9, 13, 14, 15, 16}}.csv
```

Useful columns include:

- `SucceededQ`: whether the workflow succeeded.
- `Tableau`: the SYT that was run.
- `BetheRoots`: the final roots.
- timing and diagnostic columns from the Mathematica workflow.

If a job fails, check the newest directory under `workspace/runs/` for backend stdout,
stderr, timing files, and the intermediate CSV passed to Bertini.

## Direct CSV Continuation

You can also call the Python Bertini driver directly on a CSV. The input CSV
must contain the columns used by this project, especially:

- `var`
- `Initialvar`
- `expression`
- `lambda0`

Example:

```bash
.venv/bin/python -m bae_bertini.continuation examples/continuation/initial_data_5070.csv \
  --target 0 \
  --default-precision 80 \
  --tracking-tolerance 1e-10 \
  --max-precision 1200 \
  --max-num-steps 300000 \
  --predictor RKCashKarp45
```

To write the old Julia-compatible output format:

```bash
.venv/bin/python -m bae_bertini.continuation examples/continuation/initial_data_5070.csv \
  --legacy-output \
  --output /tmp/bertini_solution.csv \
  --timing-file /tmp/bertini_timing.csv
```

## Plot Bethe Roots

Open `notebooks/plot_bethe_roots.ipynb` with the `.venv` kernel. It can:

- parse Mathematica-style complex numbers from the `BetheRoots` column;
- plot one SYT result CSV;
- compare two CSVs in the style of Mathematica `ComplexListPlot[{-r1, r2}]`.

For sign-flip checks, set:

```python
path_r1 = Path('workspace/results/lambda5070/file1.csv')
path_r2 = Path('workspace/results/lambda5070/file2.csv')

fig, ax, comparison = plot_flipped_bethe_roots(path_r1, path_r2, annotate=False)
plt.show()
```

## Cross-check an SYT and Its Flip

Run an SYT and its KKR flip concurrently with Bertini, then compare
`Roots[SYT]` with `-Roots[FlipSYT]` using symmetric Hausdorff distance:

```bash
bash scripts/crosscheck.sh '{{1,3},{2}}'
```

Both the original and flipped SYT result CSVs are saved permanently in
`workspace/results/`. Set `CROSSCHECK_RESULT_SYT_DIR` to use another destination.
The final Hausdorff calculation is performed by lightweight Python code,
avoiding an additional Wolfram kernel startup.

The default pass tolerance is `1e-5`. Override it or retain all temporary CSVs
and logs with:

```bash
bash scripts/crosscheck.sh --tolerance 1e-8 --keep-workdir '{{1,3},{2}}'
```

The command exits with status `0` when the distance satisfies the tolerance,
`1` when it does not, and `2` for an input or execution error.

## Branch Jump Note

If two symmetry-related tableaux should have roots `A` and `-A`, but the results
do not match, the tracker may have followed different branches. In the tests in
this folder, increasing the starting parameter from `lambda0 = 70` to
`lambda0 = 5070` and using the high-precision settings above made the pair match
with zero reported difference.
