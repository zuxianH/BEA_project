# Bertini Bethe Continuation Jobs

This folder runs the Mathematica Bethe workflow, but uses Python/Bertini for
homotopy continuation. There is no Julia fallback in `RunSingle.wl`; the backend
is the local script `continue_lambda0_to_zero.py`.

## Requirements

- Python 3 with `venv`
- `wolframscript` available on `PATH`
- A shell such as `bash`

## Install Python/Bertini

From this folder:

```bash
cd /home/zuxian/Documents/Bertini

python3 -m venv .venv
.venv/bin/python -m pip install --upgrade pip
.venv/bin/python -m pip install bertini2 matplotlib ipykernel
```

Check that Bertini imports:

```bash
.venv/bin/python -c "import bertini; print('bertini import ok')"
```

The local tested setup uses `bertini2` and imports it in Python as `bertini`.

## Important Files

- `RunSingle.wl`: main entry point for one SYT job.
- `continue_lambda0_to_zero.py`: Python/Bertini path tracker used by `RunSingle.wl`.
- `run.sh`: example high-precision job command.
- `Result_SYT/`: default final SYT result CSV directory.
- `data/`: intermediate continuation input and output CSV files.
- `.runs/`: per-run logs and backend outputs.
- `plot_bethe_roots.ipynb`: notebook for plotting `BetheRoots` and comparing `-r1` with `r2`.

## Run One SYT Job

Basic command:

```bash
wolframscript -file RunSingle.wl '{{1,3,7},{2,5},{4,6}}'
```

For your current example:

```bash
wolframscript -file RunSingle.wl '{{1, 2, 3, 4, 5, 10, 11, 12}, {6, 7, 8, 9, 13, 14, 15, 16}}'
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
wolframscript -file RunSingle.wl '{{1, 2, 3, 4, 5, 10, 11, 12}, {6, 7, 8, 9, 13, 14, 15, 16}}'
```

Or run the example script:

```bash
bash run.sh
```

To keep high-precision results separate:

```bash
BERTINI_RESULT_SYT_DIR=Result_SYT_lambda5070 \
BERTINI_INITIAL_LAMBDA=5070 \
BERTINI_WORKING_PRECISION=80 \
BERTINI_DEFAULT_PRECISION=80 \
BERTINI_TRACKING_TOLERANCE=1e-10 \
BERTINI_MAX_PRECISION=1200 \
BERTINI_MAX_NUM_STEPS=300000 \
BERTINI_PREDICTOR=RKCashKarp45 \
wolframscript -file RunSingle.wl '{{1,3,4,5,7,10,11,13},{2,6,8,9,12,14,15,16}}'
```

## Run Multiple SYT Jobs

`submit_run_single_jobs.sh` launches several independent `RunSingle.wl` jobs
with a configurable local concurrency limit. It uses the recommended Bertini
settings (`lambda0 = 5070`, precision `80`, tolerance `1e-10`) by default.
Batch jobs keep only the aggregate `all_SYT_<young-diagram>.csv` in the result
directory. Per-job CSVs are staged under `.runs/batch-results`, merged, and
removed automatically. The aggregate CSV is updated atomically after each
completed SYT job, so finished solutions are visible while the batch is still
running.

Generate the SYT list for a Young diagram and run at most eight jobs at once:

```bash
./submit_run_single_jobs.sh --yd '{4,3,2,1}' -j 8
```

Use an existing list with one Mathematica-form SYT per line:

```bash
./submit_run_single_jobs.sh --list 'my_SYT/{4,3,2,1}.txt' -j 8
```

Preview commands without starting jobs:

```bash
./submit_run_single_jobs.sh --yd '{4,3,2,1}' -j 8 --dry-run
```

For partitioned runs, append the partition number to the Young diagram or use
`--part`. This example runs partition 1 of 9:

```bash
./submit_run_single_jobs.sh --yd '{5,4,3,2,1}_1' -n 9 -j 100
```

The launcher skips previously successful and failed tableaux by default. Use
`--rerun-existing` to run them again. Use `--cleanup-runs` to remove successful
`.runs/syt-*` work directories after their final CSV has been saved.

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

`RunSingle.wl` reads these environment variables:

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
| `BERTINI_RESULT_SYT_DIR` | Directory for final SYT CSVs | `Result_SYT` |
| `BERTINI_TIMEOUT` | Backend timeout in seconds | `900` |

## Outputs

Each successful job writes a final CSV in the result directory. For example:

```text
Result_SYT/{{1, 2, 3, 4, 5, 10, 11, 12}, {6, 7, 8, 9, 13, 14, 15, 16}}.csv
```

Useful columns include:

- `SucceededQ`: whether the workflow succeeded.
- `Tableau`: the SYT that was run.
- `BetheRoots`: the final roots.
- timing and diagnostic columns from the Mathematica workflow.

If a job fails, check the newest directory under `.runs/` for backend stdout,
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
.venv/bin/python continue_lambda0_to_zero.py data/initial_data_5070.csv \
  --target 0 \
  --default-precision 80 \
  --tracking-tolerance 1e-10 \
  --max-precision 1200 \
  --max-num-steps 300000 \
  --predictor RKCashKarp45
```

To write the old Julia-compatible output format:

```bash
.venv/bin/python continue_lambda0_to_zero.py data/initial_data_5070.csv \
  --legacy-output \
  --output /tmp/bertini_solution.csv \
  --timing-file /tmp/bertini_timing.csv
```

## Plot Bethe Roots

Open `plot_bethe_roots.ipynb` with the `.venv` kernel. It can:

- parse Mathematica-style complex numbers from the `BetheRoots` column;
- plot one SYT result CSV;
- compare two CSVs in the style of Mathematica `ComplexListPlot[{-r1, r2}]`.

For sign-flip checks, set:

```python
path_r1 = Path('/home/zuxian/Documents/Bertini/Result_SYT_lambda5070/file1.csv')
path_r2 = Path('/home/zuxian/Documents/Bertini/Result_SYT_lambda5070/file2.csv')

fig, ax, comparison = plot_flipped_bethe_roots(path_r1, path_r2, annotate=False)
plt.show()
```

## Cross-check an SYT and Its Flip

Run an SYT and its KKR flip concurrently with Bertini, then compare
`Roots[SYT]` with `-Roots[FlipSYT]` using symmetric Hausdorff distance:

```bash
./crosscheck.sh '{{1,3},{2}}'
```

Both the original and flipped SYT result CSVs are saved permanently in
`Result_SYT/`. Set `CROSSCHECK_RESULT_SYT_DIR` to use another destination.
The final Hausdorff calculation is performed by lightweight Python code,
avoiding an additional Wolfram kernel startup.

The default pass tolerance is `1e-5`. Override it or retain all temporary CSVs
and logs with:

```bash
./crosscheck.sh --tolerance 1e-8 --keep-workdir '{{1,3},{2}}'
```

The command exits with status `0` when the distance satisfies the tolerance,
`1` when it does not, and `2` for an input or execution error.

## Branch Jump Note

If two symmetry-related tableaux should have roots `A` and `-A`, but the results
do not match, the tracker may have followed different branches. In the tests in
this folder, increasing the starting parameter from `lambda0 = 70` to
`lambda0 = 5070` and using the high-precision settings above made the pair match
with zero reported difference.
