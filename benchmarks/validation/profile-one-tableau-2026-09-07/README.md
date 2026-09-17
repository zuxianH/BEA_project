# One-tableau timing profile

Tableau: `{{1, 4, 6, 7}, {2, 5}, {3}}`, from `Result_SYT/all_SYT_{4,2,1}.csv`.

One complete run took **8.953 seconds**. The roots matched the reference, with maximum one-to-one difference **6.619e-17**, below tolerance `1e-8`. The reference SHA-256 was unchanged.

| Non-overlapping category | Seconds | Share |
| --- | ---: | ---: |
| Mathematica calculations and equation preparation/transfer | 3.427 | 38.3% |
| Bertini path tracking | 0.920 | 10.3% |
| Other Python/backend process time | 1.037 | 11.6% |
| Mathematica launch/load/finalization and measurement overhead | 3.569 | 39.9% |

Mathematica equation export preparation took 2.334 seconds within its calculation time. The first call took 2.297 seconds; subsequent calls took 0.006–0.013 seconds. This block includes equation formatting, initial-point refinement, and CSV exports, so this measurement does not isolate CSV initialization from the other operations.
Symbolic system construction took 0.605 seconds. There were 5 Bertini subprocess calls.

The next candidate is reusing initialized Mathematica workers between tableaux, followed by separating the cost of the first export-preparation call. This profile supports investigating initialization and preparation overhead for small tableaux; it does not establish a speedup or the bottleneck for larger tableaux. No numerical tolerances or production source files were changed for this measurement.

Method: ran a temporary copy of the current workflow with timing markers around dependency loading, RunSingleSYT, and intermediate-root extraction. Existing per-stage timers supplied the Mathematica/backend breakdown. An external Python timer measured the whole kernel process. Timing-report serialization happens after the internal driver timer and is included in the launch/load/finalization/measurement category. Raw values are in `profile.json`, `execution.json`, and `workflow.timings.csv`; the resulting roots and their comparison are included beside this report.
