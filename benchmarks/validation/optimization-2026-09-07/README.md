# Optimization validation — 2026-09-07

All three representative reruns passed. The original reference files were preserved. Full sweeps were stopped at the user request.

| Reference | Tableau | Maximum root difference |
| --- | --- | --- |
| all_SYT_{3,2,1}.csv | `{{1, 2, 6}, {3, 4}, {5}}` | 4.692e-17 |
| all_SYT_{3,2,1}.csv | `{{1, 2, 6}, {3, 5}, {4}}` | 2.876e-17 |
| all_SYT_{4,2,1}.csv | `{{1, 2, 3, 4}, {5, 6}, {7}}` | 1.373e-14 |

The comparison uses one-to-one matching within each Bethe-root level, including root counts and multiplicities, with tolerance `1e-8`. Raw rerun CSVs and exact errors are included beside this report in `results.json`.

Eleven Python regression tests passed, covering real/finite coefficient checks, atomic output rollback, failed tracking, equivalence of the optimized distance calculation, result merging and resume, corrupt inputs, concurrent writers, automatic lock release after process termination, and simulated batch consolidation. Wolfram tests passed for a 100-digit CSV round trip, scientific notation, invalid input rejection, and unevaluated muted diagnostics. Shell syntax and whitespace checks passed.

The numerical reruns use initial lambda 500, target 0, working/default precision 100, tracking tolerance 1e-12, maximum precision 1200, maximum step size 1/200, and RKCashKarp45. The full settings and reference SHA-256 checksums are in `results.json`.

The saved references previously passed through machine-precision CSV import. Agreement with them verifies the selected solutions to the stated tolerance; it does not certify 100-digit accuracy of the solver. The separate CSV round-trip test verifies that serialization now preserves the supplied digits. No overall speedup claim is made from these representative runs.

Wolfram documents the numeric-conversion issue and the `"Numeric" -> False` option in its [CSV documentation](https://reference.wolfram.com/language/ref/format/CSV.html).
