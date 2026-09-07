# BAE_Bertini Package Manifest

This folder is the lightweight Bertini workflow copy intended for sharing.

Included:

- `RunSingle.wl` and `SUSYWBEWorkflow.wl`: Wolfram entry points and workflow.
- `continue_lambda0_to_zero.py`: Python/pyBertini homotopy continuation driver.
- `submit_run_single_jobs.sh`, `run.sh`, `crosscheck.sh`: run helpers.
- `check_flip_distances_fast.py` and `.sh`: fast evacuation flip-distance checker.
- `crosscheck_compare.py`, `crosscheck.wl`: crosscheck helpers.
- `solver/` and `utils/`: Mathematica solver dependencies.
- `Result_SYT/checkDistances.wl` and `Result_SYT/visualize_roots.py`: result-checking/plotting tools.
- `my_SYT/*.txt`: precomputed SYT lists useful for batch runs.
- `data/`: small example continuation CSV inputs.
- `README.md`: install and run notes.

Not included intentionally:

- `.venv/`
- `.runs/`
- `logs/`
- large aggregate result CSV outputs
- Python `__pycache__/`

