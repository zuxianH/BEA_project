#!/usr/bin/env python3
"""Merge completed SYT snapshots under an automatically released file lock."""

import argparse
from contextlib import contextmanager
import csv
import fcntl
import os
from pathlib import Path
import tempfile
import time

FIELDS = ["RunID", "Tableau", "YoungDiagram", "SucceededQ", "FailureReason", "TimingSeconds", "BetheRoots"]
FAIL_FIELDS = ["Tableau", "YoungDiagram", "FailureReason", "Diagnostic", "RunID", "ResultFile"]


def key(text):
    return "".join((text or "").split())


@contextmanager
def result_lock(aggregate_file, timeout=60):
    # Keep this file: unlinking a flock file can give two writers different locks.
    with aggregate_file.with_suffix(aggregate_file.suffix + ".flock").open("a") as lock:
        deadline = time.monotonic() + timeout
        while True:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                if time.monotonic() >= deadline:
                    raise TimeoutError(f"Timed out waiting to merge {aggregate_file}")
                time.sleep(0.1)
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def write_table(path, fieldnames, rows, delimiter=","):
    with tempfile.NamedTemporaryFile(
        mode="w", newline="", encoding="utf-8", dir=path.parent,
        prefix=f".{path.name}.", suffix=".tmp", delete=False,
    ) as handle:
        temporary = Path(handle.name)
        try:
            writer = csv.DictWriter(handle, fieldnames=fieldnames, delimiter=delimiter, extrasaction="ignore")
            writer.writeheader()
            writer.writerows(rows)
            handle.close()
            os.replace(temporary, path)
        finally:
            temporary.unlink(missing_ok=True)


def merge_results(staging_dir, target_yd, aggregate_file, fail_file, lock_timeout=60):
    aggregate_file.parent.mkdir(parents=True, exist_ok=True)
    fail_file.parent.mkdir(parents=True, exist_ok=True)
    target_yd = key(target_yd)
    with result_lock(aggregate_file, lock_timeout):
        staged = sorted(staging_dir.glob("*.csv"))
        if not staged and aggregate_file.exists() and fail_file.exists():
            return False
        diagnostics = {}
        if fail_file.exists():
            with fail_file.open(newline="", encoding="utf-8") as handle:
                diagnostics = {key(r["Tableau"]): r.get("Diagnostic", "") for r in csv.DictReader(handle, delimiter="\t")}
        rows_by_tableau = {}
        consumed = {}
        paths = [(aggregate_file, False)] if aggregate_file.exists() else []
        paths += [(p, True) for p in staged]
        for path, is_staged in paths:
            with path.open(newline="", encoding="utf-8") as handle:
                identity = os.fstat(handle.fileno())
                reader = csv.DictReader(handle, strict=True)
                if not set(FIELDS).issubset(reader.fieldnames or []):
                    raise ValueError(f"Incomplete result CSV header: {path}")
                for row in reader:
                    if any(row.get(name) is None for name in FIELDS) or None in row:
                        raise ValueError(f"Incomplete result row: {path}")
                    tableau = key(row["Tableau"])
                    if key(row["YoungDiagram"]) != target_yd or not tableau:
                        raise ValueError(f"Unexpected tableau/Young diagram in {path}")
                    rows_by_tableau[tableau] = row
                    if is_staged:
                        consumed[path] = (identity.st_dev, identity.st_ino)

        ordered_keys = sorted(rows_by_tableau)
        write_table(aggregate_file, FIELDS, (rows_by_tableau[k] for k in ordered_keys))

        def failures():
            for tableau in ordered_keys:
                row = rows_by_tableau[tableau]
                if row["SucceededQ"].strip().lower() in {"true", "1", "yes"}:
                    continue
                yield dict(row, Diagnostic=row.get("Diagnostic", "") or diagnostics.get(tableau, ""),
                           ResultFile=str(aggregate_file))

        write_table(fail_file, FAIL_FIELDS, failures(), delimiter="\t")
        for path, identity in consumed.items():
            try:
                current = path.stat()
                # A concurrent rerun may have atomically replaced this snapshot.
                if (current.st_dev, current.st_ino) == identity:
                    path.unlink()
            except FileNotFoundError:
                pass
        # Leave the staging directory available to active producers.
        return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("staging_dir", type=Path)
    parser.add_argument("young_diagram")
    parser.add_argument("aggregate_file", type=Path)
    parser.add_argument("fail_file", type=Path)
    args = parser.parse_args()
    if merge_results(args.staging_dir, args.young_diagram, args.aggregate_file, args.fail_file):
        print(f"Updated aggregate: {args.aggregate_file}")


if __name__ == "__main__":
    main()


def read_results(path, limit=500):
    with Path(path).open(newline='', encoding='utf-8-sig') as stream:
        reader = csv.DictReader(stream)
        rows = []
        for row in reader:
            if len(rows) == limit:
                return rows, True
            rows.append(row)
        return rows, False
