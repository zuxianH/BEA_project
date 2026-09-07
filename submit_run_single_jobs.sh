#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WOLFRAM_KERNEL="${WOLFRAM_KERNEL:-WolframKernel}"
RUN_SINGLE="$ROOT_DIR/RunSingle.wl"
PYTHON_EXECUTABLE="$ROOT_DIR/.venv/bin/python"
if [[ ! -x "$PYTHON_EXECUTABLE" ]]; then
  PYTHON_EXECUTABLE="${PYTHON_EXECUTABLE_OVERRIDE:-python3}"
fi

BERTINI_INITIAL_LAMBDA="${BERTINI_INITIAL_LAMBDA:-500}"
BERTINI_TARGET_LAMBDA="${BERTINI_TARGET_LAMBDA:-0}"
BERTINI_WORKING_PRECISION="${BERTINI_WORKING_PRECISION:-100}"
BERTINI_DEFAULT_PRECISION="${BERTINI_DEFAULT_PRECISION:-100}"
BERTINI_TRACKING_TOLERANCE="${BERTINI_TRACKING_TOLERANCE:-1e-12}"
BERTINI_INFINITE_TOLERANCE="${BERTINI_INFINITE_TOLERANCE:-1e30}"
BERTINI_MAX_PRECISION="${BERTINI_MAX_PRECISION:-1200}"
BERTINI_MAX_NUM_STEPS="${BERTINI_MAX_NUM_STEPS:-500000}"
BERTINI_MAX_STEP_SIZE="${BERTINI_MAX_STEP_SIZE:-1/200}"
BERTINI_MAX_NEWTON_ITERATIONS="${BERTINI_MAX_NEWTON_ITERATIONS:-4}"
BERTINI_PREDICTOR="${BERTINI_PREDICTOR:-RKCashKarp45}"
SYT_LOCK_STALE_SECONDS="${SYT_LOCK_STALE_SECONDS:-21600}"
RESULT_SYT_DIR="${BERTINI_RESULT_SYT_DIR:-$ROOT_DIR/Result_SYT}"
if [[ "$RESULT_SYT_DIR" != /* ]]; then
  RESULT_SYT_DIR="$ROOT_DIR/$RESULT_SYT_DIR"
fi
BERTINI_RESULT_SYT_DIR="$RESULT_SYT_DIR"
export BERTINI_INITIAL_LAMBDA BERTINI_TARGET_LAMBDA
export BERTINI_WORKING_PRECISION BERTINI_DEFAULT_PRECISION
export BERTINI_TRACKING_TOLERANCE BERTINI_INFINITE_TOLERANCE BERTINI_MAX_PRECISION
export BERTINI_MAX_NUM_STEPS BERTINI_MAX_STEP_SIZE
export BERTINI_MAX_NEWTON_ITERATIONS BERTINI_PREDICTOR BERTINI_RESULT_SYT_DIR

LIST_FILE=""
YD=""
MAX_JOBS=1
LOG_DIR="$ROOT_DIR/logs/RunSingle"
LOG_DIR_SET=0
LOGS_ENABLED=1
DRY_RUN=0
SKIP_EXISTING=1
CLEANUP_RUNS=0
PART_INDEX=""
PART_COUNT=9

declare -A completed_tableaux=()
declare -A failed_tableaux=()

usage() {
  cat <<'USAGE'
Usage:
  ./submit_run_single_jobs.sh --yd '{2,2,1}' -j 8
  ./submit_run_single_jobs.sh --yd '{5,4,3,2,1}_1' -j 100
  ./submit_run_single_jobs.sh --yd '{5,4,3,2,1}_1' -n 9 -j 100
  ./submit_run_single_jobs.sh --list my_SYT/{2,2,1}.txt -j 8

Options:
  --yd YD              Young diagram in Mathematica InputForm, e.g. '{2,2,1}'.
                       Add _N suffix to run partition N of 9, e.g. '{5,4,3,2,1}_4'.
                       Creates/updates my_SYT/{2,2,1}.txt if --list is absent.
  --list FILE          Text file with one SYT per line. If --yd is absent,
                       the Young diagram is inferred from the first SYT entry.
  --part N             Run only partition N. Equivalent to --yd '{...}_N'.
  -n, --parts N        Number of partitions. Default: 9.
  -j, --jobs N         Maximum simultaneous RunSingle.wl jobs. Default: 1.
  --logs DIR           Directory for stdout/stderr logs. Default: logs/RunSingle,
                       or logs/RunSingle/<YD>_part_<N>_of_<M> for partitioned runs.
  --no-logs            Do not write per-SYT stdout/stderr logs under logs/RunSingle.
                       Job output is redirected to /dev/null.
  --rerun-existing     Submit jobs even when the result directory contains a
                       successful row or failed row for the SYT.
  --cleanup-runs       Delete each successful .runs/syt-* work directory after
                       its temporary batch result CSV has been saved.
  --dry-run            Print commands without submitting jobs.
  -h, --help           Show this help.

Environment:
  WOLFRAM_KERNEL       Wolfram executable to use. Default: WolframKernel.
  BERTINI_INITIAL_LAMBDA       Default: 500.
  BERTINI_TARGET_LAMBDA        Default: 0.
  BERTINI_WORKING_PRECISION    Default: 100.
  BERTINI_DEFAULT_PRECISION    Default: 100.
  BERTINI_TRACKING_TOLERANCE   Default: 1e-12.
  BERTINI_INFINITE_TOLERANCE   Default: 1e30.
  BERTINI_MAX_PRECISION        Default: 1200.
  BERTINI_MAX_NUM_STEPS        Default: 500000.
  BERTINI_MAX_STEP_SIZE        Default: 1/200.
  BERTINI_MAX_NEWTON_ITERATIONS Default: 4.
  BERTINI_PREDICTOR            Default: RKCashKarp45.
  BERTINI_RESULT_SYT_DIR       Default: <script directory>/Result_SYT.
  SYT_LOCK_STALE_SECONDS       Age for reclaiming remote locks. Default: 21600.
USAGE
}

die() {
  printf 'Error: %s\n' "$*" >&2
  exit 1
}

quote_cmd() {
  printf '%q ' "$@"
  printf '\n'
}

input_form_key() {
  printf '%s' "$1" | tr -d '[:space:]'
}

parse_yd_partition_suffix() {
  local raw_yd="$1"

  if [[ "$raw_yd" =~ ^(.+)_([1-9][0-9]*)$ ]]; then
    YD="${BASH_REMATCH[1]}"
    if [[ -n "$PART_INDEX" && "$PART_INDEX" != "${BASH_REMATCH[2]}" ]]; then
      die "partition specified twice with different values: _${BASH_REMATCH[2]} and --part $PART_INDEX"
    fi
    PART_INDEX="${BASH_REMATCH[2]}"
  else
    YD="$raw_yd"
  fi
}

aggregate_result_file_for_yd() {
  local yd="$1"
  printf '%s/all_SYT_%s.csv\n' "$RESULT_SYT_DIR" "$(input_form_key "$yd")"
}

fail_result_file_for_yd() {
  local yd="$1"
  printf '%s/fail_%s.txt\n' "$RESULT_SYT_DIR" "$(input_form_key "$yd")"
}

generate_syt_list() {
  local yd="$1"
  local output_file="$2"
  local generator
  local status

  mkdir -p "$(dirname "$output_file")"
  generator="$(mktemp "${TMPDIR:-/tmp}/generate-syt-list.XXXXXX.wl")"
  cat > "$generator" <<'WL'
Off[FrontEndObject::notavail];
Needs["Combinatorica`"];

args = Take[$CommandLine, -3];
yd = Quiet@Check[ToExpression[args[[1]], InputForm], $Failed];
outputFile = args[[2]];
cacheDirectory = args[[3]];

If[! MatchQ[yd, {__Integer}],
  Print["Invalid Young diagram: ", args[[1]]];
  Exit[1]
];

If[! DirectoryQ[cacheDirectory],
  CreateDirectory[cacheDirectory, CreateIntermediateDirectories -> True]
];

key = StringReplace[ToString[yd, InputForm], WhitespaceCharacter .. -> ""];
cacheFile = FileNameJoin[{cacheDirectory, key <> ".wxf"}];

cached = If[FileExistsQ[cacheFile],
  Quiet@Check[Import[cacheFile, "WXF"], $Failed],
  $Failed
];

allSYT = Replace[
  cached,
  {
    assoc_Association :> Lookup[assoc, "Tableaux", $Failed],
    other_ :> other
  }
];

If[! ListQ[allSYT],
  allSYT = Combinatorica`Tableaux[yd];
  Export[
    cacheFile,
    <|
      "YoungDiagram" -> yd,
      "Tableaux" -> allSYT,
      "Count" -> Length[allSYT],
      "SavedAt" -> DateString[{"ISODate", "T", "Time"}]
    |>,
    "WXF"
  ];
];

Export[
  outputFile,
  StringRiffle[ToString[#, InputForm] & /@ allSYT, "\n"] <> "\n",
  "Text"
];

Print["SYT list: ", outputFile];
Print["SYT count: ", Length[allSYT]];
WL

  if "$WOLFRAM_KERNEL" -noprompt -script "$generator" "$yd" "$output_file" "$ROOT_DIR/my_SYT"; then
    status=0
  else
    status=$?
  fi
  rm -f "$generator"
  return "$status"
}

release_syt_list_lock() {
  local lock_dir="$1"

  rm -f "$lock_dir/owner"
  rmdir "$lock_dir" 2>/dev/null || true
}

syt_list_lock_is_stale() {
  local lock_dir="$1"
  local owner_file="$lock_dir/owner"
  local owner_host=""
  local owner_pid=""
  local owner_started=""
  local current_host
  local now
  local modified
  local age

  current_host="$(hostname)"
  now="$(date +%s)"
  modified="$(stat -c %Y "$lock_dir" 2>/dev/null || printf '%s' "$now")"
  age=$((now - modified))

  if [[ -r "$owner_file" ]]; then
    IFS=$'\t' read -r owner_host owner_pid owner_started < "$owner_file" || true
    if [[ "$owner_host" == "$current_host" ]]; then
      if [[ "$owner_pid" =~ ^[1-9][0-9]*$ ]]; then
        ! kill -0 "$owner_pid" 2>/dev/null
        return
      fi
      ((age >= 10))
      return
    fi

    if [[ "$owner_host" != "$current_host" && "$age" -ge "$SYT_LOCK_STALE_SECONDS" ]]; then
      return 0
    fi
    return 1
  fi

  # Older versions created empty lock directories. Give a new owner a moment
  # to write its metadata, then reclaim an abandoned empty lock.
  ((age >= 10))
}

ensure_syt_list() {
  local yd="$1"
  local output_file="$2"
  local lock_dir="${output_file}.lock"
  local status

  if [[ -s "$output_file" ]]; then
    printf 'Using existing SYT list: %s\n' "$output_file"
    return 0
  fi

  while ! mkdir "$lock_dir" 2>/dev/null; do
    if [[ -s "$output_file" ]]; then
      printf 'Using existing SYT list: %s\n' "$output_file"
      return 0
    fi
    if syt_list_lock_is_stale "$lock_dir"; then
      printf 'Removing stale SYT list lock: %s\n' "$lock_dir"
      release_syt_list_lock "$lock_dir"
      continue
    fi
    printf 'Waiting for SYT list lock: %s\n' "$lock_dir"
    sleep 5
  done

  printf '%s\t%s\t%s\n' "$(hostname)" "$$" "$(date +%s)" > "$lock_dir/owner"
  trap 'release_syt_list_lock "$lock_dir"' EXIT INT TERM

  if [[ -s "$output_file" ]]; then
    release_syt_list_lock "$lock_dir"
    trap - EXIT INT TERM
    printf 'Using existing SYT list: %s\n' "$output_file"
    return 0
  fi

  if generate_syt_list "$yd" "$output_file"; then
    status=0
  else
    status=$?
  fi
  release_syt_list_lock "$lock_dir"
  trap - EXIT INT TERM
  return "$status"
}

resolve_yd_from_list() {
  local list_file="$1"

  "$PYTHON_EXECUTABLE" - "$list_file" <<'PY'
import ast
import sys

list_file = sys.argv[1]
entry = None
with open(list_file, encoding='utf-8') as handle:
    for raw_line in handle:
        line = raw_line.strip()
        if line and not line.startswith('#'):
            entry = line
            break

if entry is None:
    raise SystemExit(f"No SYT entries found in list file: {list_file}")

try:
    tableau = ast.literal_eval(entry.replace('{', '[').replace('}', ']'))
except Exception as exc:  # pragma: no cover
    raise SystemExit(f"Invalid SYT entry in list file: {entry}\n{exc}") from exc

if not isinstance(tableau, list) or not tableau or any(
    not isinstance(row, list) or not row or any(not isinstance(value, int) for value in row)
    for row in tableau
):
    raise SystemExit(f"Invalid SYT entry in list file: {entry}")

print('{' + ','.join(str(len(row)) for row in tableau) + '}')
PY
}

count_syt_entries() {
  local list_file="$1"
  local count=0
  local line

  while IFS= read -r line || [[ -n "$line" ]]; do
    [[ -n "${line//[[:space:]]/}" ]] || continue
    [[ "$line" =~ ^[[:space:]]*# ]] && continue
    count=$((count + 1))
  done < "$list_file"

  printf '%d\n' "$count"
}

load_completed_tableaux_map() {
  local result_dir="$1"
  local aggregate_file="$2"
  local target_yd="$3"
  local tableau_key

  while IFS= read -r tableau_key || [[ -n "$tableau_key" ]]; do
    [[ -n "$tableau_key" ]] || continue
    completed_tableaux["$tableau_key"]=1
  done < <(
    "$PYTHON_EXECUTABLE" - "$result_dir" "$aggregate_file" "$target_yd" <<'PY'
import csv
import sys
from pathlib import Path

result_dir = Path(sys.argv[1])
aggregate_file = Path(sys.argv[2])
target_yd = ''.join(sys.argv[3].split())
paths = []
if result_dir.is_dir():
    paths.extend(
        path for path in result_dir.glob('*.csv')
        if not path.name.startswith('all_SYT_')
    )
if aggregate_file.is_file():
    paths.append(aggregate_file)

seen = set()
for path in paths:
    try:
        with path.open(newline='', encoding='utf-8') as handle:
            reader = csv.DictReader(handle)
            for row in reader:
                yd = ''.join((row.get('YoungDiagram') or '').split())
                if yd != target_yd:
                    continue
                succeeded = (row.get('SucceededQ') or '').strip().lower()
                if succeeded not in {'true', '1', 'yes'}:
                    continue
                tableau = ''.join((row.get('Tableau') or '').split())
                if tableau and tableau not in seen:
                    seen.add(tableau)
                    print(tableau)
    except (OSError, csv.Error, UnicodeError):
        continue
PY
  )
}

load_failed_tableaux_map() {
  local result_dir="$1"
  local fail_file="$2"
  local target_yd="$3"
  local tableau_key

  while IFS= read -r tableau_key || [[ -n "$tableau_key" ]]; do
    [[ -n "$tableau_key" ]] || continue
    failed_tableaux["$tableau_key"]=1
  done < <(
    "$PYTHON_EXECUTABLE" - "$result_dir" "$fail_file" "$target_yd" <<'PY'
import csv
import sys
from pathlib import Path

result_dir = Path(sys.argv[1])
fail_file = Path(sys.argv[2])
target_yd = ''.join(sys.argv[3].split())

seen = set()
if result_dir.is_dir():
    for path in result_dir.glob('*.csv'):
        if path.name.startswith('all_SYT_'):
            continue
        try:
            with path.open(newline='', encoding='utf-8') as handle:
                for row in csv.DictReader(handle):
                    yd = ''.join((row.get('YoungDiagram') or '').split())
                    if yd != target_yd:
                        continue
                    succeeded = (row.get('SucceededQ') or '').strip().lower()
                    if succeeded in {'true', '1', 'yes'}:
                        continue
                    tableau = ''.join((row.get('Tableau') or '').split())
                    if tableau and tableau not in seen:
                        seen.add(tableau)
                        print(tableau)
        except (OSError, csv.Error, UnicodeError):
            continue

if fail_file.is_file():
    with fail_file.open(encoding='utf-8') as handle:
        for raw_line in handle:
            line = raw_line.strip()
            if not line or line.startswith('#'):
                continue
            parts = line.split('\t')
            if not parts or parts[0] == 'Tableau':
                continue
            tableau = ''.join(parts[0].split())
            if not tableau:
                continue
            if len(parts) >= 2:
                yd = ''.join(parts[1].split())
                if yd.startswith('{') and yd != target_yd:
                    continue
            if tableau not in seen:
                seen.add(tableau)
                print(tableau)
PY
  )
}

rebuild_result_indexes() {
  local staging_dir="$1"
  local target_yd="$2"
  local aggregate_file="$3"
  local fail_file="$4"
  local lock_dir="${aggregate_file}.lock"
  local status

  while ! mkdir "$lock_dir" 2>/dev/null; do
    sleep 1
  done

  set +e
  "$PYTHON_EXECUTABLE" - "$staging_dir" "$target_yd" "$aggregate_file" "$fail_file" <<'PY'
import csv
import os
import sys
from pathlib import Path

staging_dir = Path(sys.argv[1])
target_yd = ''.join(sys.argv[2].split())
aggregate_file = Path(sys.argv[3])
fail_file = Path(sys.argv[4])
rows_by_tableau = {}
consumed_staging_files = set()
existing_fail_diagnostics = {}

if fail_file.is_file():
    try:
        with fail_file.open(encoding='utf-8') as handle:
            reader = csv.DictReader(handle, delimiter='\t')
            for row in reader:
                tableau = ''.join((row.get('Tableau') or '').split())
                if tableau:
                    existing_fail_diagnostics[tableau] = row.get('Diagnostic', '')
    except (OSError, csv.Error, UnicodeError):
        pass

paths = []
if aggregate_file.is_file():
    paths.append((aggregate_file, False))
if staging_dir.is_dir():
    paths.extend((path, True) for path in staging_dir.glob('*.csv'))

for path, is_staged in paths:
    try:
        with path.open(newline='', encoding='utf-8') as handle:
            rows = list(csv.DictReader(handle))
    except (OSError, csv.Error, UnicodeError):
        continue
    for row in rows:
        yd = ''.join((row.get('YoungDiagram') or '').split())
        tableau = ''.join((row.get('Tableau') or '').split())
        if yd == target_yd and tableau and 'SucceededQ' in row:
            rows_by_tableau[tableau] = row
            if is_staged:
                consumed_staging_files.add(path)

rows = [rows_by_tableau[key] for key in sorted(rows_by_tableau)]
fieldnames = [
    'RunID', 'Tableau', 'YoungDiagram', 'SucceededQ',
    'FailureReason', 'TimingSeconds', 'BetheRoots'
]

aggregate_file.parent.mkdir(parents=True, exist_ok=True)
aggregate_tmp = aggregate_file.with_name(f'.{aggregate_file.name}.{os.getpid()}.tmp')
with aggregate_tmp.open('w', newline='', encoding='utf-8') as handle:
    writer = csv.DictWriter(handle, fieldnames=fieldnames, extrasaction='ignore')
    writer.writeheader()
    writer.writerows(rows)
os.replace(aggregate_tmp, aggregate_file)

fail_tmp = fail_file.with_name(f'.{fail_file.name}.{os.getpid()}.tmp')
with fail_tmp.open('w', encoding='utf-8') as handle:
    handle.write(
        'Tableau\tYoungDiagram\tFailureReason\tDiagnostic\t'
        'RunID\tResultFile\n'
    )
    for row in rows:
        succeeded = (row.get('SucceededQ') or '').strip().lower()
        if succeeded in {'true', '1', 'yes'}:
            continue
        values = [
            row.get('Tableau', ''),
            row.get('YoungDiagram', ''),
            row.get('FailureReason', ''),
            row.get('Diagnostic', '') or existing_fail_diagnostics.get(
                ''.join((row.get('Tableau') or '').split()),
                ''
            ),
            row.get('RunID', ''),
            str(aggregate_file),
        ]
        handle.write('\t'.join(str(value).replace('\t', ' ') for value in values) + '\n')
os.replace(fail_tmp, fail_file)

for path in consumed_staging_files:
    try:
        path.unlink()
    except FileNotFoundError:
        pass
try:
    staging_dir.rmdir()
except OSError:
    pass
PY
  status=$?
  set -e
  rmdir "$lock_dir"
  return "$status"
}

merge_completed_results() {
  if rebuild_result_indexes "$JOB_RESULT_DIR" "$YD" "$AGGREGATE_RESULT_FILE" "$FAIL_RESULT_FILE"; then
    printf 'Updated aggregate: %s\n' "$AGGREGATE_RESULT_FILE"
    return 0
  fi
  printf 'Warning: could not update aggregate/failure result indexes.\n' >&2
  return 1
}

while (($#)); do
  case "$1" in
    --yd)
      [[ $# -ge 2 ]] || die "--yd needs an argument"
      YD="$2"
      shift 2
      ;;
    --list)
      [[ $# -ge 2 ]] || die "--list needs an argument"
      LIST_FILE="$2"
      shift 2
      ;;
    --part)
      [[ $# -ge 2 ]] || die "--part needs an argument"
      PART_INDEX="$2"
      shift 2
      ;;
    -n|--parts)
      [[ $# -ge 2 ]] || die "--parts needs an argument"
      PART_COUNT="$2"
      shift 2
      ;;
    -j|--jobs)
      [[ $# -ge 2 ]] || die "--jobs needs an argument"
      MAX_JOBS="$2"
      shift 2
      ;;
    --logs)
      [[ $# -ge 2 ]] || die "--logs needs an argument"
      LOG_DIR="$2"
      LOG_DIR_SET=1
      LOGS_ENABLED=1
      shift 2
      ;;
    --no-logs)
      LOGS_ENABLED=0
      shift
      ;;
    --rerun-existing)
      SKIP_EXISTING=0
      shift
      ;;
    --cleanup-runs)
      CLEANUP_RUNS=1
      shift
      ;;
    --dry-run)
      DRY_RUN=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      die "unknown option: $1"
      ;;
  esac
done

[[ "$MAX_JOBS" =~ ^[1-9][0-9]*$ ]] || die "--jobs must be a positive integer"
[[ "$PART_COUNT" =~ ^[1-9][0-9]*$ ]] || die "--parts must be a positive integer"
[[ "$SYT_LOCK_STALE_SECONDS" =~ ^[1-9][0-9]*$ ]] || die "SYT_LOCK_STALE_SECONDS must be a positive integer"
[[ -f "$RUN_SINGLE" ]] || die "missing $RUN_SINGLE"
command -v "$WOLFRAM_KERNEL" >/dev/null 2>&1 || die "Wolfram executable not found: $WOLFRAM_KERNEL"
command -v "$PYTHON_EXECUTABLE" >/dev/null 2>&1 || die "Python executable not found: $PYTHON_EXECUTABLE"
"$PYTHON_EXECUTABLE" -c 'import bertini' >/dev/null 2>&1 || die "Python cannot import bertini: $PYTHON_EXECUTABLE"

if ((CLEANUP_RUNS)); then
  export BERTINI_CLEANUP_RUNS=1
fi

if [[ -n "$YD" ]]; then
  parse_yd_partition_suffix "$YD"
fi

if [[ -n "$PART_INDEX" ]]; then
  [[ "$PART_INDEX" =~ ^[1-9][0-9]*$ ]] || die "--part must be a positive integer"
  PART_INDEX=$((10#$PART_INDEX))
  PART_COUNT=$((10#$PART_COUNT))
  ((PART_INDEX <= PART_COUNT)) || die "--part must be less than or equal to --parts"
fi

if [[ -z "$LIST_FILE" ]]; then
  [[ -n "$YD" ]] || die "pass either --yd or --list"
  yd_key="$(input_form_key "$YD")"
  LIST_FILE="$ROOT_DIR/my_SYT/${yd_key}.txt"
  ensure_syt_list "$YD" "$LIST_FILE"
fi

[[ -f "$LIST_FILE" ]] || die "missing SYT list file: $LIST_FILE"

if [[ -z "$YD" ]]; then
  YD="$(resolve_yd_from_list "$LIST_FILE")"
fi

yd_key="$(input_form_key "$YD")"
AGGREGATE_RESULT_FILE="$(aggregate_result_file_for_yd "$YD")"
FAIL_RESULT_FILE="$(fail_result_file_for_yd "$YD")"
JOB_RESULT_DIR="$ROOT_DIR/.runs/batch-results/$yd_key"

if [[ -n "$PART_INDEX" && "$LOG_DIR_SET" -eq 0 ]]; then
  LOG_DIR="$ROOT_DIR/logs/RunSingle/${yd_key}_part_${PART_INDEX}_of_${PART_COUNT}"
fi

mkdir -p "$RESULT_SYT_DIR"
mkdir -p "$JOB_RESULT_DIR"
if ((LOGS_ENABLED)); then
  mkdir -p "$LOG_DIR"
fi

if ((SKIP_EXISTING)); then
  load_completed_tableaux_map "$JOB_RESULT_DIR" "$AGGREGATE_RESULT_FILE" "$YD"
  load_failed_tableaux_map "$JOB_RESULT_DIR" "$FAIL_RESULT_FILE" "$YD"
fi

TOTAL_LIST_ENTRIES="$(count_syt_entries "$LIST_FILE")"
PART_START=1
PART_END="$TOTAL_LIST_ENTRIES"
PART_SIZE="$TOTAL_LIST_ENTRIES"

if [[ -n "$PART_INDEX" ]]; then
  base_size=$((TOTAL_LIST_ENTRIES / PART_COUNT))
  extra_count=$((TOTAL_LIST_ENTRIES % PART_COUNT))
  if ((PART_INDEX <= extra_count)); then
    PART_SIZE=$((base_size + 1))
    PART_START=$(((PART_INDEX - 1) * (base_size + 1) + 1))
  else
    PART_SIZE="$base_size"
    PART_START=$((extra_count * (base_size + 1) + (PART_INDEX - extra_count - 1) * base_size + 1))
  fi
  PART_END=$((PART_START + PART_SIZE - 1))
  if ((PART_SIZE == 0)); then
    PART_START=1
    PART_END=0
  fi
fi

printf 'Target YD: %s\n' "$YD"
printf 'SYT list: %s\n' "$LIST_FILE"
printf 'SYT entries in list: %d\n' "$TOTAL_LIST_ENTRIES"
if [[ -n "$PART_INDEX" ]]; then
  printf 'Partition: %d/%d entries %d-%d count %d\n' "$PART_INDEX" "$PART_COUNT" "$PART_START" "$PART_END" "$PART_SIZE"
fi
printf 'Aggregate result file: %s\n' "$AGGREGATE_RESULT_FILE"
printf 'Failure result file: %s\n' "$FAIL_RESULT_FILE"
printf 'Temporary batch results: %s\n' "$JOB_RESULT_DIR"
printf 'Bertini settings: lambda %s -> %s, working/default precision %s/%s\n' \
  "$BERTINI_INITIAL_LAMBDA" "$BERTINI_TARGET_LAMBDA" \
  "$BERTINI_WORKING_PRECISION" "$BERTINI_DEFAULT_PRECISION"
printf 'Bertini tracker: tolerance %s, infinity tolerance %s, max precision %s, max steps %s, max step size %s, max Newton iterations %s, predictor %s\n' \
  "$BERTINI_TRACKING_TOLERANCE" "$BERTINI_INFINITE_TOLERANCE" "$BERTINI_MAX_PRECISION" \
  "$BERTINI_MAX_NUM_STEPS" "$BERTINI_MAX_STEP_SIZE" \
  "$BERTINI_MAX_NEWTON_ITERATIONS" "$BERTINI_PREDICTOR"
printf 'Already solved SYTs: %d\n' "${#completed_tableaux[@]}"
printf 'Already failed SYTs: %d\n' "${#failed_tableaux[@]}"
if ((LOGS_ENABLED)); then
  printf 'Logs: %s\n' "$LOG_DIR"
else
  printf 'Logs: disabled\n'
fi
printf 'Cleanup successful run dirs: %s\n' "$CLEANUP_RUNS"

submitted=0
skipped=0
skipped_failed=0
failures=0
line_number=0
entry_number=0
outside_partition=0

declare -A scheduled_tableaux=()

while IFS= read -r syt || [[ -n "$syt" ]]; do
  line_number=$((line_number + 1))
  [[ -n "${syt//[[:space:]]/}" ]] || continue
  [[ "$syt" =~ ^[[:space:]]*# ]] && continue

  entry_number=$((entry_number + 1))
  if [[ -n "$PART_INDEX" ]] && ((entry_number < PART_START || entry_number > PART_END)); then
    outside_partition=$((outside_partition + 1))
    continue
  fi

  syt_key="$(input_form_key "$syt")"
  if ((SKIP_EXISTING)) && [[ -n "${completed_tableaux[$syt_key]+x}" ]]; then
    printf 'Skipping existing solved SYT in %s: %s\n' "$AGGREGATE_RESULT_FILE" "$syt"
    skipped=$((skipped + 1))
    continue
  fi

  if ((SKIP_EXISTING)) && [[ -n "${failed_tableaux[$syt_key]+x}" ]]; then
    printf 'Skipping existing failed SYT in %s: %s\n' "$FAIL_RESULT_FILE" "$syt"
    skipped=$((skipped + 1))
    skipped_failed=$((skipped_failed + 1))
    continue
  fi

  if [[ -n "${scheduled_tableaux[$syt_key]+x}" ]]; then
    printf 'Skipping duplicate SYT entry on line %d: %s\n' "$line_number" "$syt"
    skipped=$((skipped + 1))
    continue
  fi
  scheduled_tableaux["$syt_key"]=1

  submitted=$((submitted + 1))
  job_id="$(printf '%05d' "$submitted")"
  if ((LOGS_ENABLED)); then
    stdout_log="$LOG_DIR/${job_id}.out"
    stderr_log="$LOG_DIR/${job_id}.err"
  fi

  cmd=(env "BERTINI_RESULT_SYT_DIR=$JOB_RESULT_DIR" "$WOLFRAM_KERNEL" -noprompt -script "$RUN_SINGLE" "$syt")
  if ((DRY_RUN)); then
    printf '[dry-run] '
    quote_cmd "${cmd[@]}"
    continue
  fi

  while (( $(jobs -pr | wc -l) >= MAX_JOBS )); do
    if ! wait -n; then
      failures=$((failures + 1))
    fi
    if ! merge_completed_results; then
      failures=$((failures + 1))
    fi
  done

  printf 'Submitting job %s from line %d entry %d: %s\n' "$job_id" "$line_number" "$entry_number" "$syt"
  if ((LOGS_ENABLED)); then
    "${cmd[@]}" > "$stdout_log" 2> "$stderr_log" &
  else
    "${cmd[@]}" >/dev/null 2>&1 &
  fi
done < "$LIST_FILE"

if ((DRY_RUN)); then
  printf 'Dry run complete. Commands planned: %d, skipped existing: %d, skipped failed: %d\n' "$submitted" "$skipped" "$skipped_failed"
  if [[ -n "$PART_INDEX" ]]; then
    printf 'Outside selected partition: %d\n' "$outside_partition"
  fi
  exit 0
fi

while (( $(jobs -pr | wc -l) > 0 )); do
  if ! wait -n; then
    failures=$((failures + 1))
  fi
  if ! merge_completed_results; then
    failures=$((failures + 1))
  fi
done

if ! merge_completed_results; then
  failures=$((failures + 1))
fi

printf 'Submitted: %d\n' "$submitted"
printf 'Skipped existing: %d\n' "$skipped"
printf 'Skipped failed: %d\n' "$skipped_failed"
if [[ -n "$PART_INDEX" ]]; then
  printf 'Outside selected partition: %d\n' "$outside_partition"
fi
printf 'Failed jobs: %d\n' "$failures"
if ((LOGS_ENABLED)); then
  printf 'Logs: %s\n' "$LOG_DIR"
else
  printf 'Logs: disabled\n'
fi
printf 'Aggregate result file: %s\n' "$AGGREGATE_RESULT_FILE"
printf 'Failure result file: %s\n' "$FAIL_RESULT_FILE"

if ((failures > 0)); then
  exit 1
fi
