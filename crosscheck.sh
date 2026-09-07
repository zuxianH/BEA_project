#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WOLFRAM_KERNEL="${WOLFRAM_KERNEL:-WolframKernel}"
PYTHON="$ROOT_DIR/.venv/bin/python"
RUN_SINGLE="$ROOT_DIR/RunSingle.wl"
HELPER="$ROOT_DIR/crosscheck.wl"
COMPARE_HELPER="$ROOT_DIR/crosscheck_compare.py"
TOLERANCE="1e-5"
KEEP_WORKDIR=0
SYT=""
SAVED_RESULT_DIR="${CROSSCHECK_RESULT_SYT_DIR:-$ROOT_DIR/Result_SYT}"
if [[ "$SAVED_RESULT_DIR" != /* ]]; then
  SAVED_RESULT_DIR="$ROOT_DIR/$SAVED_RESULT_DIR"
fi

usage() {
  cat <<'USAGE'
Usage:
  ./crosscheck.sh '{{1,3},{2}}'
  ./crosscheck.sh --tolerance 1e-8 --keep-workdir '{{1,3},{2}}'

Runs an SYT and its KKR-flipped SYT with Bertini, then checks the symmetric
Hausdorff distance between Roots[SYT] and -Roots[FlipSYT].

Options:
  --tolerance VALUE   Pass threshold. Default: 1e-5.
  --keep-workdir      Keep temporary CSVs and logs under .runs/crosscheck-*.
  -h, --help          Show this help.

The Bertini BERTINI_* environment variables are honored. Current defaults are
lambda 500 -> 0, precision 100, tolerance 1e-12, maximum precision 1200,
maximum steps 300000, maximum step size 1/100, maximum Newton iterations 4,
and predictor RKCashKarp45.
The flipped result is saved in Result_SYT. Override its destination with
CROSSCHECK_RESULT_SYT_DIR.
USAGE
}

die() {
  printf 'Error: %s\n' "$*" >&2
  exit 2
}

while (($#)); do
  case "$1" in
    --tolerance)
      [[ $# -ge 2 ]] || die "--tolerance needs a value"
      TOLERANCE="$2"
      shift 2
      ;;
    --keep-workdir)
      KEEP_WORKDIR=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    -*)
      die "unknown option: $1"
      ;;
    *)
      [[ -z "$SYT" ]] || die "pass exactly one SYT"
      SYT="$1"
      shift
      ;;
  esac
done

[[ -n "$SYT" ]] || die "missing SYT"
[[ -x "$PYTHON" ]] || die "missing Python environment: $PYTHON"
[[ -f "$RUN_SINGLE" && -f "$HELPER" && -f "$COMPARE_HELPER" ]] || \
  die "missing RunSingle.wl, crosscheck.wl, or crosscheck_compare.py"
command -v "$WOLFRAM_KERNEL" >/dev/null 2>&1 || die "Wolfram executable not found: $WOLFRAM_KERNEL"
"$PYTHON" -c 'import bertini' >/dev/null 2>&1 || die "Python cannot import bertini"

export BERTINI_INITIAL_LAMBDA="${BERTINI_INITIAL_LAMBDA:-500}"
export BERTINI_TARGET_LAMBDA="${BERTINI_TARGET_LAMBDA:-0}"
export BERTINI_WORKING_PRECISION="${BERTINI_WORKING_PRECISION:-100}"
export BERTINI_DEFAULT_PRECISION="${BERTINI_DEFAULT_PRECISION:-100}"
export BERTINI_TRACKING_TOLERANCE="${BERTINI_TRACKING_TOLERANCE:-1e-12}"
export BERTINI_MAX_PRECISION="${BERTINI_MAX_PRECISION:-1200}"
export BERTINI_MAX_NUM_STEPS="${BERTINI_MAX_NUM_STEPS:-500000}"
export BERTINI_MAX_STEP_SIZE="${BERTINI_MAX_STEP_SIZE:-1/200}"
export BERTINI_MAX_NEWTON_ITERATIONS="${BERTINI_MAX_NEWTON_ITERATIONS:-4}"
export BERTINI_PREDICTOR="${BERTINI_PREDICTOR:-RKCashKarp45}"

mkdir -p "$ROOT_DIR/.runs"
WORK_DIR="$(mktemp -d "$ROOT_DIR/.runs/crosscheck-XXXXXX")"
RESULT_DIR="$WORK_DIR/results"
FLIP_FILE="$WORK_DIR/flip.txt"
REPORT_FILE="$WORK_DIR/report.txt"
mkdir -p "$RESULT_DIR"

cleanup() {
  local status=$?
  if ((KEEP_WORKDIR)) || ((status != 0)); then
    printf 'Work directory: %s\n' "$WORK_DIR"
  else
    rm -rf "$WORK_DIR"
  fi
}
trap cleanup EXIT

"$WOLFRAM_KERNEL" -noprompt -script "$HELPER" flip "$SYT" "$FLIP_FILE" \
  >"$WORK_DIR/flip.stdout.log" 2>"$WORK_DIR/flip.stderr.log"
FLIP_SYT="$(tr -d '\r\n' < "$FLIP_FILE")"
[[ -n "$FLIP_SYT" ]] || die "failed to compute flipped SYT"

run_syt() {
  local label="$1"
  local tableau="$2"
  BERTINI_RESULT_SYT_DIR="$RESULT_DIR" \
    "$WOLFRAM_KERNEL" -noprompt -script "$RUN_SINGLE" "$tableau" \
    >"$WORK_DIR/${label}.stdout.log" 2>"$WORK_DIR/${label}.stderr.log"
}

printf 'Running SYT: %s\n' "$SYT"
run_syt original "$SYT" &
ORIGINAL_PID=$!
FLIPPED_PID=""

if [[ "${SYT//[[:space:]]/}" != "${FLIP_SYT//[[:space:]]/}" ]]; then
  printf 'Running flipped SYT: %s\n' "$FLIP_SYT"
  run_syt flipped "$FLIP_SYT" &
  FLIPPED_PID=$!
else
  printf 'Flipped SYT is identical; reusing the original result.\n'
fi

set +e
wait "$ORIGINAL_PID"
ORIGINAL_STATUS=$?
FLIPPED_STATUS=0
if [[ -n "$FLIPPED_PID" ]]; then
  wait "$FLIPPED_PID"
  FLIPPED_STATUS=$?
fi
set -e

if ((ORIGINAL_STATUS != 0 || FLIPPED_STATUS != 0)); then
  printf 'OriginalStatus=%d\nFlippedStatus=%d\n' "$ORIGINAL_STATUS" "$FLIPPED_STATUS" >&2
  cat "$WORK_DIR/original.stderr.log" >&2
  if [[ -f "$WORK_DIR/flipped.stderr.log" ]]; then
    cat "$WORK_DIR/flipped.stderr.log" >&2
  fi
  die "one or both Bertini runs failed"
fi

mkdir -p "$SAVED_RESULT_DIR"
shopt -s nullglob
RESULT_FILES=("$RESULT_DIR"/*.csv)
shopt -u nullglob
((${#RESULT_FILES[@]} > 0)) || die "no result CSVs were produced"
for RESULT_FILE in "${RESULT_FILES[@]}"; do
  SAVED_RESULT="$SAVED_RESULT_DIR/$(basename "$RESULT_FILE")"
  SAVED_TMP="${SAVED_RESULT}.tmp.$$"
  cp -- "$RESULT_FILE" "$SAVED_TMP"
  mv -- "$SAVED_TMP" "$SAVED_RESULT"
  printf 'Saved result: %s\n' "$SAVED_RESULT"
done

set +e
"$PYTHON" "$COMPARE_HELPER" "$RESULT_DIR" "$SYT" "$FLIP_SYT" "$TOLERANCE" \
  --report "$REPORT_FILE" \
  >"$WORK_DIR/compare.stdout.log" 2>"$WORK_DIR/compare.stderr.log"
COMPARE_STATUS=$?
set -e

[[ -f "$REPORT_FILE" ]] || {
  cat "$WORK_DIR/compare.stdout.log" >&2
  cat "$WORK_DIR/compare.stderr.log" >&2
  die "comparison failed"
}

cat "$REPORT_FILE"
printf 'BertiniLambda=%s->%s\n' "$BERTINI_INITIAL_LAMBDA" "$BERTINI_TARGET_LAMBDA"
printf 'BertiniWorkingPrecision=%s\n' "$BERTINI_WORKING_PRECISION"
printf 'BertiniDefaultPrecision=%s\n' "$BERTINI_DEFAULT_PRECISION"
printf 'BertiniTrackingTolerance=%s\n' "$BERTINI_TRACKING_TOLERANCE"
printf 'BertiniMaxStepSize=%s\n' "$BERTINI_MAX_STEP_SIZE"
printf 'BertiniMaxNewtonIterations=%s\n' "$BERTINI_MAX_NEWTON_ITERATIONS"
printf 'BertiniPredictor=%s\n' "$BERTINI_PREDICTOR"

exit "$COMPARE_STATUS"
