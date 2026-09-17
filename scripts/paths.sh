#!/usr/bin/env bash
# Source this from repository scripts; never depend on the caller's cwd.
ROOT_DIR="${BAE_BERTINI_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
RUNS_DIR="$ROOT_DIR/workspace/runs"
LOGS_DIR="$ROOT_DIR/workspace/logs"
RESULTS_DIR="$ROOT_DIR/workspace/results"
TABLEAUX_DIR="$ROOT_DIR/data/tableaux"
export PYTHONPATH="$ROOT_DIR/src${PYTHONPATH:+:$PYTHONPATH}"
