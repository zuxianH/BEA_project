#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PYTHON_EXECUTABLE="$ROOT_DIR/.venv/bin/python"
if [[ ! -x "$PYTHON_EXECUTABLE" ]]; then
  PYTHON_EXECUTABLE="${PYTHON_EXECUTABLE_OVERRIDE:-python3}"
fi

exec "$PYTHON_EXECUTABLE" "$ROOT_DIR/check_flip_distances_fast.py" "$@"
