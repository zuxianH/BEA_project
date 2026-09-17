#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/paths.sh"
PYTHON_EXECUTABLE="$ROOT_DIR/.venv/bin/python"
if [[ ! -x "$PYTHON_EXECUTABLE" ]]; then
  PYTHON_EXECUTABLE="${PYTHON_EXECUTABLE_OVERRIDE:-python3}"
fi

exec "$PYTHON_EXECUTABLE" -m bae_bertini.flip_checks "$@"
