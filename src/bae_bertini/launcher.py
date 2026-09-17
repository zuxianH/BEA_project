#!/usr/bin/env python3
"""Start the local Streamlit server using the project's Python environment."""
import os
from pathlib import Path
import sys


def main():
    from .paths import ROOT
    root = ROOT
    python = root / '.venv/bin/python'
    if not python.is_file():
        python = Path(sys.executable)
    os.chdir(root)
    os.execv(str(python), [str(python), '-m', 'streamlit', 'run',
                          str(root / 'streamlit_app.py'), '--server.address=127.0.0.1',
                          '--browser.gatherUsageStats=false', *sys.argv[1:]])


if __name__ == '__main__':
    main()
