"""Streamlit entry point; run with `python3 bertini_studio.py`."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent / 'src'))
from bae_bertini.ui.app import main

if __name__ == '__main__':
    main()
