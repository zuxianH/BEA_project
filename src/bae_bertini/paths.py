"""Repository paths shared by Python entry points, independent of the cwd."""
import os
from pathlib import Path
import sys

ROOT = Path(os.environ.get('BAE_BERTINI_ROOT', Path(__file__).resolve().parents[2])).expanduser().resolve()
WOLFRAM = ROOT / 'wolfram'
SCRIPTS = ROOT / 'scripts'
WORKSPACE = ROOT / 'workspace'
STATE = WORKSPACE / 'state'
RESULTS = WORKSPACE / 'results'
RUNS = WORKSPACE / 'runs'
LOGS = WORKSPACE / 'logs'
REFERENCES = ROOT / 'data' / 'references'
TABLEAUX = ROOT / 'data' / 'tableaux'
EXAMPLES = ROOT / 'examples' / 'continuation'
PYTHON = ROOT / '.venv' / 'bin' / 'python'
if not PYTHON.is_file():
    PYTHON = Path(sys.executable)


def local_path(value):
    """Resolve checkout paths, including locations retained in older UI settings."""
    path = Path(value).expanduser()
    path = Path(os.path.abspath(path if path.is_absolute() else ROOT / path))
    try:
        relative = path.relative_to(ROOT)
    except ValueError:
        return path.resolve()
    relocated = {
        'Result_SYT': REFERENCES,
        'Result_SYT_desktop': RESULTS / 'desktop',
        'Result_SYT_studio': RESULTS / 'studio',
        'my_SYT': TABLEAUX,
        '.desktop-state': STATE,
        '.runs': RUNS,
        'logs': LOGS,
    }
    if relative.parts and relative.parts[0] in relocated:
        path = relocated[relative.parts[0]].joinpath(*relative.parts[1:])
    return path.resolve()
