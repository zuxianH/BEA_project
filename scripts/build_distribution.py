#!/usr/bin/env python3
"""Build a portable source bundle from the authoritative files, with checksums."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
ROOT_FILES = ('README.md', '.gitignore', 'pyproject.toml', 'streamlit_app.py')


def distribution_files(root=ROOT):
    """Explicit allowlist excludes local state, archives, caches, and big datasets."""
    files = {name: root / name for name in ROOT_FILES}
    for directory, suffixes in {
        'src/bae_bertini': {'.py'}, 'wolfram': {'.wl', '.m'},
        'scripts': {'.py', '.sh'}, 'examples': {'.csv', '.py'},
        'tests': {'.py', '.wl'}, 'docs': {'.md'}, 'notebooks': {'.ipynb'},
        'data/tableaux': {'.txt'},
    }.items():
        for path in (root / directory).rglob('*'):
            if path.is_file() and not path.is_symlink() and path.suffix in suffixes and '__pycache__' not in path.parts:
                files[str(path.relative_to(root))] = path
    for name in ('all_SYT_{3,2,1}.csv', 'all_SYT_{4,2,1}.csv'):
        path = root / 'data/references' / name
        files[str(path.relative_to(root))] = path
    return files


def build_distribution(output, root=ROOT):
    files = distribution_files(root)
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=output.parent, suffix='.zip', delete=False) as stream:
        temporary = Path(stream.name)
    try:
        manifest = {}
        with zipfile.ZipFile(temporary, 'w', compression=zipfile.ZIP_DEFLATED) as archive:
            for name, path in sorted(files.items()):
                data = path.read_bytes()
                manifest[name] = hashlib.sha256(data).hexdigest()
                archive.write(path, 'BAE_Bertini/' + name)
            archive.writestr('BAE_Bertini/PACKAGE_MANIFEST.json', json.dumps({
                'description': 'Generated from the maintained src/ and wolfram/ tree; includes two small reference CSVs.',
                'sha256': manifest,
            }, indent=2) + '\n')
        temporary.replace(output)
    finally:
        temporary.unlink(missing_ok=True)
    return len(files)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'dist/BAE_Bertini.zip')
    args = parser.parse_args()
    count = build_distribution(args.output.resolve())
    print(f'Wrote {args.output}: {count} source/data files plus manifest')


if __name__ == '__main__':
    main()
