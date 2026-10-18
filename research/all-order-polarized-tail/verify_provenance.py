#!/usr/bin/env python3
"""Check pins, immutable upstream source and absence of proof escapes."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from check_public_roots import lean_code

BASE = '76fead5cbc40c350449966a5f5c89ff8ea47d234'
OPERATOR = '045369f6dedcb2e75e9aefed1d12c9f73b9a2532'
DEPENDENCIES = [
    'theta-fifth-odd-pattern', 'critical-source-return',
    'return-block-compatibility', 'corrected-green-source-ports',
    'material-integral-certificate', 'prime-camera-schur',
    'material-pivot-certificate', 'material-central-calibration',
]


def head(root):
    return subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()


def pins(root):
    return {p['name']: p['rev'] for p in json.loads((root/'lake-manifest.json').read_text())['packages']
            if p['name'] in ('mathlib', 'GreenFrame')}


def verify(repo, operator):
    assert head(operator) == OPERATOR, 'Changed operator pin'
    assert (repo/'lean-toolchain').read_bytes() == (operator/'lean-toolchain').read_bytes()
    assert pins(repo) == pins(operator) and len(pins(repo)) == 2
    unchanged = ['GeometryOfNumbers', 'scripts', 'lean-toolchain', 'lake-manifest.json']
    unchanged += ['research/'+f for f in DEPENDENCIES]
    subprocess.run(['git', '-C', str(repo), 'diff', '--exit-code', BASE, '--', *unchanged], check=True)
    for folder in DEPENDENCIES:
        manifest_path = repo/'research'/folder/'evidence/source-manifest.json'
        # These older packages predate that manifest format. Their source
        # bytes are still checked against BASE above and hashed in our ledger.
        if folder in ('material-pivot-certificate', 'material-central-calibration'):
            continue
        manifest = json.loads(manifest_path.read_text())
        for name, expected in manifest['lean_sources'].items():
            assert hashlib.sha256((repo/'research'/folder/name).read_bytes()).hexdigest() == expected
    research = Path(__file__).resolve().parent
    for path in research.glob('*.lean'):
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', lean_code(path.read_text())), path
    print('PASS: unchanged source, pinned dependencies and no trust escapes')


if __name__ == '__main__':
    verify(*map(Path, sys.argv[1:]))
