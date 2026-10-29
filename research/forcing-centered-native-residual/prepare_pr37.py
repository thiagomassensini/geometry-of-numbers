#!/usr/bin/env python3
"""Recover immutable PR37 sources; preserve every mathematical body."""
from pathlib import Path
import hashlib
import json
import subprocess

root=Path(__file__).resolve().parent
repo=root.parent.parent
commit='bf2ff244e363b110a4e54ba897e475b81552bbdb'
sources={
    'Forcing37':'GeometryOfNumbers/Analysis/CarryMaterialForcingGreenEnergy.lean',
    'SourceBalance37':'research/completed-green-confluent-balance/SourceBalance.lean',
}
cache=root/'.cache/pr37/source'
cache.mkdir(parents=True,exist_ok=True)
manifest={}
for module,path in sources.items():
    original=subprocess.check_output(['git','show',f'{commit}:{path}'],cwd=repo)
    adapted=original.replace(b'import GeometryOfNumbers.Analysis.CarryMaterialForcingGreenEnergy\n',
                             b'import Forcing37\n') if module=='SourceBalance37' else original
    assert adapted.split(b'\n',1)[1]==original.split(b'\n',1)[1]
    (cache/f'{module}.lean').write_bytes(adapted)
    manifest[module]={'commit':commit,'path':path,
        'original_sha256':hashlib.sha256(original).hexdigest(),
        'recovered_sha256':hashlib.sha256(adapted).hexdigest(),
        'change':'import name only' if adapted!=original else 'byte-identical'}
evidence=root/'evidence'
evidence.mkdir(exist_ok=True)
(evidence/'pr37-source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('PASS: PR37 immutable proof bodies recovered; only import adapter changed')
