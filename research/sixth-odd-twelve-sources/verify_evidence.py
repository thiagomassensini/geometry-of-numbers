#!/usr/bin/env python3
"""Verify exported evidence integrity and the public-root axiom outputs."""
from pathlib import Path
import hashlib,json,re
p=Path(__file__).resolve().parent;e=p/'evidence'
m=json.loads((e/'source-manifest.json').read_text())
v=json.loads((e/'validation.json').read_text())
for group in ['lean_sources','scripts','documentation']:
    for name,digest in m[group].items():
        assert hashlib.sha256((p/name).read_bytes()).hexdigest()==digest,name
for group in ['logs','data']:
    for name,digest in v[group].items():
        assert hashlib.sha256((e/name).read_bytes()).hexdigest()==digest,name
assert len(v['commands'])==18 and all(x['exit_code']==0 for x in v['commands'])
roots=(p/'public-roots.txt').read_text().splitlines()
assert len(roots)==v['public_roots']==78
audit=(e/'Audit.log').read_text()
for name in roots:
    assert name in audit,name
allowed={'propext','Classical.choice','Quot.sound'}
for axioms in re.findall(r'depends on axioms: \[([^\]]*)\]',audit):
    assert {x.strip() for x in axioms.split(',') if x.strip()} <= allowed,axioms
print('PASS: all source, data and log hashes; 18 successful commands; 78 public roots; standard Analysis axioms only')
