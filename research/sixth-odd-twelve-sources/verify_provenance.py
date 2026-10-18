#!/usr/bin/env python3
"""Check original sources/pins and existing cached-dependency manifests."""
import hashlib,json,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[2]
o=r.parent/'carry-self-adjoint-operator'
base='76fead5cbc40c350449966a5f5c89ff8ea47d234'
def git(p,*args):return subprocess.check_output(['git','-C',str(p),*args],text=True).strip()
assert git(o,'rev-parse','HEAD')=='045369f6dedcb2e75e9aefed1d12c9f73b9a2532'
assert (r/'lean-toolchain').read_bytes()==(o/'lean-toolchain').read_bytes()
def pins(p):return {x['name']:x['rev'] for x in json.loads((p/'lake-manifest.json').read_text())['packages'] if x['name'] in ['mathlib','GreenFrame']}
assert pins(r)==pins(o) and len(pins(r))==2
changed=git(r,'diff','--name-only',base,'--').splitlines()
assert all(p.startswith('research/sixth-odd-twelve-sources/') for p in changed),changed
for folder in ['return-block-compatibility','corrected-green-source-ports','prime-camera-schur','critical-source-return','material-integral-certificate','theta-fifth-odd-pattern','sixth-even-source-schur']:
    manifest=json.loads((r/'research'/folder/'evidence/source-manifest.json').read_text())
    for name,digest in manifest['lean_sources'].items():
        assert hashlib.sha256((r/'research'/folder/name).read_bytes()).hexdigest()==digest,(folder,name)
    assert (r/'.lake/build/research'/folder).is_dir()
print('PASS: original source trees, historical module manifests, operator commit and common pins unchanged')
