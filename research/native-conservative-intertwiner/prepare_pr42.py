#!/usr/bin/env python3
from pathlib import Path
import subprocess,hashlib,json
root=Path(__file__).resolve().parent
repo=root.parent.parent
spec=json.loads((root/'ancestor-sources.json').read_text())
out=root/'.cache/pr42/source';out.mkdir(parents=True,exist_ok=True)
for name,expected in spec['sources'].items():
 data=subprocess.check_output(['git','show',spec['commit']+':research/critical-source-relative-asymptotics/'+name],cwd=repo)
 assert hashlib.sha256(data).hexdigest()==expected,name
 (out/name).write_bytes(data)
print('Verified immutable PR42 source recovery:',len(spec['sources']))
