#!/usr/bin/env python3
"""Recompile only the four unchanged PR90 source dependencies."""
from pathlib import Path
import hashlib,json,subprocess
root=Path(__file__).resolve().parent
repo=root.parents[1]
base='457ea144d33d0b376a5c589b06ef1695e6d14adb'
record={}
for n in ['PrimeProjection','PrimeAnalysis','PrimeCanaries','MellinPrimeReadout']:
 p=root.parent/'source-dependent-prime-readouts'/f'{n}.lean'
 rel=str(p.relative_to(repo))
 original=subprocess.check_output(['git','show',base+':'+rel],cwd=repo)
 assert p.read_bytes()==original
 subprocess.run(['bash',str(root/'compile_module.sh'),n,str(p)],check=True)
 record[n]={'source':rel,'source_sha256':hashlib.sha256(original).hexdigest(),
            'olean_sha256':hashlib.sha256((p.parent/'.cache'/f'{n}.olean').read_bytes()).hexdigest()}
 print('UPSTREAM PASS '+n,flush=True)
(root/'evidence/upstream.json').write_text(json.dumps({'base':base,'modules':record},indent=2)+'\n')
