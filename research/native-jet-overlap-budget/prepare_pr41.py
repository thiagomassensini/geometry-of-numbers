#!/usr/bin/env python3
"""Read and compile immutable proof sources from PR #41, without merging it."""
from pathlib import Path
import hashlib
import json
import os
import subprocess

root=Path(__file__).resolve().parent
repo=root.parent.parent
operator=repo.parent/'carry-self-adjoint-operator'
revision='ee56930a2c30456cfbd214a29bb31b12d3977204'
modules=['MomentFunctional','PolynomialCoordinates','JacobiLogic','NativeApplication','SchurLogic']
cache=root/'.cache'/'pr41'
source=cache/'source'
source.mkdir(parents=True,exist_ok=True)
env=os.environ.copy()
env['PATH']='/home/thlinux/.elan/bin:'+env['PATH']
subprocess.run(['git','cat-file','-e',revision+'^{commit}'],cwd=repo,check=True)
hashes={}
for module in modules:
    relative='research/native-moment-orthogonalization-audit/'+module+'.lean'
    data=subprocess.check_output(['git','show',revision+':'+relative],cwd=repo)
    (source/(module+'.lean')).write_bytes(data)
    hashes[relative]=hashlib.sha256(data).hexdigest()
repo_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,env=env,text=True).strip()
operator_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=operator,env=env,text=True).strip()
env['LEAN_PATH']=str(cache)+':'+repo_path+':'+operator_path
for module in modules:
    subprocess.run(['lean','-DwarningAsError=true','--root='+str(source),
                    '-o',str(cache/(module+'.olean')),str(source/(module+'.lean'))],
                   cwd=repo,env=env,check=True)
    print('PR41 '+module+': PASS',flush=True)
evidence=root/'evidence'
evidence.mkdir(exist_ok=True)
(evidence/'pr41-source.json').write_text(json.dumps({'pr':41,'commit':revision,
    'mode':'immutable git-object sources; no merge; no tracked source replacement',
    'sha256':hashes},indent=2)+'\n')
