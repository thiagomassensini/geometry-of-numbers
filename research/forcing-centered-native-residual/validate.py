#!/usr/bin/env python3
"""Validate the new physical identity; preserve main, PRs and native source."""
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

root=Path(__file__).resolve().parent
repo=root.parent.parent
operator=repo.parent/'carry-self-adjoint-operator'
evidence=root/'evidence'
evidence.mkdir(exist_ok=True)
base='845829bacd623f044ba779e23da0bb4c48d25c11'
relative=str(root.relative_to(repo))
env=os.environ.copy()
env['PATH']='/home/thlinux/.elan/bin:'+env['PATH']
env['PYTHONDONTWRITEBYTECODE']='1'

def read(*args,cwd=repo):
    return subprocess.check_output(args,cwd=cwd,env=env,text=True).strip()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

refs=['main','origin/main','agent/native-moment-orthogonalization-audit',
      'agent/seventh-even-centered-source','agent/source-euler-residual-control',
      'agent/native-positive-square-kernel','agent/entrywise-moment-square',
      'agent/native-return-boundary-deflation','agent/native-cauchy-residual-return',
      'agent/completed-green-confluent-balance']
protected=[operator/'CarrySelfAdjointOperator'/name for name in
           ['C2OddTfvdTransport.lean','C2OddTfvdTransportAudit.lean']]
preflight={'base':base,'branch':read('git','branch','--show-current'),
           'head_before_commit':read('git','rev-parse','HEAD'),
           'protected_refs':{r:read('git','rev-parse',r) for r in refs},
           'operator_head':read('git','rev-parse','HEAD',cwd=operator),
           'operator_status':read('git','status','--short',cwd=operator),
           'protected_source_sha256':{str(p):sha(p) for p in protected},
           'manifest_sha256':{str(p):sha(p) for p in [repo/'lake-manifest.json',operator/'lake-manifest.json']},
           'toolchain':(repo/'lean-toolchain').read_text().strip(),
           'worktrees':read('git','worktree','list','--porcelain')}
assert not read('git','diff','HEAD','--',cwd=operator)
# PR51 is intentionally not an ancestor of this physical investigation.
# Its checkout residue belongs to the earlier task and must remain untouched.
pr51=repo/'research/entrywise-moment-square'
preflight['preserved_pr51_files']={str(p.relative_to(pr51)):sha(p) for p in sorted(pr51.rglob('*'))
                                 if p.is_file()}
(evidence/'preflight.json').write_text(json.dumps(preflight,indent=2)+'\n')
for path in root.glob('*.lean'):
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s',path.read_text(),re.M),path

checks=[
    ('recover-pr37',['python3',f'{relative}/prepare_pr37.py'],repo),
    ('audit-generation',['python3',f'{relative}/generate_audit.py'],repo),
    ('native-operator-build',['lake','build','--wfail',
      'CarrySelfAdjointOperator.CompletedNativeChiralReturnFiniteTransfer',
      'CarrySelfAdjointOperator.CompletedNativeCentralChiralQuotientCurvature'],operator),
]
checks += [(f'kernel-{m}',['bash',f'{relative}/compile_module.sh',m],repo)
           for m in ['Forcing37','SourceBalance37','ForcingCenter','RetainedLeg','CriticalGreen','Audit']]
checks += [
    ('exact-rational-controls',['python3',f'{relative}/experiment.py'],repo),
    ('focused-build',['lake','build','--wfail','GeometryOfNumbers.Analysis.CarryMaterialSourceFactor',
                      'GeometryOfNumbers.Analysis.CanonicalFiniteHeight'],repo),
    ('root-build',['lake','build','--wfail'],repo),
    ('foundation-audit',['bash','scripts/audit-foundation.sh'],repo),
    ('geometry-audit',['bash','scripts/audit-geometry.sh'],repo),
    ('analysis-audit',['bash','scripts/audit-analysis.sh'],repo),
    ('twelve-source-regression',['bash','research/sixth-odd-twelve-sources/compile_module.sh','Regression'],repo),
    ('historical-files-unchanged',['git','diff','--exit-code',base,'--','.',f':(exclude){relative}'],repo),
    ('diff-check',['git','diff','--check'],repo),
]
results=[]
for name,command,cwd in checks:
    start=time.monotonic()
    with tempfile.TemporaryFile(mode='w+',encoding='utf-8') as output:
        result=subprocess.run(command,cwd=cwd,env=env,stdout=output,stderr=subprocess.STDOUT)
        output.seek(0)
        log='\n'.join(line.rstrip() for line in output.read().splitlines())+'\n'
    if name in ['root-build','analysis-audit']:
        (evidence/f'{name}.log.gz').write_bytes(gzip.compress(log.encode(),mtime=0))
    else:
        (evidence/f'{name}.log').write_text(log)
    results.append({'name':name,'command':command,'cwd':str(cwd),'exit_code':result.returncode,
                    'seconds':round(time.monotonic()-start,3)})
    (evidence/'checks.json').write_text(json.dumps(results,indent=2)+'\n')
    print(name+(': PASS' if result.returncode==0 else ': FAIL'),flush=True)
    if result.returncode:
        print(log[-7000:])
        raise SystemExit(result.returncode)
for r,value in preflight['protected_refs'].items():
    assert read('git','rev-parse',r)==value
assert read('git','rev-parse','HEAD',cwd=operator)==preflight['operator_head']
assert read('git','status','--short',cwd=operator)==preflight['operator_status']
assert not read('git','diff','HEAD','--',cwd=operator)
for path,value in preflight['protected_source_sha256'].items():
    assert sha(Path(path))==value
for path,value in preflight['manifest_sha256'].items():
    assert sha(Path(path))==value
for name,value in preflight['preserved_pr51_files'].items():
    assert sha(pr51/name)==value
manifest={str(p.relative_to(root)):sha(p) for p in sorted(root.rglob('*'))
          if p.is_file() and '.cache' not in p.parts and 'evidence' not in p.parts}
(evidence/'source-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'PASS: {len(results)} checks; complete source, main, prior PRs and pins preserved',flush=True)
