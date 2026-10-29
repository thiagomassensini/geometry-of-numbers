#!/usr/bin/env python3
"""Focused Lean builds, source audits, numerical replay and preservation checks."""
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

root = Path(__file__).resolve().parent
repo = root.parent.parent
operator = repo.parent/'carry-self-adjoint-operator'
evidence = root/'evidence'
evidence.mkdir(exist_ok=True)
base = 'a5ed1d73b643cc4b24549b3ee3cfe10a5b29a59b'
relative = str(root.relative_to(repo))
env = os.environ.copy()
env['PATH'] = '/home/thlinux/.elan/bin:'+env['PATH']

def read(*command, cwd=repo):
    return subprocess.check_output(command, cwd=cwd, env=env, text=True).strip()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

protected = [operator/'CarrySelfAdjointOperator'/name for name in
             ['C2OddTfvdTransport.lean','C2OddTfvdTransportAudit.lean']]
refs = ['main','origin/main','agent/native-positive-square-kernel',
        'agent/native-moment-orthogonalization-audit','agent/seventh-even-centered-source']
before = {'base':base, 'branch':read('git','branch','--show-current'),
          'head_before_commit':read('git','rev-parse','HEAD'),
          'protected_refs':{name:read('git','rev-parse',name) for name in refs},
          'operator_head':read('git','rev-parse','HEAD',cwd=operator),
          'operator_status':read('git','status','--short',cwd=operator),
          'protected_sha256':{str(p):sha(p) for p in protected},
          'manifests':{str(p):sha(p) for p in [repo/'lake-manifest.json',operator/'lake-manifest.json']},
          'toolchain':(repo/'lean-toolchain').read_text().strip(),
          'worktrees':read('git','worktree','list','--porcelain')}
assert not read('git','diff','HEAD','--',cwd=operator)
(evidence/'preflight.json').write_text(json.dumps(before,indent=2)+'\n')
for path in root.glob('*.lean'):
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s',path.read_text(),re.M), path
checks = [
    ('audit-generation',['python3',f'{relative}/generate_audit.py']),
    ('kernel-EntrywiseSquare',['bash',f'{relative}/compile_module.sh','EntrywiseSquare']),
    ('kernel-NativeWitness',['bash',f'{relative}/compile_module.sh','NativeWitness']),
    ('kernel-Audit',['bash',f'{relative}/compile_module.sh','Audit']),
    ('experiment',['/home/thlinux/miniforge3/bin/python',f'{relative}/experiment.py']),
    ('focused-build',['lake','build','--wfail','GeometryOfNumbers.Analysis.CanonicalFiniteHeight']),
    ('root-build',['lake','build','--wfail']),
    ('foundation-audit',['bash','scripts/audit-foundation.sh']),
    ('geometry-audit',['bash','scripts/audit-geometry.sh']),
    ('analysis-audit',['bash','scripts/audit-analysis.sh']),
    ('historical-files-unchanged',['git','diff','--exit-code',base,'--','.',f':(exclude){relative}']),
    ('diff-check',['git','diff','--check']),
]
results = []
for name, command in checks:
    start = time.monotonic()
    with tempfile.TemporaryFile(mode='w+',encoding='utf-8') as output:
        result = subprocess.run(command,cwd=repo,env=env,stdout=output,stderr=subprocess.STDOUT)
        output.seek(0)
        log = '\n'.join(line.rstrip() for line in output.read().splitlines())+'\n'
    log_path = evidence/f'{name}.log'
    if name in ['root-build','analysis-audit']:
        log_path.with_suffix('.log.gz').write_bytes(gzip.compress(log.encode(),mtime=0))
    else:
        log_path.write_text(log)
    results.append({'name':name,'command':command,'exit_code':result.returncode,
                    'seconds':round(time.monotonic()-start,3)})
    (evidence/'checks.json').write_text(json.dumps(results,indent=2)+'\n')
    print(f'{name}: '+('PASS' if result.returncode == 0 else 'FAIL'),flush=True)
    if result.returncode:
        print(log[-6000:])
        raise SystemExit(result.returncode)
for ref,value in before['protected_refs'].items():
    assert read('git','rev-parse',ref)==value
assert read('git','rev-parse','HEAD',cwd=operator)==before['operator_head']
assert read('git','status','--short',cwd=operator)==before['operator_status']
assert not read('git','diff','HEAD','--',cwd=operator)
for path,value in before['protected_sha256'].items():
    assert sha(Path(path))==value
for path,value in before['manifests'].items():
    assert sha(Path(path))==value
manifest = {str(p.relative_to(root)):sha(p) for p in sorted(root.rglob('*'))
            if p.is_file() and '.cache' not in p.parts and 'evidence' not in p.parts}
(evidence/'source-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'PASS: {len(results)} checks; original source, main, PR41/50 and pins preserved',flush=True)
