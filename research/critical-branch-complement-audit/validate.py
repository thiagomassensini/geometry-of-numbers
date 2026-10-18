#!/usr/bin/env python3
"""Record bounded Lean/build commands without treating baseline failures as passes."""
from pathlib import Path
import subprocess, json, hashlib, datetime, sys
root=Path(__file__).resolve().parents[2]
kind='geometry' if root.name=='geometry-of-numbers' else 'operator'
out=Path(__file__).resolve().parent/'evidence'
out.mkdir(exist_ok=True)
commands=[('source-check',[sys.executable,str(Path(__file__).with_name('check_sources.py'))])]
if kind=='geometry':
    commands += [
        ('focused',['lake','build','--wfail','GeometryOfNumbers.Analysis.CriticalBranchComplementTransport','GeometryOfNumbers.Analysis.CriticalBranchComplementAudit']),
        ('root',['lake','build','--wfail']),
        ('foundation',['bash','scripts/audit-foundation.sh']),
        ('analysis',['bash','scripts/audit-analysis.sh']),
        ('geometry',['bash','scripts/audit-geometry.sh'])]
else:
    commands += [
        ('focused',['lake','build','--wfail','CarrySelfAdjointOperator.CriticalBranchNativeObstructions','CarrySelfAdjointOperator.CriticalBranchNativeAudit']),
        ('root',['lake','build','--wfail']),
        ('audit-root',['lake','build','--wfail','CarrySelfAdjointOperator.Audit']),
        ('physical-registry',[sys.executable,'scripts/check_physical_sewing_registry.py'])]
commands += [('diff-check',['git','diff','--check'])]
records=[]
for label,cmd in commands:
    path=out/(label+'.log')
    started=datetime.datetime.now(datetime.timezone.utc).isoformat()
    with path.open('w') as stream:
        result=subprocess.run(cmd,cwd=root,stdout=stream,stderr=subprocess.STDOUT)
    records.append(dict(label=label,command=cmd,started_utc=started,exit_code=result.returncode,
        log=path.name,sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
    (out/'validation.json').write_text(json.dumps(dict(repository=root.name,checks=records),indent=2)+'\n')
    print(label,result.returncode,flush=True)
    if result.returncode:
        print(path.read_text()[-5000:],flush=True)
        sys.exit(result.returncode)
print('VALIDATED',root.name,flush=True)
