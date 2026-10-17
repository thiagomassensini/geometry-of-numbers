import datetime
import json
import os
from pathlib import Path
import subprocess
import sys
import time

root = Path('/home/thlinux/geometry-of-numbers')
out = Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
env['PATH'] = '/home/thlinux/.elan/bin:' + env['PATH']
steps = [
    ('focused', ['lake','build','--wfail','GeometryOfNumbers.Analysis.CarryMaterialSourceFactor']),
    ('full', ['lake','build','--wfail']),
    ('foundation', ['bash','scripts/audit-foundation.sh']),
    ('geometry', ['bash','scripts/audit-geometry.sh']),
    ('analysis', ['bash','scripts/audit-analysis.sh']),
    ('factor-regression', ['lake','env','lean','-DwarningAsError=true','research/material-source-factor/Regression.lean']),
    ('return-regression', ['lake','env','lean','-DwarningAsError=true','research/projective-global-return/Regression.lean']),
    ('valve-comparison', ['bash','scripts/audit-material-projective-comparison.sh','/home/thlinux/carry-self-adjoint-operator']),
    ('source-factor-comparison', ['bash','scripts/audit-material-central-comparison.sh','/home/thlinux/carry-self-adjoint-operator']),
]
records=[]
for name, command in steps:
    started=time.monotonic()
    print('Running '+name,flush=True)
    with (out/(name+'.log')).open('w') as stream:
        result=subprocess.run(command,cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
    records.append(dict(name=name,command=command,exit_code=result.returncode,seconds=time.monotonic()-started))
    (out/'validation.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),records=records),indent=2)+'\n')
    print(name+': '+('PASS' if result.returncode == 0 else 'FAIL'),flush=True)
    if result.returncode:
        print((out/(name+'.log')).read_text()[-5000:],flush=True)
        sys.exit(result.returncode)
