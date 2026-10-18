#!/usr/bin/env python3
"""Run every formal check and record exit codes before packaging evidence."""
from pathlib import Path
import json,os,subprocess,time

p=Path(__file__).resolve().parent;r=p.parents[1];e=p/'evidence'
env=os.environ.copy();env['PATH']='/home/thlinux/.elan/bin:'+env.get('PATH','')
env['PYTHONDONTWRITEBYTECODE']='1'
e.mkdir(exist_ok=True)
results=[]
def run(name,cmd,cwd=r):
    started=time.monotonic()
    with (e/(name+'.log')).open('w') as out:
        ret=subprocess.run(cmd,cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT)
    results.append({'name':name,'command':cmd,'cwd':str(cwd),'exit_code':ret.returncode,
                    'seconds':time.monotonic()-started})
    (e/'build-results.json').write_text(json.dumps(results,indent=2)+'\n')
    if ret.returncode:
        print((e/(name+'.log')).read_text()[-12000:],flush=True)
        raise SystemExit(ret.returncode)
    print('PASS: '+name,flush=True)

run('provenance',['python3',str(p/'verify_provenance.py')])
run('public-inventory',['python3',str(p/'check_public_roots.py')])
modules=['OddSourceTwentyFour','OddSourceBoxes','OddTrialData','OddTrialPositivity',
         'OrderedKernelPositivity','OddOrderedCertificate','OddPhysicalTwelve',
         'OddPhysicalPolarization','ResidualObstructions','Regression','Audit']
# Sequential compilation bounds peak memory of kernel integer reduction.
for name in modules:
    run(name,['/usr/bin/time','-f','elapsed=%e maxrss_kb=%M','bash',str(p/'compile_module.sh'),name])
run('root-build',['lake','build','--wfail'])
for zone in ['foundation','geometry','analysis']:
    run(zone+'-audit',['bash','scripts/audit-'+zone+'.sh'])
run('final-provenance',['python3',str(p/'verify_provenance.py')])
subprocess.run(['python3',str(p/'package_evidence.py')],check=True,cwd=r,env=env)
