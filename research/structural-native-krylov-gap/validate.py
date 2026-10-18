from pathlib import Path
import datetime,hashlib,json,subprocess,sys
folder=Path(__file__).resolve().parent; root=folder.parents[1]
evidence=folder/'evidence';evidence.mkdir(exist_ok=True)
commands=[('source',[sys.executable,str(folder/'check_sources.py')]),
 ('focused',['lake','build','--wfail','GeometryOfNumbers.Analysis.MaterialClockKrylovGap','GeometryOfNumbers.Analysis.MaterialClockKrylovGapAudit']),
 ('canonical',['bash',str(folder/'compile_module.sh'),'CanonicalClockGap']),
 ('regression',['bash',str(folder/'compile_module.sh'),'Regression']),
 ('axioms',['bash',str(folder/'compile_module.sh'),'Audit']),
 ('root',['lake','build','--wfail']),
 ('foundation',['bash','scripts/audit-foundation.sh']),
 ('geometry',['bash','scripts/audit-geometry.sh']),
 ('analysis',['bash','scripts/audit-analysis.sh']),
 ('diff',['git','diff','--check'])]
records=[]
for label,cmd in commands:
    log=evidence/(label+'.log')
    started=datetime.datetime.now(datetime.timezone.utc).isoformat()
    with log.open('w') as out:r=subprocess.run(cmd,cwd=root,stdout=out,stderr=subprocess.STDOUT)
    records.append(dict(label=label,command=cmd,exit_code=r.returncode,started_utc=started,log=log.name,sha256=hashlib.sha256(log.read_bytes()).hexdigest()))
    (evidence/'validation.json').write_text(json.dumps(dict(base='59e53d863f4ef0ad998b0eb19fd3891c9839cc35',checks=records),indent=2)+'\n')
    print(label,r.returncode,flush=True)
    if r.returncode:
        print(log.read_text()[-5000:],flush=True);sys.exit(r.returncode)
print('VALIDATED: structural-native-krylov-gap',flush=True)
