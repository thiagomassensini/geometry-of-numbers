from pathlib import Path
import subprocess,os,json,hashlib,gzip,time
folder=Path(__file__).resolve().parent;root=folder.parents[1]
evidence=folder/'evidence';evidence.mkdir(exist_ok=True)
env=os.environ.copy();env['PATH']='/home/thlinux/.elan/bin:'+env['PATH']
steps=[
 ['python3',str(folder/'check_sources.py')],
 ['lake','build','--wfail','GeometryOfNumbers.Analysis.CarryScaleCovarianceAudit'],
 ['bash',str(folder/'compile_module.sh'),'NativeScaleSeam'],
 ['bash',str(folder/'compile_module.sh'),'Audit'],
 ['lake','build','--wfail'],
 ['bash','scripts/audit-foundation.sh'],
 ['bash','scripts/audit-geometry.sh'],
 ['bash','scripts/audit-analysis.sh'],
 ['git','diff','--check'],
]
report={'source_manifest_sha256':hashlib.sha256((folder/'source-manifest.json').read_bytes()).hexdigest(),'checks':[]}
for i,cmd in enumerate(steps,1):
    log=evidence/f'{i:02}.log';t=time.monotonic()
    print(f'START {i}/{len(steps)}: '+' '.join(cmd),flush=True)
    with log.open('wb') as f:p=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
    data=log.read_bytes();packed=gzip.compress(data,mtime=0)
    out=log.with_suffix('.log.gz');out.write_bytes(packed);log.unlink()
    report['checks'].append({'command':cmd,'exit_code':p.returncode,'seconds':round(time.monotonic()-t,3),'log':out.name,'sha256':hashlib.sha256(packed).hexdigest(),'uncompressed_sha256':hashlib.sha256(data).hexdigest()})
    (evidence/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'END {i}/{len(steps)}: exit {p.returncode}',flush=True)
    if p.returncode:
        print(data.decode(errors='replace')[-14000:],flush=True);raise SystemExit(p.returncode)
print('VALIDATION PASS: all nine commands succeeded',flush=True)
