#!/usr/bin/env python3
"""Focused replay after strengthening forbidden dependency guards."""
from pathlib import Path
import hashlib,json,subprocess,time
root=Path(__file__).resolve().parent;ev=root/'evidence';ev.mkdir(exist_ok=True)
checks=[]
for label,args,logname in [('strengthened-generate-audit',['python3','generate_audit.py'],'generate-audit.log'),
                         ('strengthened-lean-Audit',['bash','compile_module.sh','Audit'],'lean-Audit.log')]:
 log=ev/logname;initial=ev/('initial-'+logname)
 if log.exists() and not initial.exists():initial.write_bytes(log.read_bytes())
 start=time.monotonic()
 with log.open('w') as f:r=subprocess.run(args,cwd=root,stdout=f,stderr=subprocess.STDOUT)
 checks.append({'label':label,'command':args,'cwd':str(root),'exit_code':r.returncode,
  'seconds':round(time.monotonic()-start,3),'log':'evidence/'+logname,
  'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()})
 (ev/'strengthened-audit.json').write_text(json.dumps({'checks':checks,
  'reason':'Final guards additionally reject the earlier correction sign, eventual orientation, unknown-cutoff monotonicity and old accumulated-tail theorems. Math modules are unchanged; only the dependency audit was strengthened.'},indent=2)+'\n')
 print(label+': exit '+str(r.returncode),flush=True)
 if r.returncode:raise SystemExit(r.returncode)
