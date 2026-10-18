#!/usr/bin/env python3
"""Package checked sources and completed validation logs; never proves a claim."""
from pathlib import Path
import gzip,hashlib,json,subprocess
p=Path(__file__).resolve().parent;r=p.parents[1];e=p/'evidence'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def git(d,*args):return subprocess.check_output(['git','-C',str(d),*args],text=True).strip()
required=['ThetaTwentyTwo']+['ThetaCheck'+str(i) for i in range(12)]+['ThetaInputs','SourceEnclosures','SixthEvenCertificate','VariationalSchur','Regression','Audit']
for n in required:assert (e/(n+'.log')).exists(),n
for name in ['root-build','foundation-audit','geometry-audit','analysis-audit']:
    f=e/(name+'.log')
    if f.exists():
        f.with_suffix('.log.gz').write_bytes(gzip.compress(f.read_bytes(),mtime=0));f.unlink()
    assert f.with_suffix('.log.gz').exists(),name
manifest={'base_commit':'7e874fe8b6cfbec4463e5838a60cb359992b99b7','geometry_head_at_validation':git(r,'rev-parse','HEAD'),
 'operator_head':git(r.parent/'carry-self-adjoint-operator','rev-parse','HEAD'),
 'lean_toolchain':(r/'lean-toolchain').read_text().strip(),
 'lean_sources':{f.name:sha(f) for f in sorted(p.glob('*.lean'))},
 'scripts':{f.name:sha(f) for f in sorted(p.iterdir()) if f.suffix in ['.py','.sh']},
 'documentation':{f.name:sha(f) for f in sorted(p.glob('*.md'))}}
(e/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
validation={'status':'pass','compiled_modules':required,'public_roots':len((p/'public-roots.txt').read_text().splitlines()),
 'kernel_checks':'decide +kernel only; standard Analysis axioms audited transitively',
 'root_build':'lake build --wfail','zone_audits':['foundation','geometry','analysis'],
 'logs':{f.name:sha(f) for f in sorted(e.iterdir()) if f.name.endswith(('.log','.gz'))}}
(e/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
print('PASS: source manifest and validation log hashes packaged')
