#!/usr/bin/env python3
"""Hash final sources/logs only after all required commands returned zero."""
from pathlib import Path
import gzip,hashlib,json,subprocess
p=Path(__file__).resolve().parent;r=p.parents[1];e=p/'evidence'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def git(d,*args):return subprocess.check_output(['git','-C',str(d),*args],text=True).strip()
required=['provenance', 'public-inventory', 'SourceTwentySix', 'SourceCoefficients', 'CenteredLogRecurrence', 'CenteredReferenceData', 'CenteredEvaluation', 'CenteredMomentBoxes', 'EvenTrialData', 'EvenSeventhCertificate', 'RelativeResidual', 'Regression', 'Audit', 'root-build', 'foundation-audit', 'geometry-audit', 'analysis-audit', 'final-provenance']
rows=json.loads((e/'build-results.json').read_text())
assert [x['name'] for x in rows]==required
assert all(x['exit_code']==0 for x in rows)
for name in ['root-build','foundation-audit','geometry-audit','analysis-audit']:
    f=e/(name+'.log')
    if f.exists():
        f.with_suffix('.log.gz').write_bytes(gzip.compress(f.read_bytes(),mtime=0));f.unlink()
    assert f.with_suffix('.log.gz').exists(),name
manifest={'base_commit':'59e53d863f4ef0ad998b0eb19fd3891c9839cc35',
 'geometry_head_at_validation':git(r,'rev-parse','HEAD'),
 'operator_head':git(r.parent/'carry-self-adjoint-operator','rev-parse','HEAD'),
 'momentos_head':git(r.parent/'momentos','rev-parse','HEAD'),
 'lean_toolchain':(r/'lean-toolchain').read_text().strip(),
 'lean_sources':{f.name:sha(f) for f in sorted(p.glob('*.lean'))},
 'scripts':{f.name:sha(f) for f in sorted(p.iterdir()) if f.suffix in ['.py','.sh']},
 'documentation':{f.name:sha(f) for f in sorted(p.iterdir()) if f.suffix=='.md' or f.name=='public-roots.txt'}}
(e/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
validation={'status':'pass','commands':rows,'public_roots':len((p/'public-roots.txt').read_text().splitlines()),
 'historical_dependencies':'reused after manifests, pins and commit verification; not freshly rebuilt',
 'kernel_checks':'decide +kernel; no custom axioms or native_decide; transitive type-and-body guards',
 'logs':{f.name:sha(f) for f in sorted(e.iterdir()) if f.name.endswith(('.log','.gz'))},
 'data':{f.name:sha(f) for f in sorted(e.iterdir()) if f.suffix=='.json' and f.name not in ['source-manifest.json','validation.json']}}
(e/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
print('PASS: exact source, data, command and log manifest',flush=True)
