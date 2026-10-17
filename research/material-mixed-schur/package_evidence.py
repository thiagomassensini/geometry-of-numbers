"""Package the successful mixed-jet checks; usage: python3 package_evidence.py LOG_DIR."""
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'research/material-mixed-schur'
LOGS = Path(sys.argv[1])
BASE = 'b711431f9393db9382739af19ea135d9bc11fc0f'

def git(root, *args):
    return subprocess.check_output(['git','-C',str(root),*args],text=True).strip()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

validation=json.loads((LOGS/'validation.json').read_text())
assert len(validation['records']) == 8
assert all(item['exit_code']==0 for item in validation['records'])
evidence=OUT/'evidence'
evidence.mkdir(exist_ok=True)
for item in validation['records']:
    raw=(LOGS/(item['name']+'.log')).read_bytes()
    assert not re.search(r'\berror:|\bwarning:',raw.decode()),item['name']
    target='evidence/'+item['name']+'.log.gz'
    (OUT/target).write_bytes(gzip.compress(raw,mtime=0))
    item['log']=target

core='GeometryOfNumbers/Analysis/CarryMaterialMixedSchur.lean'
comparison='research/material-central-calibration/CanonicalComparison.lean'
roots=[]
for file,ns in [(core,'GeometryOfNumbers.Analysis.'),(comparison,'CarryMaterialMixedSchurComparison.')]:
    source=(ROOT/file).read_text()
    start=0 if file==core else source.index('namespace CarryMaterialMixedSchurComparison')
    added=source[start:]
    assert not re.search(r'\b(sorry|admit|unsafe|native_decide|implemented_by)\b|^axiom\s',added,re.M)
    for m in re.finditer(r'^(def|theorem) (\w+)',added,re.M):
        roots.append(dict(name=ns+m[2],kind=m[1],path=file,line=source[:start+m.start()].count('\n')+1))

footprints={}
for stem in ['analysis','mixed-comparison']:
    text=(LOGS/(stem+'.log')).read_text()
    for name,footprint in re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",text):
        footprints[name]=[x.strip() for x in footprint.split(',') if x.strip()]
allowed={'propext','Classical.choice','Quot.sound'}
for row in roots:
    assert row['name'] in footprints,('missing audit',row['name'])
    assert set(footprints[row['name']]) <= allowed,row
assert len(roots)==48

for file in ['GeometryOfNumbers/Analysis.lean','GeometryOfNumbers/Analysis/Audit.lean',comparison]:
    old=subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+file])
    new=(ROOT/file).read_bytes()
    if file.endswith('/Analysis.lean'):
        assert new==b'import GeometryOfNumbers.Analysis.CarryMaterialMixedSchur\n'+old
    elif file==comparison:
        assert new.startswith(b'import GeometryOfNumbers.Analysis.CarryMaterialMixedSchur\nimport CarrySelfAdjointOperator.NativeSourceSchurThetaIntegral\n'+old)
    else:
        assert new.startswith(old)

unchanged=['lakefile.toml','lake-manifest.json','lean-toolchain',
    'GeometryOfNumbers/Analysis/CarryMaterialProjectiveGlobalReturn.lean',
    'GeometryOfNumbers/Analysis/CarryMaterialProjectiveReturnGreen.lean',
    'GeometryOfNumbers/Analysis/CarryMaterialNullHierarchy.lean',
    'GeometryOfNumbers/Analysis/CarryMaterialClockCentralCoupling.lean',
    'GeometryOfNumbers/Analysis/CompletedBoundaryTransportedClock.lean',
    'research/material-tfvd-projective/CanonicalValveComparison.lean']
subprocess.run(['git','-C',str(ROOT),'diff','--exit-code',BASE,'--',*unchanged],check=True)
subprocess.run(['git','-C',str(ROOT),'diff','--check'],check=True)
(OUT/'new-roots.json').write_text(json.dumps(roots,indent=2)+'\n')
(OUT/'footprints.json').write_text(json.dumps({x['name']:footprints[x['name']] for x in roots},indent=2)+'\n')
validation.update(host='llm',base=BASE,new_roots_audited=len(roots),
    new_theorems=sum(x['kind']=='theorem' for x in roots),axiom_policy=sorted(allowed),
    audit='Lean.collectAxioms transitive types and bodies plus #print axioms per public root',
    preserved_literal_sources=unchanged,old_audit_and_comparison_prefixes_preserved=True,
    positive_block='Only the confluent Taylor block at orders 2 and 4; prior five-source sign reused',
    valve_readout_scope='Ordered central row germs, not a joint kernel extension on the noncentral diagonal',
    numeric_proof_input=False,new_metric=False,new_operator=False,new_physical_source=False,
    strong_global_hilbert_derivatives_added=False,derivatives_exchanged_with_prefix_limits=False,
    all_order_positive_claimed=False,
    source_sha256={f:sha(ROOT/f) for f in [core,comparison]})
(OUT/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
operator=Path('/home/thlinux/carry-self-adjoint-operator')
momentos=Path('/home/thlinux/momentos')
provenance=dict(geometry_base=BASE,operator_head=git(operator,'rev-parse','HEAD'),
    momentos_head=git(momentos,'rev-parse','HEAD'),
    pins_sha256={f:sha(ROOT/f) for f in ['lakefile.toml','lake-manifest.json','lean-toolchain']},
    sources=[dict(path=f,sha256=sha(ROOT/f),last_commit=git(ROOT,'log','-1','--format=%H','--',f)) for f in unchanged[3:]],
    operator_tracked_status=git(operator,'diff','--stat'),momentos_tracked_status=git(momentos,'diff','--stat'),
    branch=git(ROOT,'branch','--show-current'),new_worktrees=False,
    operator_source_files={f:sha(operator/'CarrySelfAdjointOperator'/f) for f in
      ['NativeSourceAllOrderSchur.lean','NativeSourceSchurThetaIntegral.lean',
       'CompletedNativeChiralReturnTenthSourceIntegral.lean','CompletedNativeChiralReturnFiveBoundaryFace.lean',
       'C2OddTfvdTransport.lean','C2OddTfvdTransportAudit.lean']})
(OUT/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
print(json.dumps(dict(roots=len(roots),theorems=validation['new_theorems'],checks=8)))
