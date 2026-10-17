from pathlib import Path
import datetime, hashlib, json, re, shutil, subprocess
root=Path('/home/thlinux/geometry-of-numbers')
folder=root/'research/material-pivot-certificate'
evidence=folder/'evidence';evidence.mkdir(exist_ok=True)
log=Path('/tmp/carry-pivot-candidate-final.log').read_text()
assert 'error:' not in log
source=(folder/'CanonicalPivotCertificate.lean').read_text()
assert not re.search(r'^\s*(axiom|sorry|admit)\b',source,re.M)
roots=[]
for ns,section in [('CarryMaterialThetaCertificate',source.split('-- BEGIN GENERATED')[0]),('CarryMaterialPivotCertificate',source.split('-- BEGIN GENERATED')[1])]:
 for name in re.findall(r'^#assert_central_comparison_axioms (\w+)',section,re.M):roots.append(ns+'.'+name)
assert len(roots)==17 and len(set(roots))==17
footprints={}
for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S):
 if name in roots:
  a=[s.strip() for s in axioms.split(',') if s.strip()]
  assert set(a)<= {'propext','Classical.choice','Quot.sound'}
  footprints[name]=a
for name in re.findall(r"'([^']+)' does not depend on any axioms",log):
 if name in roots:footprints[name]=[]
assert set(footprints)==set(roots),(set(roots)-set(footprints))
classic=json.loads(Path('/tmp/carry-pivot-full-validation/validation.json').read_text())
assert len(classic['records'])==11 and all(x['exit_code']==0 for x in classic['records'])
assert 'PASS: exact endpoint replay' in Path('/tmp/carry-pivot-certificate-check.log').read_text()
assert 'PASS: all source/moment/pivot intervals contain their refined enclosures' in Path('/tmp/carry-pivot-certificate-check.log').read_text()
fresh=json.loads(Path('/tmp/carry-pivot-fresh-coarse.json').read_text());saved=json.loads((folder/'certificate.json').read_text())
assert {k:v for k,v in fresh.items() if k!='seconds'}=={k:v for k,v in saved.items() if k!='seconds'}
for src,dest in [('/tmp/carry-pivot-candidate-final.log','certificate-lean.log'),('/tmp/carry-pivot-coarse-run.log','coarse.log'),('/tmp/carry-pivot-refined-run.log','refined.log'),('/tmp/carry-pivot-certificate-check.log','rational-checks.log'),('/tmp/carry-pivot-fresh-refined.json','refined-certificate.json')]:shutil.copyfile(src,evidence/dest)
raw_logs={}
for r in classic['records']:
 p=Path('/tmp/carry-pivot-full-validation')/(r['name']+'.log')
 raw_logs[r['name']]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,tail=p.read_text().splitlines()[-3:])
(evidence/'footprints.json').write_text(json.dumps(footprints,indent=2)+'\n')
(evidence/'public-roots.json').write_text(json.dumps(roots,indent=2)+'\n')
record=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base='ac0fe970edeac46a43085960d93d85d7cc4aa17e',operator='045369f6dedcb2e75e9aefed1d12c9f73b9a2532',records=classic['records']+[dict(name='new-pivot-certificate',command=['lean','-DwarningAsError=true','research/material-pivot-certificate/CanonicalPivotCertificate.lean'],result='PASS',public_guards_verified=17,base_module='compiled CanonicalComparison; unchanged source and matching dependency pins'),dict(name='rational-source-certificate',grid=[64,128],taylor_order=16,result='PASS',recorded_certificate_reproduced=True,refined_containment=True,cache='diagnostic only')],public_roots=len(roots),regression_log_metadata=raw_logs,source_box_lean_status='NOT_PROVED',pivot_lean_status='CONDITIONAL_ON_EXPLICIT_THETA_BOX',analytic_certificate_status='EXACT_RATIONAL_COMPUTATION_WITH_WRITTEN_ANALYTIC_JUSTIFICATION',files={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(folder.glob('*')) if p.is_file() and p.name!='package_evidence.py'})
(evidence/'validation.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: packaged 11 regressions, new module, two rational grids and 17 kernel axiom guards')
