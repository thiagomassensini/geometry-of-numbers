#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
root=Path(__file__).resolve().parent
repo=root.parents[1]
operator=Path('/home/thlinux/carry-self-adjoint-operator')
base='457ea144d33d0b376a5c589b06ef1695e6d14adb'
def run(args,cwd):return subprocess.check_output(args,cwd=cwd,text=True).strip()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert run(['git','merge-base','HEAD',base],repo)==base
upstream=json.loads((root/'evidence/upstream.json').read_text())
assert upstream['base']==base
for name,e in upstream['modules'].items():
 p=repo/e['source'];assert sha(p)==e['source_sha256']
 data=subprocess.check_output(['git','show',base+':'+e['source']],cwd=repo)
 assert hashlib.sha256(data).hexdigest()==e['source_sha256']
 assert sha(p.parent/'.cache'/f'{name}.olean')==e['olean_sha256']
geometry=['C2BranchIsometryCanary','C2GlobalPhysicalBranchCanary','C2GlobalGreenBridge']
geom={}
for n in geometry:
 p=repo/'GeometryOfNumbers/Analysis'/f'{n}.lean'
 rel=str(p.relative_to(repo));assert p.read_bytes()==subprocess.check_output(['git','show',base+':'+rel],cwd=repo)
 geom[rel]=sha(p)
ops=['CompletedNativeRadialChiralMultiplier','NativePrimeCarryKernelCalibration','NativeRealComplementTransport','NativeSourceThetaMomentPolynomials']
record={'base':base,'branch':run(['git','branch','--show-current'],repo),
'main':run(['git','rev-parse','origin/main'],repo),'unchanged_upstream':upstream,
'geometry_vertical_sources_sha256':geom,
'operator_head':run(['git','rev-parse','HEAD'],operator),
'operator_status':run(['git','status','--porcelain=v1'],operator),
'operator_source_sha256':{n:sha(operator/'CarrySelfAdjointOperator'/f'{n}.lean') for n in ops},
'packages':{n:run(['git','rev-parse','HEAD'],operator/'.lake/packages'/n) for n in ['CPFormal','NativeCarryC3Crosswalk','NativeCarrySpectralWeyl']},
'pr90':json.loads(run(['gh','pr','view','90','--repo','thiagomassensini/geometry-of-numbers','--json','state,isDraft,headRefOid,baseRefName'],repo))}
(root/'evidence/source-provenance.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: unchanged PR90 modules, existing vertical isometries, operator sources and pins verified.')
