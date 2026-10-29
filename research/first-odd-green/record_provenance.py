#!/usr/bin/env python3
"""Record original sources and immutable eight-module upstream build."""
from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parent
repo=root.parents[1]
operator=Path('/home/thlinux/carry-self-adjoint-operator')
base='365d91c60d49740a4c31153e90d620f424eec8fe'
def run(args,cwd=repo):return subprocess.check_output(args,cwd=cwd,text=True).strip()
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
names=['finite-green-crossing','mean-contrast-green','radial-green-intertwiner','radial-common-refinement','completed-trace-kernel','physical-cauchy-endpoint-domain']
files={p.stem:p for name in names for p in (root.parent/name).glob('*.lean') if p.stem!='Audit'}
log=(root/'evidence/upstream-build.log').read_text()
modules=re.findall(r'^UPSTREAM PASS (\w+)$',log,re.M)
assert len(modules)==len(set(modules))
assert log.rstrip().endswith(f'Compiled {len(modules)} ancestor modules.')
ancestry={}
for name in modules:
    path=files[name]; rel=str(path.relative_to(repo))
    original=subprocess.check_output(['git','show',base+':'+rel],cwd=repo)
    assert hashlib.sha256(original).hexdigest()==sha(path),rel
    olean=path.parent/'.cache'/f'{name}.olean'
    ancestry[name]={'source':rel,'sha256':sha(path),'olean_sha256':sha(olean)}
source_paths=['CompletedC3FullWronskianCentralChiralEnergy','CompletedGreenDiagonalClosure','NativePhysicalGreenResolvent','NativeIntervalMultiplier','NativeCompletedFiniteGreenResidual','NativeScalarZetaIdentification','CompletedNativeProjectiveChiralCarrier','CompletedNativeProjectiveChiralForwardDifference',
'CompletedNativeChiralBoundaryJetTransport','CompletedNativeChiralJetStorageTransport',
'CompletedNativeRadialChiralMultiplier','CompletedGreenForwardDifferenceVectorLimit',
'CompletedNativeRealWeylMoments','CompletedNativeRadialTiltSamplePositivity']
record={'base':base,'main':run(['git','rev-parse','origin/main']),
'branch':run(['git','branch','--show-current']),'operator_head':run(['git','rev-parse','HEAD'],operator),
'operator_status':run(['git','status','--porcelain=v1'],operator),'ancestors':ancestry,
'operator_sources_sha256':{name:sha(operator/'CarrySelfAdjointOperator'/f'{name}.lean') for name in source_paths},
'packages':{n:run(['git','rev-parse','HEAD'],operator/'.lake/packages'/n) for n in ['CPFormal','NativeCarryC3Crosswalk','NativeCarrySpectralWeyl']}}
for number in [41,81,82,83,84]:
    record[f'pr{number}']=json.loads(run(['gh','pr','view',str(number),'--repo','thiagomassensini/geometry-of-numbers','--json','state,isDraft,headRefOid,baseRefName']))
(root/'evidence/source-provenance.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: immutable ancestor sources, original operators and PR41/81 recorded.')
