#!/usr/bin/env python3
"""Record original sources and immutable eight-module upstream build."""
from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parent
repo=root.parents[1]
operator=Path('/home/thlinux/carry-self-adjoint-operator')
base='8a287232a55709fb79847033143978f555fa10b4'
def run(args,cwd=repo):return subprocess.check_output(args,cwd=cwd,text=True).strip()
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
names=['completed-trace-kernel','physical-cauchy-endpoint-domain']
files={p.stem:p for name in names for p in (root.parent/name).glob('*.lean') if p.stem!='Audit'}
log=(root/'evidence/upstream-build.log').read_text()
modules=re.findall(r'^UPSTREAM PASS (\w+)$',log,re.M)
assert len(modules)==len(set(modules))==8
assert log.rstrip().endswith('Compiled 8 ancestor modules.')
ancestry={}
for name in modules:
    path=files[name]; rel=str(path.relative_to(repo))
    original=subprocess.check_output(['git','show',base+':'+rel],cwd=repo)
    assert hashlib.sha256(original).hexdigest()==sha(path),rel
    olean=path.parent/'.cache'/f'{name}.olean'
    ancestry[name]={'source':rel,'sha256':sha(path),'olean_sha256':sha(olean)}
primos=Path('/home/thlinux/primos')
prime_paths=['CPFormal/Analytic/CpPrimeTowerCarryMangoldtBridge.lean','CPFormal/Analytic/CpPrimeDepthLogWaveBridge.lean']
prime_commit='298a54f7be6111b6f83c4fee4de3bf3fed9f4a95'
prime_sources={}
for path in prime_paths:
    data=subprocess.check_output(['git','show',prime_commit+':'+path],cwd=primos)
    prime_sources[path]=hashlib.sha256(data).hexdigest()
pr36='8da373522add9b9423c4ecb04e271f096d405165'
pr36path='research/structural-native-krylov-gap/CanonicalClockGap.lean'
pr36data=subprocess.check_output(['git','show',pr36+':'+pr36path],cwd=repo)
source_paths=['CompletedNativeProjectiveChiralCarrier','CompletedNativeProjectiveChiralForwardDifference',
'CompletedNativeChiralBoundaryJetTransport','CompletedNativeChiralJetStorageTransport',
'CompletedNativeRadialChiralMultiplier','CompletedGreenForwardDifferenceVectorLimit',
'CompletedNativeRealWeylMoments','CompletedNativeRadialTiltSamplePositivity']
record={'base':base,'main':run(['git','rev-parse','origin/main']),
'branch':run(['git','branch','--show-current']),'operator_head':run(['git','rev-parse','HEAD'],operator),
'operator_status':run(['git','status','--porcelain=v1'],operator),'ancestors':ancestry,
'operator_sources_sha256':{name:sha(operator/'CarrySelfAdjointOperator'/f'{name}.lean') for name in source_paths},
'old_source_box':{'source':'research/sixth-odd-twelve-sources/OddSourceBoxes.lean',
'sha256':sha(root.parent/'sixth-odd-twelve-sources/OddSourceBoxes.lean')},
'primos_head':run(['git','rev-parse','HEAD'],primos),'primos_status':run(['git','status','--porcelain=v1'],primos),
'primos47_merge':prime_commit,'primos47_sources_sha256':prime_sources,
'pr36_read_only':{'commit':pr36,'source':pr36path,'sha256':hashlib.sha256(pr36data).hexdigest(),
'note':'Read for provenance only; not imported. Inequality rebuilt from original boxes in PrimeTowerCanary.'},
'packages':{n:run(['git','rev-parse','HEAD'],operator/'.lake/packages'/n) for n in ['CPFormal','NativeCarryC3Crosswalk','NativeCarrySpectralWeyl']}}
for number in [41,79]:
    record[f'pr{number}']=json.loads(run(['gh','pr','view',str(number),'--repo','thiagomassensini/geometry-of-numbers','--json','state,isDraft,headRefOid,baseRefName']))
record['primos47']=json.loads(run(['gh','pr','view','47','--repo','thiagomassensini/primos','--json','state,mergeCommit,mergedAt']))
(root/'evidence/source-provenance.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: eight immutable ancestor sources, source boxes, original operators, PR41/79 and primos47 recorded.')
