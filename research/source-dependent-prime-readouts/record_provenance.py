#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
root=Path(__file__).resolve().parent
repo=root.parents[1]
operator=Path('/home/thlinux/carry-self-adjoint-operator')
momentos=Path('/home/thlinux/momentos')
base='d17aba9dfd0aa53a7b677cbb3da0e1e6213e0a54'
def run(args,cwd):return subprocess.check_output(args,cwd=cwd,text=True).strip()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert run(['git','merge-base','HEAD',base],repo)==base
ops=['NativeRealComplementTransport','NativePrimeCarryKernelCalibration',
'CompletedNativeCentralChiralQuotientCurvature','CompletedNativeRadialChiralMultiplier',
'CompletedNativePrimosProjectiveMassCrosswalkAudit','RealQuadratureDomainTransport',
'NativeRealFirstQuadratureNaturality','NativeCauchyLaguerreSources']
cpf=['CpNativeGprePrimeCarryContraction','CpPrimeCarryDefectReadoutCrosswalk',
'CpGenuinePrimeCarryDefectUniformBound','CpNativeGpreTowerNorm','CpGpreTypes']
record={'base':base,'branch':run(['git','branch','--show-current'],repo),
'main':run(['git','rev-parse','origin/main'],repo),
'operator_head':run(['git','rev-parse','HEAD'],operator),
'operator_status':run(['git','status','--porcelain=v1'],operator),
'operator_source_sha256':{n:sha(operator/'CarrySelfAdjointOperator'/f'{n}.lean') for n in ops},
'CPFormal_source_sha256':{n:sha(operator/'.lake/packages/CPFormal/CPFormal/Analytic'/f'{n}.lean') for n in cpf},
'packages':{n:run(['git','rev-parse','HEAD'],operator/'.lake/packages'/n) for n in ['CPFormal','NativeCarryC3Crosswalk','NativeCarrySpectralWeyl']},
'momentos_head':run(['git','rev-parse','HEAD'],momentos),
'momentos_status':run(['git','status','--porcelain=v1'],momentos),
'readme_url':'https://github.com/thiagomassensini/momentos/blob/main/native_jet_exploration/vm_campaign/README.md',
'readme_git_blob':run(['git','hash-object','native_jet_exploration/vm_campaign/README.md'],momentos),
'readme_github_blob':run(['gh','api','repos/thiagomassensini/momentos/contents/native_jet_exploration/vm_campaign/README.md','--jq','.sha'],momentos),
'pr89':json.loads(run(['gh','pr','view','89','--repo','thiagomassensini/geometry-of-numbers','--json','state,isDraft,headRefOid,baseRefName'],repo))}
assert record['readme_git_blob']==record['readme_github_blob']
(root/'evidence/source-provenance.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: original source hashes, pins, PR89 base and current GitHub README recorded.')
