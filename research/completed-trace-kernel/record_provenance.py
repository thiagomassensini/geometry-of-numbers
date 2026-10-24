#!/usr/bin/env python3
"""Record the actual source checkouts and literal files used by this transport."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess
import re

root = Path(__file__).resolve().parent
repo = root.parents[1]
operator = Path('/home/thlinux/carry-self-adjoint-operator')

def git(directory, *args):
    return subprocess.check_output(['git', '-C', str(directory), *args], text=True).strip()

def hashes(directory, paths):
    return {name: hashlib.sha256((directory / name).read_bytes()).hexdigest()
            for name in paths}

data = {
    'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'geometry_base': git(repo, 'rev-parse', 'origin/agent/physical-cauchy-endpoint-domain'),
    'geometry_origin_main': git(repo, 'rev-parse', 'origin/main'),
    'geometry_branch': git(repo, 'branch', '--show-current'),
    'operator_head': git(operator, 'rev-parse', 'HEAD'),
    'operator_status': git(operator, 'status', '--porcelain=v1'),
    'operator_source_sha256': hashes(operator, [
        'CarrySelfAdjointOperator/NativeCauchyLaguerreIsometry.lean',
        'CarrySelfAdjointOperator/NativeCauchyLaguerreHeadTail.lean',
        'CarrySelfAdjointOperator/NativeCauchyLaguerreSources.lean',
        'CarrySelfAdjointOperator/NativePhysicalEndpointEncoder.lean',
        'CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean',
        'CarrySelfAdjointOperator/CompletedNativeRadialChiralMultiplier.lean',
        '.lake/packages/CPFormal/CPFormal/Analytic/CpFiniteGreenPositivity.lean',
        'CarrySelfAdjointOperator/CompletedNativePolarizedTfvdGreenMomentKernel.lean',
        'CarrySelfAdjointOperator/CompletedC3BracketTfvdGreenFactorization.lean',
        'CarrySelfAdjointOperator/CompletedNativeTfvdWronskianMoments.lean',
        'CarrySelfAdjointOperator/CompletedC3FNegFPrimeMixedKernel.lean',
        'CarrySelfAdjointOperator/CompletedGreenForwardDifferenceLimit.lean',
        'CarrySelfAdjointOperator/CompletedC3FullWronskianPolarization.lean',
        'CarrySelfAdjointOperator/CompletedC3KernelMetricCalibration.lean',
        'CarrySelfAdjointOperator/CompletedC3SymplecticCrossingNormalAudit.lean',
        'CarrySelfAdjointOperator/CompletedC3SymplecticCrossingTangentAudit.lean',
        'CarrySelfAdjointOperator/CompletedC3FullWronskianCentralChiralEnergy.lean',
        'CarrySelfAdjointOperator/CompletedC3FullWronskianOperatorCarrier.lean',
        '.lake/packages/NativeCarryC3Crosswalk/NativeCarryC3Crosswalk/EnrichedTfvdPairTransport.lean',
        '.lake/packages/NativeCarryC3Crosswalk/NativeCarryC3Crosswalk/GenuineBracketGreenIdentity.lean',
        '.lake/packages/CPFormal/CPFormal/Analytic/CpFiniteSeededTfvdGreenIdentity.lean',
        '.lake/packages/CPFormal/CPFormal/Analytic/CpFiniteGreenRadial.lean',
    ]),
    'base_research_sha256': hashes(repo, [
        'research/material-theta-tfvd-port/NativePortCalibration.lean',
        'research/native-camera-tail-mellin/NativeCompletion.lean',
        'research/tfvd-four-leg-mellin/MixedLegs.lean',
        'research/tfvd-four-leg-mellin/ReadoutResidual.lean',
        'research/tfvd-four-leg-mellin/C2CellStep.lean',
        'research/tfvd-green-provenance-mellin/CompleteLedger.lean',
        'research/full-source-gram-obstruction/FullCarrierMass.lean',
        'research/full-source-gram-obstruction/NormalizedCrossing.lean',
        'research/full-source-gram-obstruction/NativeGaps.lean',
        'research/native-completed-pairing/CompletedSource.lean',
        'research/native-completed-pairing/SignedFrontier.lean',
    ]),
    'packages': {name: {'path': str(operator / '.lake/packages' / name),
                        'head': git(operator / '.lake/packages' / name, 'rev-parse', 'HEAD')}
                 for name in ['CPFormal', 'NativeCarryC3Crosswalk', 'NativeCarrySpectralWeyl']},
}
mapping={p.stem:p for name in ['physical-cauchy-endpoint-domain','native-completed-pairing',
    'tfvd-green-provenance-mellin','tfvd-four-leg-mellin','native-camera-tail-mellin','material-theta-tfvd-port']
    for p in (root.parent/name).glob('*.lean') if p.stem!='Audit'}
log=(root/'upstream-build.log').read_text()
assert log.rstrip().endswith('Compiled 30 ancestor modules.')
modules=re.findall(r'^UPSTREAM PASS (\w+)$',log,re.M)
assert len(modules)==len(set(modules))==30
base=git(repo,'rev-parse','origin/agent/physical-cauchy-endpoint-domain')
ancestry={}
for name in modules:
    path=mapping[name]
    relative=str(path.relative_to(repo))
    original=subprocess.check_output(['git','-C',str(repo),'show',base+':'+relative])
    digest=hashlib.sha256(path.read_bytes()).hexdigest()
    assert digest==hashlib.sha256(original).hexdigest(), relative
    olean=path.parent/'.cache'/f'{name}.olean'
    assert olean.is_file(), olean
    ancestry[name]={'source':relative,'source_sha256':digest,
        'olean_sha256':hashlib.sha256(olean.read_bytes()).hexdigest()}
data['compiled_ancestor_modules']=ancestry
(root / 'evidence').mkdir(exist_ok=True)
(root / 'evidence/ancestor-build.log').write_text(log)
(root / 'evidence/source-provenance.json').write_text(json.dumps(data, indent=2) + '\n')
print('Source and package provenance recorded.')
