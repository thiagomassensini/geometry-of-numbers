#!/usr/bin/env python3
"""Record the actual source checkouts and literal files used by this transport."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess

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
    'geometry_base': git(repo, 'rev-parse', 'origin/agent/full-source-gram-obstruction'),
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
(root / 'evidence').mkdir(exist_ok=True)
(root / 'evidence/source-provenance.json').write_text(json.dumps(data, indent=2) + '\n')
print('Source and package provenance recorded.')
