"""Read-only source inventory on llm; does not discover or alter definitions."""
import hashlib
import json
import subprocess
from pathlib import Path

geometry = Path('/home/thlinux/geometry-material-residual-study')
carry = Path('/home/thlinux/carry-self-adjoint-operator')
groups = {
    'geometry-of-numbers': (geometry, [
        'Foundation/FirstLocalReturnCapacity', 'Foundation/EmergentResidualTower',
        'Foundation/QuadraticMassCompatibility', 'Foundation/FoundationalHalfScalingCapstone',
        'Geometry/ResidualTowerDepth', 'Geometry/CenterLegReflection',
        'Geometry/CenteredSecondDifference', 'Geometry/CarryCenterLegCrosswalk',
        'Geometry/BalancedCarryDepthCrosswalk', 'Geometry/IntegerCameraIncidence',
        'Analysis/CarryMaterialResidualResponse', 'Analysis/CarryMaterialNormalizedResponse', 'Analysis/CompletedBoundaryTransportedClock', 'Analysis/CompletedMaterialGradientStrongClock', 'Analysis/CarryMaterialGeneralTransport', 'Analysis/CarryMaterialTfvdGreenReadout', 'Analysis/CarryMaterialSourceRealization', 'Analysis/CarryMaterialCameraTransport', 'Analysis/BaseTwoPhysicalEdgeTfvdBridge', 'Analysis/BaseTwoPhysicalEdgeC2Address', 'Analysis/C2RealFiberTfvdIncidence', 'Analysis/CompleteVerticalObservationGram', 'Analysis/SeparatedCenterClockObstruction', 'Analysis/PrimeCameraProvenance', 'Analysis/IntegerIncidenceEnergy',
        'Analysis/RealDepthMass', 'Analysis/RealQuadraticAmplitude',
        'Analysis/RealCriticalDepthState', 'Analysis/C2FiberRealDynamics',
        'Analysis/RealCarryTfvd', 'Analysis/CompleteVerticalObservationGram',
        'Analysis/CanonicalGreenMomentJetSeam', 'Analysis/C2GlobalPhysicalBranchCanary',
        'Analysis/FiniteMaterialClockJets', 'Analysis/FiniteNativeMaterialClock',
        'Analysis/BaseTwoExactHeadTailCompletion', 'Analysis/BaseTwoCompletedGradientSignalLift',
        'Analysis/BaseTwoCompletedBoundaryLimit', 'Analysis/BaseTwoCompletedBoundaryHilbert',
        'Analysis/BaseTwoCompletedBoundaryDynamics', 'Analysis/BaseTwoCompletedVectorLiftGate',
        'Analysis/BaseTwoCanonicalDressingMoments', 'Analysis/BaseTwoCanonicalArchimedeanDressing', 'Analysis/BaseTwoCanonicalCameraDressing', 'Analysis/BaseTwoCompletedSignalRegularity',
    ]),
    'carry-self-adjoint-operator': (carry, [
        'NativeCompletedSourcePositiveReduction', 'NativeCompletedSourcePositiveReductionJet', 'NativeCompletedSourceTwoPositiveChannels', 'NativeCompletedSourceThirdPositiveChannel', 'NativeCompletedSourceFourthPositiveChannel', 'NativeCompletedSourceReductionChain', 'NativeCompletedDividedVectorResponse', 'NativeCompletedDividedVectorSeries', 'NativeCompletedVectorGreenReadout', 'PrimeDepthNormalizedResponseVectorJet', 'CompletedC3FullWronskianOperatorCarrier', 'CompletedGreenRealKernelClosure', 'CompletedNativeAmbientCentralCurvatureDecision', 'CompletedC3CoisometricAmbientMomentGate', 'CompletedC3AmbientRadialTiltSamplePositivity', 'CompletedC3AllCutoffHilbertState', 'CompletedOperatorCharacteristic', 'DivisionFreeGreenConfinement', 'CompletedNativeRealWeylMoments', 'CompletedNativeHerglotzFourthOrderGate', 'CompletedC3KernelMetricCalibration', 'CompletedNativeCentralProductDressingAudit', 'C2GeometryNativeSourceBridge', 'RealQuadratureDomainTransport', 'RealMaterialPhaseConnection',
        'NativeRealComplementTransport', 'NativeRealFirstQuadratureNaturality',
        'CompletedNativeSourceThreeSectorSewing', 'CompletedNativeHPGateAudit',
        'CompletedGreenForwardDifferenceGramBridge', 'CompletedGreenMomentJets', 'CompletedGreenJetCoefficientRecurrence', 'BR2CenterLegMomentKernel',
    ]),
}

def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args], text=True).strip()

result = {}
for name, (repo, modules) in groups.items():
    prefix = 'GeometryOfNumbers' if name == 'geometry-of-numbers' else 'CarrySelfAdjointOperator'
    files = []
    for module in modules:
        rel = f'{prefix}/{module}.lean'
        files.append({'path': rel,
                      'sha256': hashlib.sha256((repo / rel).read_bytes()).hexdigest(),
                      'last_touch_commit': git(repo, 'log', '-1', '--format=%H', '--', rel)})
    result[name] = {'base_commit': git(repo, 'rev-parse', 'HEAD'), 'files': files,
                    'manifest_sha256': hashlib.sha256((repo / 'lake-manifest.json').read_bytes()).hexdigest()}
result['base_pull_requests'] = [json.loads(subprocess.check_output(
    ['gh', 'pr', 'view', number, '--repo', repo, '--json',
     'number,title,url,state,mergeCommit,mergedAt'], text=True))
    for repo, number in [('thiagomassensini/geometry-of-numbers', '1'), ('thiagomassensini/geometry-of-numbers', '2'), ('thiagomassensini/geometry-of-numbers', '3'), ('thiagomassensini/geometry-of-numbers', '4'), ('thiagomassensini/geometry-of-numbers', '5'), ('thiagomassensini/carry-self-adjoint-operator', '105'),
                         ('thiagomassensini/carry-self-adjoint-operator', '106')]]
mom = Path('/home/thlinux/momentos')
result['momentos'] = {'base_commit': git(mom, 'rev-parse', 'HEAD'), 'files': []}
for rel in ['AUDITORIA_CORRECTED_MOMENTS_VS_CANONICAL_RECURRENCE.md', 'native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/coefficients.json', 'native_jet_exploration/auditoria_corrected_vs_canonical/stage_B/coefficients.json']:
    result['momentos']['files'].append({'path':rel,'sha256':hashlib.sha256((mom/rel).read_bytes()).hexdigest(),'last_touch_commit':git(mom,'log','-1','--format=%H','--',rel)})
result['new_roots'] = json.loads((geometry/'research/material-residual-study/new-roots.json').read_text())

operator_doc = carry/'docs/completed-native-ambient-central-curvature-decision.md'
result['ambient_antecedent'] = {'doc_sha256':hashlib.sha256(operator_doc.read_bytes()).hexdigest(),'doc_last_touch_commit':git(carry,'log','-1','--format=%H','--','docs/completed-native-ambient-central-curvature-decision.md')}
cp = carry/'.lake/packages/CPFormal'
result['common_gradient_dependency'] = {'commit':git(cp,'rev-parse','HEAD'),'files':[]}
for rel in ['CPFormal/Analytic/CpFiniteGreen.lean','CPFormal/Analytic/CpFiniteDirichletChart.lean']:
    result['common_gradient_dependency']['files'].append({'path':rel,'sha256':hashlib.sha256((cp/rel).read_bytes()).hexdigest()})
result['task_sources'] = []
for rel in ['GeometryOfNumbers/Analysis/CarryMaterialResidualResponse.lean', 'GeometryOfNumbers/Analysis.lean', 'GeometryOfNumbers/Analysis/Audit.lean', 'research/material-central-calibration/CanonicalComparison.lean', 'research/material-residual-study/Regression.lean', 'docs/MATERIAL_RESIDUAL_STUDY.md']:
    result['task_sources'].append({'path': rel, 'sha256': hashlib.sha256((geometry/rel).read_bytes()).hexdigest()})
print(json.dumps(result, indent=2))
