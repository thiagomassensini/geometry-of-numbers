"""Read-only inventory at the validated source commits."""
import hashlib
import json
import subprocess
from pathlib import Path

g = Path(__file__).resolve().parents[2]
c = Path('/home/thlinux/carry-self-adjoint-operator')
m = Path('/home/thlinux/momentos')

def git(p, *args):
    return subprocess.check_output(['git', '-C', str(p), *args], text=True).strip()

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

modules = {
    'geometry': (g, 'GeometryOfNumbers/', [
        'Analysis/CarryMaterialNullHierarchy', 'Analysis/CarryMaterialThirdNullSector',
        'Analysis/CarryMaterialSecondNullSector', 'Analysis/CarryMaterialResidualPositiveTransport',
        'Analysis/CarryMaterialSourceRealization', 'Analysis/CarryMaterialCameraTransport',
        'Analysis/CarryMaterialTfvdGreenReadout', 'Analysis/CarryMaterialNormalizedResponse']),
    'operator': (c, 'CarrySelfAdjointOperator/', [
        'AllOrderLogJetLedger', 'NativeMomentProjectiveValveBridge',
        'CompletedNativeSixthOrderThetaPositivity', 'CompletedNativeXiThetaMoments',
        'CompletedNativeHerglotzFourthOrderGate', 'NativeSourceThetaMomentPolynomials', 'NativeSourceSchurThetaMasses',
        'NativeSourceSchurThetaIntegral', 'NativeSourceThetaGreenTransport',
        'CompletedNativeXiCosineKernel', 'CompletedNativeRealWeylMoments',
        'CompletedNativeLogCoefficientMajorant', 'CompletedNativeChiralReturnFiveBoundaryFace',
        'CompletedNativeChiralReturnSixBoundaryFace', 'CompletedNativeChiralReturnSevenBoundaryFace',
        'CompletedNativeChiralReturnEightBoundaryFace',
        'CompletedNativeChiralReturnTenthSourceIntegral',
        'CompletedNativeChiralReturnTwelfthSourceIntegral',
        'CompletedNativeChiralReturnFourteenthSourceIntegral',
        'CompletedNativeThetaTenthSourceCertificate', 'CompletedNativeThetaTwelfthSourceCertificate',
        'CompletedNativeThetaFourteenthSourceCertificate',
        'CompletedNativeChiralReturnBoundaryCoefficientProvenance',
        'PrimeDepthGeometricMomentRecurrence', 'NativeCompletedSourceFourthPositiveChannel'])}
out = {}
for name, (p, prefix, paths) in modules.items():
    files = []
    for x in paths:
        rel = prefix+x+'.lean'
        files.append({'path': rel, 'sha256': sha(p/rel),
                      'last_touch_commit': git(p, 'log', '-1', '--format=%H', '--', rel)})
    out[name] = {'head': git(p, 'rev-parse', 'HEAD'), 'files': files,
                 'manifest_sha256': sha(p/'lake-manifest.json'),
                 'shared_pins': {x['name']: x['rev'] for x in json.loads((p/'lake-manifest.json').read_text())['packages'] if x['name'] in ('mathlib', 'GreenFrame')},
                 'lean_toolchain': (p/'lean-toolchain').read_text().strip()}
assert out['geometry']['shared_pins'] == out['operator']['shared_pins']
assert out['geometry']['lean_toolchain'] == out['operator']['lean_toolchain']
out['momentos'] = {'head': git(m, 'rev-parse', 'HEAD'), 'status': git(m, 'status', '--porcelain'),
                   'note': 'Existing untracked investigations preserved; no new numerical experiment.'}
out['preserved_user_files'] = [{'path': str(c/r), 'sha256': sha(c/r)} for r in (
    'CarrySelfAdjointOperator/C2OddTfvdTransport.lean',
    'CarrySelfAdjointOperator/C2OddTfvdTransportAudit.lean')]
out['base_pr'] = json.loads(subprocess.check_output(['gh','pr','view','13','--repo',
    'thiagomassensini/geometry-of-numbers','--json','number,title,url,state,mergeCommit'],text=True))
out['prior_provenance'] = {'path': 'research/material-hierarchy-sign/provenance.json',
                          'sha256': sha(g/'research/material-hierarchy-sign/provenance.json')}
paths = ['research/material-central-calibration/CanonicalComparison.lean',
         'research/material-pole-dominance/new-roots.json',
         'docs/MATERIAL_POLE_DOMINANCE.md', 'scripts/audit-material-central-comparison.sh']
out['task_sources'] = [{'path': r, 'sha256': sha(g/r)} for r in paths]
out['collection_note'] = 'Before task commit; new sources identified by SHA256. Other source modules unchanged.'
inp=m/'native_jet_exploration/auditoria_corrected_vs_canonical/stage_B/coefficients.json'
out['numerical_input']={'path':str(inp),'sha256':sha(inp),'status':'Finite numerical input; not a proof of infinite source pole data.'}
out['consulted_open_reference_pr']=json.loads(subprocess.check_output(['gh','pr','view','62','--repo','thiagomassensini/carry-self-adjoint-operator','--json','number,title,url,headRefOid,files'],text=True))
print(json.dumps(out, indent=2))
