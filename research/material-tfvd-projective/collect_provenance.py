"""Read-only receipt for the actual source and unchanged dependency pins."""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OPERATOR = Path('/home/thlinux/carry-self-adjoint-operator')


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


files = [
    'GeometryOfNumbers/Analysis/RealCarryTfvd.lean',
    'GeometryOfNumbers/Analysis/RealDiscreteProjectiveReconstruction.lean',
    'GeometryOfNumbers/Analysis/CarryMaterialTfvdGreenReadout.lean',
    'GeometryOfNumbers/Analysis/BaseTwoPhysicalEdgeTfvdBridge.lean',
]
op_files = [
    'CarrySelfAdjointOperator/NativeMomentProjectiveValveBridge.lean',
    'CarrySelfAdjointOperator/CompletedC3ValveNaturality.lean',
    'CarrySelfAdjointOperator/CompletedC3ValveGreenNaturality.lean',
    'CarrySelfAdjointOperator/CompletedC3ValveCauchyNaturalityFrontier.lean',
]
receipt = {
    'geometry_base': '31e8ff082cccac2a881180eb3b079824591e22d3',
    'operator_head': git(OPERATOR, 'rev-parse', 'HEAD'),
    'geometry_pins_sha256': {
        f: sha(ROOT / f) for f in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']
    },
    'operator_manifest_sha256': sha(OPERATOR / 'lake-manifest.json'),
    'source_provenance': [
        {'repo': repo, 'path': f, 'sha256': sha(r / f),
         'last_commit': git(r, 'log', '-1', '--format=%H', '--', f)}
        for repo, r, paths in [('geometry-of-numbers', ROOT, files),
                               ('carry-self-adjoint-operator', OPERATOR, op_files)]
        for f in paths
    ],
    'preserved_operator_files': {
        f: sha(OPERATOR / 'CarrySelfAdjointOperator' / f)
        for f in ['C2OddTfvdTransport.lean', 'C2OddTfvdTransportAudit.lean']
    },
    'new_library_sha256': sha(ROOT / 'GeometryOfNumbers/Analysis/CarryMaterialTfvdProjectiveTransport.lean'),
    'new_comparison_sha256': sha(ROOT / 'research/material-tfvd-projective/CanonicalValveComparison.lean'),
    'numerical_proof_input': False,
}
print(json.dumps(receipt, indent=2))
