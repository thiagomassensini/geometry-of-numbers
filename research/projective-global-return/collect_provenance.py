"""Read-only provenance and preservation receipt for the polarized return."""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OPERATOR = Path('/home/thlinux/carry-self-adjoint-operator')
MOMENTOS = Path('/home/thlinux/momentos')
BASE = '4d84edfd53e7e6d5cd087c6b1c7c1349e99dce05'


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


files = [
    'GeometryOfNumbers/Analysis/CarryMaterialTfvdProjectiveTransport.lean',
    'GeometryOfNumbers/Analysis/CompletedBoundaryTransportedClock.lean',
    'GeometryOfNumbers/Analysis/BaseTwoPhysicalEdgeTfvdBridge.lean',
    'GeometryOfNumbers/Analysis/CarryMaterialTfvdGreenReadout.lean',
    'GeometryOfNumbers/Analysis/CarryMaterialNormalizedResponse.lean',
    'GeometryOfNumbers/Analysis/CarryMaterialCompanionGreenTransport.lean',
    'GeometryOfNumbers/Analysis/CarryMaterialClockCentralCoupling.lean',
]
receipt = {
    'geometry_base': BASE,
    'operator_head': git(OPERATOR, 'rev-parse', 'HEAD'),
    'momentos_head': git(MOMENTOS, 'rev-parse', 'HEAD'),
    'geometry_pins_sha256': {f: sha(ROOT / f) for f in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']},
    'operator_manifest_sha256': sha(OPERATOR / 'lake-manifest.json'),
    'source_provenance': [
        {'path': f, 'sha256': sha(ROOT / f),
         'last_commit': git(ROOT, 'log', '-1', '--format=%H', '--', f)} for f in files
    ],
    'previous_external_comparison_sha256': hashlib.sha256(subprocess.check_output(
        ['git', '-C', str(ROOT), 'show', BASE + ':research/material-central-calibration/CanonicalComparison.lean'])).hexdigest(),
    'preserved_operator_files': {
        f: sha(OPERATOR / 'CarrySelfAdjointOperator' / f)
        for f in ['C2OddTfvdTransport.lean', 'C2OddTfvdTransportAudit.lean']
    },
    'numerical_proof_input': False,
    'new_worktree': '/home/thlinux/geometry-projective-global-return',
    'new_branch': 'agent/projective-global-return',
}
print(json.dumps(receipt, indent=2))
