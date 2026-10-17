import hashlib
import json
import subprocess
from pathlib import Path

def git(p, *args):
    return subprocess.check_output(['git', '-C', str(p), *args], text=True).strip()

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

geo = Path('/home/thlinux/geometry-of-numbers')
operator = Path('/home/thlinux/carry-self-adjoint-operator')
mom = Path('/home/thlinux/momentos')
data = {
    'geometry_base': git(geo, 'rev-parse', 'HEAD'),
    'operator_head': git(operator, 'rev-parse', 'HEAD'),
    'momentos_head': git(mom, 'rev-parse', 'HEAD'),
    'geometry_status': git(geo, 'status', '--short', '--branch'),
    'operator_status': git(operator, 'status', '--short', '--branch'),
    'momentos_status': git(mom, 'status', '--short', '--branch'),
    'geometry_pins_sha256': {n: sha(geo/n) for n in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain')},
    'operator_manifest_sha256': sha(operator/'lake-manifest.json'),
    'operator_preserved_files': {n: sha(operator/'CarrySelfAdjointOperator'/n)
        for n in ('C2OddTfvdTransport.lean', 'C2OddTfvdTransportAudit.lean')},
    'finite_diagnostic_input_sha256': sha(mom/'native_jet_exploration/auditoria_corrected_vs_canonical/stage_B/coefficients.json'),
    'shared_packages': {x['name']: x['rev'] for x in json.loads((geo/'lake-manifest.json').read_text())['packages']
        if x['name'] in ('mathlib', 'GreenFrame')},
    'lean_toolchain': (geo/'lean-toolchain').read_text().strip(),
    'new_worktree': '/home/thlinux/geometry-material-theta-tail',
    'new_branch': 'agent/material-theta-tail',
}
print(json.dumps(data, indent=2))
