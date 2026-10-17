"""Package only successful task checks and audit their recorded footprints."""
import gzip
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'research/material-tfvd-projective'
BASE = '31e8ff082cccac2a881180eb3b079824591e22d3'

checks = [
    ('focused-build', 'lake build GeometryOfNumbers.Analysis.CarryMaterialTfvdProjectiveTransport --wfail', 'Build completed successfully (8785 jobs).'),
    ('full-build', 'lake build --wfail', 'Build completed successfully (8836 jobs).'),
    ('foundation-audit', 'bash scripts/audit-foundation.sh', 'PASS: foundation build and empty-axiom audit.'),
    ('geometry-audit', 'bash scripts/audit-geometry.sh', 'PASS: tower-depth relation has empty footprint'),
    ('analysis-audit', 'bash scripts/audit-analysis.sh', 'PASS: real analysis build and standard-axiom audit'),
    ('comparison', 'bash scripts/audit-material-projective-comparison.sh /home/thlinux/carry-self-adjoint-operator', 'PASS: same scalar valve, physical curvature and native mass defect'),
    ('regression', 'lake env lean -DwarningAsError=true research/material-tfvd-projective/Regression.lean', 'carryMaterialClock_reduced_green_ledger'),
    ('previous-comparison-regression', 'bash scripts/audit-material-central-comparison.sh /home/thlinux/carry-self-adjoint-operator', 'PASS: scalar source identification, central defect and normalized-kernel obstruction'),
]

evidence = OUT / 'evidence'
evidence.mkdir(exist_ok=True)
for stem, _, expected in checks:
    raw = (OUT / (stem + '.log')).read_bytes()
    text = raw.decode()
    assert expected in text, (stem, 'missing success marker')
    assert 'error:' not in text and 'warning:' not in text, stem
    (evidence / (stem + '.log.gz')).write_bytes(gzip.compress(raw, mtime=0))

root_rows = []
inputs = [
    ('GeometryOfNumbers/Analysis/CarryMaterialTfvdProjectiveTransport.lean', 'GeometryOfNumbers.Analysis.'),
    ('research/material-tfvd-projective/CanonicalValveComparison.lean', 'CarryMaterialProjectiveComparison.'),
]
for file, ns in inputs:
    source = (ROOT / file).read_text()
    assert not re.search(r'\b(sorry|admit|unsafe|native_decide|implemented_by)\b|^axiom\s', source, re.M)
    for match in re.finditer(r'^(def|theorem|structure) (\w+)', source, re.M):
        root_rows.append({'name': ns + match[2], 'kind': match[1], 'path': file,
                          'line': source[:match.start()].count('\n') + 1})
    if ns.startswith('GeometryOfNumbers'):
        struct = next(x for x in root_rows if x['kind'] == 'structure')
        for field in ['mk', 'seed', 'fibers', 'residual', 'globalReturn']:
            root_rows.append({'name': ns + 'CarryMaterialProjectiveLedger.' + field,
                              'kind': 'constructor' if field == 'mk' else 'projection',
                              'path': file, 'line': struct['line']})

footprints = {}
for stem in ['analysis-audit', 'comparison']:
    text = (OUT / (stem + '.log')).read_text()
    for name, footprint in re.findall(
            r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", text):
        footprints[name] = [x.strip() for x in footprint.split(',') if x.strip()]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for row in root_rows:
    name = row['name']
    assert name in footprints, ('missing audit', name)
    assert set(footprints[name]) <= allowed, (name, footprints[name])

for file in ['GeometryOfNumbers/Analysis.lean', 'GeometryOfNumbers/Analysis/Audit.lean']:
    old = subprocess.check_output(['git', '-C', str(ROOT), 'show', BASE + ':' + file])
    new = (ROOT / file).read_bytes()
    if file.endswith('Analysis.lean'):
        assert new == b'import GeometryOfNumbers.Analysis.CarryMaterialTfvdProjectiveTransport\n' + old
    else:
        assert new.startswith(old)

subprocess.run(['git', '-C', str(ROOT), 'diff', '--check'], check=True)
unchanged = ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
             'research/material-central-calibration/CanonicalComparison.lean',
             'GeometryOfNumbers/Analysis/CarryMaterialClockCentralCoupling.lean']
subprocess.run(['git', '-C', str(ROOT), 'diff', '--exit-code', BASE, '--', *unchanged], check=True)

(OUT / 'new-roots.json').write_text(json.dumps(root_rows, indent=2) + '\n')
(OUT / 'footprints.json').write_text(json.dumps({x['name']: footprints[x['name']] for x in root_rows}, indent=2) + '\n')
validation = {
    'host': 'llm', 'base': BASE,
    'checks': [{'command': command, 'exit_code': 0, 'log': 'evidence/' + stem + '.log.gz'}
               for stem, command, _ in checks],
    'new_roots_audited': len(root_rows),
    'new_theorems': sum(x['kind'] == 'theorem' for x in root_rows),
    'axiom_policy': sorted(allowed),
    'audit': 'Lean.collectAxioms transitive type and body, plus #print axioms per root',
    'unchanged_literal_sources': unchanged,
    'existing_audit_prefix_preserved': True,
    'existing_analysis_imports_preserved': True,
    'new_metric': False, 'new_operator': False, 'new_source': False,
    'numeric_proof_input': False,
    'open': ['joint canonical pairing identification', 'normalized Green residual positivity',
             'all-order hierarchy positivity'],
    'narrow_obstruction': 'direct unit-core real depth-mass identification at time zero',
}
(OUT / 'validation.json').write_text(json.dumps(validation, indent=2) + '\n')
print(json.dumps({'roots': len(root_rows), 'theorems': validation['new_theorems'], 'checks': len(checks)}))
