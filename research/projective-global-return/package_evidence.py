"""Package successful Lean checks and audit every new declaration root."""
import gzip
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'research/projective-global-return'
BASE = '4d84edfd53e7e6d5cd087c6b1c7c1349e99dce05'

checks = [
    ('focused-build', 'lake build GeometryOfNumbers.Analysis.CarryMaterialProjectiveReturnGreen --wfail', 'Build completed successfully (8795 jobs).'),
    ('full-build', 'lake build --wfail', 'Build completed successfully (8838 jobs).'),
    ('foundation-audit', 'bash scripts/audit-foundation.sh', 'PASS: foundation build and empty-axiom audit.'),
    ('geometry-audit', 'bash scripts/audit-geometry.sh', 'PASS: tower-depth relation has empty footprint'),
    ('analysis-audit', 'bash scripts/audit-analysis.sh', 'PASS: real analysis build and standard-axiom audit'),
    ('comparison', 'bash scripts/audit-material-central-comparison.sh /home/thlinux/carry-self-adjoint-operator', 'PASS: scalar source identification, central defect and normalized-kernel obstruction'),
    ('regression', 'lake env lean -DwarningAsError=true research/projective-global-return/Regression.lean', 'carryMaterialClock_reduced_green_ledger'),
    ('previous-valve-comparison', 'bash scripts/audit-material-projective-comparison.sh /home/thlinux/carry-self-adjoint-operator', 'PASS: same scalar valve, physical curvature and native mass defect'),
]

evidence = OUT / 'evidence'
evidence.mkdir(exist_ok=True)
for stem, _, expected in checks:
    raw = (OUT / (stem + '.log')).read_bytes()
    text = raw.decode()
    assert expected in text, (stem, 'missing success marker')
    assert 'error:' not in text and 'warning:' not in text, stem
    (evidence / (stem + '.log.gz')).write_bytes(gzip.compress(raw, mtime=0))

roots = []
sources = [
    ('GeometryOfNumbers/Analysis/CarryMaterialProjectiveGlobalReturn.lean', 'GeometryOfNumbers.Analysis.'),
    ('GeometryOfNumbers/Analysis/CarryMaterialProjectiveReturnGreen.lean', 'GeometryOfNumbers.Analysis.'),
    ('research/material-central-calibration/CanonicalComparison.lean', 'CarryMaterialValveGlobalReturnComparison.'),
]
for file, namespace in sources:
    source = (ROOT / file).read_text()
    if namespace.startswith('GeometryOfNumbers'):
        assert not re.search(r'\b(sorry|admit|unsafe|native_decide|implemented_by)\b|^axiom\s', source, re.M)
    for match in re.finditer(r'^(def|theorem) (\w+)', source, re.M):
        if namespace.startswith('CarryMaterialValve') and not match[2].startswith('material_valve_'):
            continue
        roots.append({'name': namespace + match[2], 'kind': match[1], 'path': file,
                      'line': source[:match.start()].count('\n') + 1})

footprints = {}
for stem in ['analysis-audit', 'comparison']:
    text = (OUT / (stem + '.log')).read_text()
    for name, footprint in re.findall(
            r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", text):
        footprints[name] = [x.strip() for x in footprint.split(',') if x.strip()]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for row in roots:
    assert row['name'] in footprints, ('missing audit', row['name'])
    assert set(footprints[row['name']]) <= allowed, row

for file in ['GeometryOfNumbers/Analysis.lean', 'GeometryOfNumbers/Analysis/Audit.lean',
             'research/material-central-calibration/CanonicalComparison.lean']:
    old = subprocess.check_output(['git', '-C', str(ROOT), 'show', BASE + ':' + file])
    new = (ROOT / file).read_bytes()
    if file.endswith('Analysis.lean'):
        assert new == b'import GeometryOfNumbers.Analysis.CarryMaterialProjectiveReturnGreen\n' + old
    elif file.endswith('CanonicalComparison.lean'):
        assert new.startswith(b'import GeometryOfNumbers.Analysis.CarryMaterialProjectiveReturnGreen\n' + old)
    else:
        assert new.startswith(old)

unchanged = ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
             'GeometryOfNumbers/Analysis/CarryMaterialTfvdProjectiveTransport.lean',
             'GeometryOfNumbers/Analysis/CompletedBoundaryTransportedClock.lean',
             'GeometryOfNumbers/Analysis/CarryMaterialClockCentralCoupling.lean',
             'research/material-tfvd-projective/CanonicalValveComparison.lean']
subprocess.run(['git', '-C', str(ROOT), 'diff', '--exit-code', BASE, '--', *unchanged], check=True)
subprocess.run(['git', '-C', str(ROOT), 'diff', '--check'], check=True)
(OUT / 'new-roots.json').write_text(json.dumps(roots, indent=2) + '\n')
(OUT / 'footprints.json').write_text(json.dumps({x['name']: footprints[x['name']] for x in roots}, indent=2) + '\n')
validation = {
    'host': 'llm', 'base': BASE,
    'checks': [{'command': command, 'exit_code': 0, 'log': 'evidence/' + stem + '.log.gz'}
               for stem, command, _ in checks],
    'new_roots_audited': len(roots), 'new_theorems': sum(x['kind'] == 'theorem' for x in roots),
    'axiom_policy': sorted(allowed),
    'audit': 'Lean.collectAxioms transitive type and body, plus #print axioms per root',
    'unchanged_literal_sources': unchanged,
    'old_audit_and_comparison_prefixes_preserved': True,
    'cutoff_filter': 'Filter.atTop ×ˢ Filter.atTop on Nat × Nat',
    'second_order_clock_domain_claimed': False,
    'separate_infinite_green_trace_sums_used': False,
    'singular_normalization_divided_out': False,
    'new_metric': False, 'new_operator': False, 'new_source': False, 'numeric_proof_input': False,
    'open': ['structural sign of the full normalized signed balance', 'canonical residual positivity'],
    'source_sha256': {file: hashlib.sha256((ROOT / file).read_bytes()).hexdigest() for file, _ in sources},
}
(OUT / 'validation.json').write_text(json.dumps(validation, indent=2) + '\n')
print(json.dumps({'roots': len(roots), 'theorems': validation['new_theorems'], 'checks': len(checks)}))
