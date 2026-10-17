"""Package the source-factor Lean validation; run from its repository copy."""
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'research/material-fourth-pivot'
LOGS = Path(sys.argv[1])
BASE = 'c1acf41d0d842861e85ceb50e0a79fd833b530f3'

def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

validation = json.loads((LOGS/'validation.json').read_text())
assert len(validation['records']) == 11
assert all(x['exit_code'] == 0 for x in validation['records'])
(OUT/'evidence').mkdir(exist_ok=True)
for row in validation['records']:
    raw = (LOGS/(row['name']+'.log')).read_bytes()
    assert not re.search(r'\berror:|\bwarning:', raw.decode()), row['name']
    target = 'evidence/'+row['name']+'.log.gz'
    (OUT/target).write_bytes(gzip.compress(raw, mtime=0))
    row['log'] = target

core = 'GeometryOfNumbers/Analysis/CarryMaterialFourthPivot.lean'
comparison = 'research/material-central-calibration/CanonicalComparison.lean'
roots = []
for file, namespace in [(core, 'GeometryOfNumbers.Analysis.'),
                        (comparison, 'CarryMaterialFourthPivotComparison.')]:
    source = (ROOT/file).read_text()
    start = 0 if file == core else source.index('namespace CarryMaterialFourthPivotComparison')
    added = source[start:]
    assert not re.search(r'\b(sorry|admit|unsafe|native_decide|implemented_by)\b|^axiom\s', added, re.M)
    for m in re.finditer(r'^(def|theorem) (\w+)', added, re.M):
        roots.append(dict(name=namespace+m[2], kind=m[1], path=file,
                          line=source[:start+m.start()].count('\n')+1))
assert len(roots) == 27

footprints = {}
for stem in ['analysis', 'fourth-pivot-comparison']:
    text = (LOGS/(stem+'.log')).read_text()
    for name, footprint in re.findall(
            r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", text):
        footprints[name] = [x.strip() for x in footprint.split(',') if x.strip()]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for row in roots:
    assert row['name'] in footprints, ('missing axiom audit', row['name'])
    assert set(footprints[row['name']]) <= allowed, row

# Every pre-existing source identity and audit prefix remains literal.
for file in ['GeometryOfNumbers/Analysis.lean', 'GeometryOfNumbers/Analysis/Audit.lean', comparison]:
    old = subprocess.check_output(['git', '-C', str(ROOT), 'show', BASE+':'+file])
    new = (ROOT/file).read_bytes()
    if file == 'GeometryOfNumbers/Analysis.lean':
        assert new == b'import GeometryOfNumbers.Analysis.CarryMaterialFourthPivot\n'+old
    elif file == comparison:
        assert new.startswith(b'import GeometryOfNumbers.Analysis.CarryMaterialFourthPivot\n'+old)
    else:
        assert new.startswith(old)

unchanged = ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
    'GeometryOfNumbers/Analysis/CarryMaterialSourceFactor.lean',
    'GeometryOfNumbers/Analysis/CarryMaterialMixedSchur.lean',
    'GeometryOfNumbers/Analysis/CarryMaterialProjectiveGlobalReturn.lean',
    'GeometryOfNumbers/Analysis/CarryMaterialProjectiveReturnGreen.lean',
    'GeometryOfNumbers/Analysis/CarryMaterialNullHierarchy.lean',
    'GeometryOfNumbers/Analysis/CarryMaterialClockCentralCoupling.lean',
    'GeometryOfNumbers/Analysis/CompletedBoundaryTransportedClock.lean',
    'research/material-tfvd-projective/CanonicalValveComparison.lean']
subprocess.run(['git', '-C', str(ROOT), 'diff', '--exit-code', BASE, '--', *unchanged], check=True)
subprocess.run(['git', '-C', str(ROOT), 'diff', '--check'], check=True)

(OUT/'new-roots.json').write_text(json.dumps(roots, indent=2)+'\n')
(OUT/'footprints.json').write_text(json.dumps({x['name']: footprints[x['name']] for x in roots}, indent=2)+'\n')
validation.update(host='llm', base=BASE, new_roots_audited=len(roots),
    new_theorems=sum(x['kind']=='theorem' for x in roots), axiom_policy=sorted(allowed),
    audit='Lean.collectAxioms transitive types and bodies plus #print axioms per public root',
    preserved_literal_sources=unchanged, old_audit_and_comparison_prefixes_preserved=True,
    positive_block='No new positive block: next source sign remains open',
    native_hankel_factor='No additional unconditional factor at the new order',
    result='Fourth polarized sewing, critical energy and equivalence to original theta integral estimate',
    new_pivot_sign_proved=False, source_estimate_proved=False, numeric_proof_input=False,
    new_metric=False, new_operator=False, new_physical_source=False,
    source_sha256={f: sha(ROOT/f) for f in [core, comparison,
                                          'research/material-fourth-pivot/Regression.lean']})
(OUT/'validation.json').write_text(json.dumps(validation, indent=2)+'\n')

operator = Path('/home/thlinux/carry-self-adjoint-operator')
momentos = Path('/home/thlinux/momentos')
old_provenance = json.loads((ROOT/'research/material-source-factor/provenance.json').read_text())
for f, expected in old_provenance['operator_source_files'].items():
    assert sha(operator/'CarrySelfAdjointOperator'/f) == expected, ('operator source changed', f)
provenance = dict(geometry_base=BASE, operator_head=git(operator, 'rev-parse', 'HEAD'),
    momentos_head=git(momentos, 'rev-parse', 'HEAD'),
    pins_sha256={f: sha(ROOT/f) for f in unchanged[:3]},
    sources=[dict(path=f, sha256=sha(ROOT/f), last_commit=git(ROOT, 'log', '-1', '--format=%H', '--', f))
             for f in unchanged[3:]],
    branch=git(ROOT, 'branch', '--show-current'), new_worktrees=False,
    operator_status=git(operator, 'status', '--short'), momentos_status=git(momentos, 'status', '--short'),
    operator_source_files={f: sha(operator/'CarrySelfAdjointOperator'/f) for f in
        ['CanonicalLDLWhitening.lean', 'NativeSourceAllOrderSchur.lean',
         'NativeSourceSchurThetaIntegral.lean', 'CompletedNativeChiralReturnFourteenthSourceIntegral.lean',
         'CompletedNativeChiralReturnSevenBoundaryFace.lean',
         'C2OddTfvdTransport.lean', 'C2OddTfvdTransportAudit.lean']})
(OUT/'provenance.json').write_text(json.dumps(provenance, indent=2)+'\n')
(OUT/'diagnostic.json').write_bytes((LOGS/'diagnostic.json').read_bytes())
print(json.dumps(dict(roots=len(roots), theorems=validation['new_theorems'], checks=11)))
