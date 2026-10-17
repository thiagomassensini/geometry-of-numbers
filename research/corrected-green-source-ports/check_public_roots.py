#!/usr/bin/env python3
"""Check that every published public declaration has a type/body axiom guard."""
from pathlib import Path
import re
root = Path(__file__).resolve().parent
excluded = {'Audit', 'DumpNodeCache', 'DumpTaylorCache', 'EvaluateCached'}
modules = [p for p in sorted(root.glob('*.lean'))
           if p.stem not in excluded and not p.stem.startswith(('Diagnostic', 'Kernel'))]
names = []
for path in modules:
    names += re.findall(r'^(?:(?:noncomputable|protected) )?(?:def|theorem|lemma|inductive|structure|abbrev) ([A-Za-z_][A-Za-z_0-9.\u0080-\uffff]*)', path.read_text(), re.M)
assert len(names) == len(set(names)), 'Duplicate public root'
expected = ''.join('CarryCorrectedGreenPorts.' + name + '\n' for name in names)
assert (root / 'public-roots.txt').read_text() == expected, 'Stale public root inventory'
audit = (root / 'Audit.lean').read_text()
for name in names:
    assert '\n#assert_central_comparison_axioms ' + name + '\n' in audit, name
    assert '\n#print axioms ' + name + '\n' in audit, name
assert len(re.findall(r'^#assert_central_comparison_axioms ', audit, re.M)) == len(names)
print(f'PASS: {len(names)} public roots have explicit transitive type-and-body guards')
