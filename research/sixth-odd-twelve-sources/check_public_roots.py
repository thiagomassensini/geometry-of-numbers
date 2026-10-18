#!/usr/bin/env python3
"""Inventory and audit every public declaration in this research package."""
from pathlib import Path
import re, sys

sys.dont_write_bytecode=True
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root.parent/'theta-fifth-odd-pattern'))
from check_public_roots import lean_code

def inventory():
    found=[]
    for f in sorted(root.glob('*.lean')):
        if f.stem=='Audit': continue
        code=lean_code(f.read_text())
        namespace=re.search(r'^namespace (\w+)',code,re.M).group(1)
        names=re.findall(r'^(?:(?:noncomputable|protected) )?(?:def|theorem|lemma|inductive|structure|abbrev) ([A-Za-z_][A-Za-z_0-9.\u0080-\uffff]*)',code,re.M)
        found.extend(namespace+'.'+n for n in names)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',code), f
    assert len(found)==len(set(found))
    return found

def main():
    names=inventory()
    if '--generate' in sys.argv:
        (root/'public-roots.txt').write_text(''.join(n+'\n' for n in names).rstrip()+'\n')
        (root/'Audit.lean').write_text('import Regression\n\n'+''.join(
            '#assert_central_comparison_axioms '+n+'\n#print axioms '+n+'\n\n' for n in names).rstrip()+'\n')
    assert (root/'public-roots.txt').read_text()==''.join(n+'\n' for n in names)
    audit=(root/'Audit.lean').read_text()
    for n in names:
        assert '\n#assert_central_comparison_axioms '+n+'\n' in audit, n
        assert '\n#print axioms '+n+'\n' in audit,n
    assert len(re.findall(r'^#assert_central_comparison_axioms ',audit,re.M))==len(names)
    print(f'PASS: {len(names)} public roots, transitive type-and-body guards; no trust escapes')

if __name__=='__main__': main()
