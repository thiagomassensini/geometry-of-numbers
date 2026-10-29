#!/usr/bin/env python3
"""Ensure new source roots are registered and original input files/pins are intact."""
from pathlib import Path
import subprocess,re,json,hashlib
root=Path(__file__).resolve().parents[2]
kind='geometry' if root.name=='geometry-of-numbers' else 'operator'
base={'geometry':'59e53d863f4ef0ad998b0eb19fd3891c9839cc35','operator':'045369f6dedcb2e75e9aefed1d12c9f73b9a2532'}[kind]
file={'geometry':'GeometryOfNumbers/Analysis/CriticalBranchComplementTransport.lean','operator':'CarrySelfAdjointOperator/CriticalBranchNativeObstructions.lean'}[kind]
source=(root/file).read_text()
# Strip Lean nested block comments and line comments before token checks.
def code_only(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if s[i:i+2]=='/-': depth+=1; i+=2
        elif depth and s[i:i+2]=='-/': depth-=1; i+=2
        elif depth: i+=1
        elif s[i:i+2]=='--':
            j=s.find('\n',i); i=len(s) if j<0 else j
        else: out.append(s[i]); i+=1
    assert depth==0
    return ''.join(out)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',code_only(source))
names=re.findall(r'^(?:def|theorem) (\w+)',source,re.M)
auditfile={'geometry':'GeometryOfNumbers/Analysis/CriticalBranchComplementAudit.lean','operator':'CarrySelfAdjointOperator/CriticalBranchNativeAudit.lean'}[kind]
audit=(root/auditfile).read_text()
namespace={'geometry':'GeometryOfNumbers.Analysis.CriticalBranchComplement.','operator':'CarrySelfAdjointOperator.CriticalBranchNativeAudit.'}[kind]
for n in names:
    assert '#print axioms '+namespace+n in audit,n
    assert re.search(r'^  '+re.escape(namespace+n)+r'$',audit,re.M),n
if kind=='operator':
    registered={x['qualified'] for x in json.loads((root/'audit/theorem-registry.json').read_text())['theorems']}
    assert all(namespace+n in registered for n in names)
    expected={'C2OddTfvdTransport.lean':'5bfe06e8d15432c4d6cab6719dc22a0376019243f3e896329ea9ab9dd7458cb0',
      'C2OddTfvdTransportAudit.lean':'b6f05d0241058885da362b5cb20d3968d704a667da3ffc443714a69f3564623c'}
    for f,h in expected.items(): assert hashlib.sha256((root/'CarrySelfAdjointOperator'/f).read_bytes()).hexdigest()==h
    allowed={'CarrySelfAdjointOperator.lean','CarrySelfAdjointOperator/Audit.lean','audit/theorem-registry.json'}
else:
    allowed={'GeometryOfNumbers/Analysis.lean','GeometryOfNumbers/Analysis/Audit.lean'}
changed=set(subprocess.check_output(['git','diff','--name-only',base],cwd=root,text=True).splitlines())
# New files become tracked on commit; both states are accepted.
allowed|={file,auditfile}
assert all(f in allowed or f.startswith('research/critical-branch-') for f in changed),changed-allowed
for f in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
    old=subprocess.check_output(['git','show',base+':'+f],cwd=root)
    assert (root/f).read_bytes()==old,f
# All new proof declarations have explicit audits; no old mathematical file changed.
print('SOURCE PASS:',kind,len(names),'public roots; original modules, pins and user files preserved')
