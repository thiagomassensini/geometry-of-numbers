from pathlib import Path
import re,json,subprocess,hashlib
root=Path(__file__).resolve().parents[2]
base='59e53d863f4ef0ad998b0eb19fd3891c9839cc35'
folder=Path(__file__).resolve().parent
public=json.loads((folder/'public-roots.json').read_text())
expected={
 'GeometryOfNumbers/Analysis/MaterialClockKrylovGap.lean':('GeometryOfNumbers.Analysis.MaterialClockKrylovGap.',public['library']),
 'research/structural-native-krylov-gap/CanonicalClockGap.lean':('CarryStructuralKrylov.',[n for n in public['research'] if not n.split('.')[-1].startswith('regression_')]),
 'research/structural-native-krylov-gap/Regression.lean':('CarryStructuralKrylov.',[n for n in public['research'] if n.split('.')[-1].startswith('regression_')])}
def code_only(s):
    chars=[]; depth=0;i=0
    while i<len(s):
        if s[i:i+2]=='/-':depth+=1;i+=2
        elif depth and s[i:i+2]=='-/':depth-=1;i+=2
        elif depth:i+=1
        elif s[i:i+2]=='--':
            j=s.find('\n',i);i=len(s) if j<0 else j
        else:chars.append(s[i]);i+=1
    assert depth==0
    return ''.join(chars)
for path,(ns,roots) in expected.items():
    text=(root/path).read_text()
    names={ns+n for n in re.findall(r'^theorem (\w+)',text,re.M)}
    assert names==set(roots),(path,names,set(roots))
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',code_only(text)),path
    audit=(root/'GeometryOfNumbers/Analysis/MaterialClockKrylovGapAudit.lean').read_text() if '/Analysis/' in path else (folder/'Audit.lean').read_text()
    for n in names:
        assert '#print axioms '+n in audit,n
        assert '\n  '+n+'\n' in audit,n
allowed={'GeometryOfNumbers/Analysis.lean','GeometryOfNumbers/Analysis/Audit.lean','GeometryOfNumbers/Analysis/MaterialClockKrylovGap.lean','GeometryOfNumbers/Analysis/MaterialClockKrylovGapAudit.lean'}
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=root,text=True).splitlines()
assert all(f in allowed or f.startswith('research/structural-native-krylov-gap/') for f in changed),changed
for file in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
    assert (root/file).read_bytes()==subprocess.check_output(['git','show',base+':'+file],cwd=root),file
operator=root.parent/'carry-self-adjoint-operator'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=operator,text=True).strip()=='bfeb10fd2425400fa38139903d12bf0599f02e53'
for file,h in {'C2OddTfvdTransport.lean':'5bfe06e8d15432c4d6cab6719dc22a0376019243f3e896329ea9ab9dd7458cb0','C2OddTfvdTransportAudit.lean':'b6f05d0241058885da362b5cb20d3968d704a667da3ffc443714a69f3564623c'}.items():
    assert hashlib.sha256((operator/'CarrySelfAdjointOperator'/file).read_bytes()).hexdigest()==h,file
print('SOURCE PASS: 22 public theorems audited; original mathematics, pins and operator user files preserved')
