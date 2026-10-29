from pathlib import Path
import re,json,subprocess,hashlib
folder=Path(__file__).resolve().parent;root=folder.parents[1]
m=json.loads((folder/'source-manifest.json').read_text())
public=json.loads((folder/'public-roots.json').read_text())
operator=root.parent/'carry-self-adjoint-operator'
for category,base in [('new_files',root),('reused_sources',root),('operator_files',operator)]:
    for f,h in m[category].items():
        assert hashlib.sha256((base/f).read_bytes()).hexdigest()==h,(category,f)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=operator,text=True).strip()==m['operator_head']
for file in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
    assert (root/file).read_bytes()==subprocess.check_output(['git','show',m['base']+':'+file],cwd=root),file
for file,ns,key in [('GeometryOfNumbers/Analysis/'+name+'.lean','GeometryOfNumbers.Analysis.CarryScale.','library') for name in ['CarryScaleGeometry','MomentScaleElimination','MomentScaleHeight','LogDerivativeScale']]+[('research/carry-scale-covariance/NativeScaleSeam.lean','CarryNativeScaleSeam.','research')]:
    s=(root/file).read_text()
    audit=(root/'GeometryOfNumbers/Analysis/CarryScaleCovarianceAudit.lean').read_text() if key=='library' else (folder/'Audit.lean').read_text()
    for kind in ['theorem','def']:
        names={ns+n for n in re.findall(r'^'+kind+r' (\w+)',s,re.M)}
        expected=set(public.get(key+('_theorems' if kind=='theorem' else '_definitions'),[]))
        assert names <= expected,(file,kind,names,expected)
        for n in names:
            assert '#print axioms '+n+'\n' in audit,n
            assert '\n  '+n+'\n' in audit,n
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',s),file
reference=json.loads((folder/'evidence/reference-local.json').read_text())
assert reference['exit_code']==0
assert reference['script_sha256']==hashlib.sha256((folder/'reference_test.py').read_bytes()).hexdigest()
allowed={'GeometryOfNumbers/Analysis.lean','GeometryOfNumbers/Analysis/Audit.lean'} | {f for f in m['new_files'] if f.startswith('GeometryOfNumbers/')}
changed=subprocess.check_output(['git','diff','--name-only',m['base']],cwd=root,text=True).splitlines()
assert all(f in allowed or f.startswith('research/carry-scale-covariance/') for f in changed),changed
assert not subprocess.check_output(['git','diff',m['base'],'--','GeometryOfNumbers/Foundation','GeometryOfNumbers/Geometry'],cwd=root)
print('SOURCE PASS: all new roots covered, hashes match, source/metric/pins and user files preserved')
