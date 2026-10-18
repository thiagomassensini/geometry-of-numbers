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
for file,ns,key in [('GeometryOfNumbers/Analysis/CarryMaterialForcingGreenEnergy.lean','GeometryOfNumbers.Analysis.','library'),('research/completed-green-confluent-balance/SourceBalance.lean','CarryCompletedGreenBalance.','research')]:
    s=(root/file).read_text()
    for kind in ['theorem','def']:
        names={ns+n for n in re.findall(r'^'+kind+r' (\w+)',s,re.M)}
        expected=set(public[key+('_theorems' if kind=='theorem' else '_definitions')])
        assert names==expected,(file,kind,names,expected)
        audit=(root/'GeometryOfNumbers/Analysis/CarryMaterialForcingGreenEnergyAudit.lean').read_text() if key=='library' else (folder/'Audit.lean').read_text()
        for n in names:
            assert '#print axioms '+n+'\n' in audit,n
            assert '\n  '+n+'\n' in audit,n
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',s),file
allowed={'GeometryOfNumbers/Analysis.lean','GeometryOfNumbers/Analysis/Audit.lean','GeometryOfNumbers/Analysis/CarryMaterialForcingGreenEnergy.lean','GeometryOfNumbers/Analysis/CarryMaterialForcingGreenEnergyAudit.lean'}
changed=subprocess.check_output(['git','diff','--name-only',m['base']],cwd=root,text=True).splitlines()
assert all(f in allowed or f.startswith('research/completed-green-confluent-balance/') for f in changed),changed
assert not subprocess.check_output(['git','diff',m['base'],'--','GeometryOfNumbers/Foundation','GeometryOfNumbers/Geometry'],cwd=root)
print('SOURCE PASS: all new roots covered, hashes match, source/metric/pins and user files preserved')
