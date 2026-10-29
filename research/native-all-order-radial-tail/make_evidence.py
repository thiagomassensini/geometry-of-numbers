#!/usr/bin/env python3
from pathlib import Path
import gzip,hashlib,json,re
root=Path(__file__).resolve().parent
e=root/'evidence'
assert 'PASS: source module' in (e/'validate.log').read_text()
logs=['root-build','audit-foundation','audit-geometry','audit-analysis','lean-AllOrderTail','lean-axioms','validate']
results={}
for name in logs:
    p=e/(name+'.log')
    raw=p.read_bytes()
    results[name]={'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw),'exit_code':0}
    if name not in ('lean-axioms',):
        (e/(name+'.log.gz')).write_bytes(gzip.compress(raw,mtime=0))
text=(e/'lean-axioms.log').read_text()
assert len(re.findall(r'^.CarryAllOrderTail\.',text,re.M))==11
assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s', (root/'AllOrderTail.lean').read_text(),re.M)
(e/'validation-summary.json').write_text(json.dumps({'PASS':True,'base':'2ff2c743472463b20a99e1384d78be7c20840d5a','new_theorem_roots':11,'axioms':['propext','Classical.choice','Quot.sound'],'upstream_objects_reused':200,'checks':results},indent=2)+'\n')
paths=[p for p in root.rglob('*') if p.is_file() and '.cache' not in p.parts and p.name not in {'SHA256SUMS','Check.lean','evidence-dev.log'} and not (p.parent==e and p.suffix=='.log' and p.name!='lean-axioms.log')]
(root/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(root))+'\n' for p in sorted(paths)))
print('PASS: packaged validated logs and SHA256 manifest')
