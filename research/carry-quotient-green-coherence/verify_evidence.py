from pathlib import Path
import json,hashlib,gzip,re,subprocess

folder=Path(__file__).resolve().parent;root=folder.parents[1]
report=json.loads((folder/'evidence/validation.json').read_text())
for item in json.loads((folder/'proof-source-manifest.json').read_text())['files']:
    assert hashlib.sha256((root/item['path']).read_bytes()).hexdigest()==item['sha256'],item
assert report['source_manifest_sha256']==hashlib.sha256((folder/'source-manifest.json').read_bytes()).hexdigest()
assert len(report['checks'])==11
texts={}
for item in report['checks']:
    assert item['exit_code']==0,item
    raw=(folder/'evidence'/item['log']).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==item['sha256']
    unpacked=gzip.decompress(raw)
    assert hashlib.sha256(unpacked).hexdigest()==item['uncompressed_sha256']
    texts[item['log']]=unpacked.decode()
assert 'roots: 18; type/body closure: 3481; foundational guard passed' in texts['02.log.gz']
assert 'roots: 20; type/body closure: 4972; foundational guard passed' in texts['05.log.gz']
regression=json.loads(texts['06.log.gz'])
assert regression['status']=='PASS_FINITE_REGRESSION'
assert len(regression['checks'])==8
roots=json.loads((folder/'public-roots.json').read_text())
lib=(root/'GeometryOfNumbers/Analysis/CarryMaterialReadoutQuotient.lean').read_text()
actual_lib=['GeometryOfNumbers.Analysis.'+n for n in re.findall(r'^theorem\s+(\w+)',lib,re.M)]
assert roots['library']==actual_lib
assert len(roots['library'])==18 and len(roots['research'])==20
subprocess.run(['python3',str(folder/'check_sources.py')],check=True)
print('PASS: eleven exit-zero checks, log hashes, 38 audited roots, source manifest, and finite regressions')
