from pathlib import Path
import hashlib,json,gzip,re,subprocess
folder=Path(__file__).resolve().parent;root=folder.parents[1]
for item in json.loads((folder/'proof-source-manifest.json').read_text())['files']:
    assert hashlib.sha256((root/item['path']).read_bytes()).hexdigest()==item['sha256'],item
report=json.loads((folder/'evidence/validation.json').read_text())
assert report['source_manifest_sha256']==hashlib.sha256((folder/'source-manifest.json').read_bytes()).hexdigest()
assert len(report['checks'])==14
texts={}
for item in report['checks']:
    assert item['exit_code']==0,item
    raw=(folder/'evidence'/item['log']).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==item['sha256']
    unpacked=gzip.decompress(raw)
    assert hashlib.sha256(unpacked).hexdigest()==item['uncompressed_sha256']
    texts[item['log']]=unpacked.decode()
assert 'PR38 source compiled read-only at 16de0ef478afb1c95c16edfe8153ac80dc035b71' in texts['05.log.gz']
assert 'roots: 41; type/body closure: 6814; foundational guard passed' in texts['09.log.gz']
roots=json.loads((folder/'public-roots.json').read_text())
assert len(roots['new'])==38 and len(roots['regressions'])==3
actual=[]
for file,namespace in [('GreenSynthesis','CarryGlobalGreenSynthesis'),('CameraBudget','CarryGlobalCameraBudget'),('ScaleCompatibility','CarryGlobalScaleCompatibility')]:
    actual += [namespace+'.'+n for n in re.findall(r'^(?:theorem|def|abbrev)\s+(\w+)',(folder/(file+'.lean')).read_text(),re.M)]
assert actual==roots['new']
subprocess.run(['python3',str(folder/'check_sources.py')],check=True)
print('PASS: fourteen exit-zero checks, sealed proof sources and logs, frozen PR38 compilation, 38 new roots and three regressions')
