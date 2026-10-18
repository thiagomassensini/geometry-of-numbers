from pathlib import Path
import gzip,json,hashlib
folder=Path(__file__).resolve().parent;root=folder.parents[1]
r=json.loads((folder/'evidence/validation.json').read_text())
assert len(r['checks'])==10
for c in r['checks']:
    assert c['exit_code']==0,c
    data=(folder/'evidence'/c['log']).read_bytes()
    assert hashlib.sha256(data).hexdigest()==c['sha256'],c['log']
    if c['log'].endswith('.gz'):assert hashlib.sha256(gzip.decompress(data)).hexdigest()==c['uncompressed_sha256']
m=json.loads((folder/'source-manifest.json').read_text())
for category in ['new_files','reused_sources']:
    for f,v in m[category].items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==v['sha256'],f
print('EVIDENCE PASS: ten successful final commands; new/reused source hashes and compressed logs match')
