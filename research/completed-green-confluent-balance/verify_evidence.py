from pathlib import Path
import json,hashlib,gzip
folder=Path(__file__).resolve().parent
r=json.loads((folder/'evidence/validation.json').read_text())
assert len(r['checks'])==9
assert hashlib.sha256((folder/'source-manifest.json').read_bytes()).hexdigest()==r['source_manifest_sha256']
for c in r['checks']:
    assert c['exit_code']==0,c
    data=(folder/'evidence'/c['log']).read_bytes()
    assert hashlib.sha256(data).hexdigest()==c['sha256']
    assert hashlib.sha256(gzip.decompress(data)).hexdigest()==c['uncompressed_sha256']
print('EVIDENCE PASS: all nine successful commands, compressed logs and source manifest match')
