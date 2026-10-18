from pathlib import Path
import gzip,hashlib,json
base=Path(__file__).resolve().parent
r=json.loads((base/'evidence/validation.json').read_text())
for check in r['checks']:
    assert check['exit_code']==0,check
    data=(base/'evidence'/check['log']).read_bytes()
    assert hashlib.sha256(data).hexdigest()==check['sha256'],check['log']
    if 'uncompressed_sha256' in check:
        assert hashlib.sha256(gzip.decompress(data)).hexdigest()==check['uncompressed_sha256']
print('EVIDENCE PASS:',r['repository'],len(r['checks']),'successful commands and matching log hashes')
