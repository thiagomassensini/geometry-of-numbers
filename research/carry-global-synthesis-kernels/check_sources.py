from pathlib import Path
import hashlib,json,re,subprocess
folder=Path(__file__).resolve().parent;root=folder.parents[1]
manifest=json.loads((folder/'source-manifest.json').read_text())
for item in manifest['files']:
    path=root/item['path']
    if hashlib.sha256(path.read_bytes()).hexdigest()!=item['sha256']:raise SystemExit('SOURCE CHANGED: '+str(path))
for item in manifest['pr38_sources']:
    data=subprocess.check_output(['git','show',manifest['pr38_commit']+':'+item['path']],cwd=root)
    assert hashlib.sha256(data).hexdigest()==item['sha256'],item
for path in folder.glob('*.lean'):
    if re.search(r'\b(?:sorry|admit|native_decide|unsafe)\b|^\s*(?:axiom|opaque)\s',path.read_text(),re.M):
        raise SystemExit('UNAPPROVED TRUST CONSTRUCT: '+str(path))
print('PASS: preserved source hashes, frozen PR38 objects, and proof-source scan')
