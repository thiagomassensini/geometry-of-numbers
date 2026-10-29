from pathlib import Path
import hashlib,json,re

folder=Path(__file__).resolve().parent;root=folder.parents[1]
manifest=json.loads((folder/'source-manifest.json').read_text())
for record in manifest['files']:
    path=root/record['path']
    actual=hashlib.sha256(path.read_bytes()).hexdigest()
    if actual!=record['sha256']:raise SystemExit('SOURCE CHANGED: '+str(path))
for path in [root/'GeometryOfNumbers/Analysis/CarryMaterialReadoutQuotient.lean',folder/'CameraObservation.lean',folder/'MaterialCameraSeparation.lean']:
    if re.search(r'\b(?:sorry|admit|native_decide|unsafe)\b|^\s*(?:axiom|opaque)\s',path.read_text(),re.M):
        raise SystemExit('UNAPPROVED TRUST CONSTRUCT: '+str(path))
print('PASS: source hashes and trust-construct scan')
