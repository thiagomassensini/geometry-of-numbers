#!/usr/bin/env python3
"""Read current primary sources; never execute the attached experiment."""
from pathlib import Path
import subprocess,json,base64,hashlib
root=Path(__file__).resolve().parent
path='investigations/jacobi_polynomial_moments_20261024/derivacao_jacobi_momentos_c2.md'
obj=json.loads(subprocess.check_output(['gh','api','repos/thiagomassensini/momentos/contents/'+path],text=True))
data=base64.b64decode(obj['content'])
assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==obj['sha']
record={'jacobi_doc_url':obj['html_url'],'github_blob':obj['sha'],
 'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),
 'local_checkout_has_doc':(Path('/home/thlinux/momentos')/path).exists(),
 'inspection':'Finite Jacobi identities; positive real off-diagonal choice requires positive pivots. Not an upstream source-norm transport.',
 'theta_polynomial_theorem':'CarrySelfAdjointOperator.nativeThetaMomentPolynomial_integral',
 'theta_use':'Existing identity rechecked separately; not a premise of the new domain theorems',
 'index_warning':'Jacobi level is not vertical carry depth or radial regularization index'}
(root/'evidence/context-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: current GitHub Jacobi note verified by immutable blob; finite scope and index distinction recorded; no experiment executed.')
