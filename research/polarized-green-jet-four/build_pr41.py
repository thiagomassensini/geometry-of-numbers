#!/usr/bin/env python3
"""Recompile unchanged PR41 certificate sources from their published commit.
No historical working tree or source is edited; recovered copies are ignored.
"""
from pathlib import Path
import subprocess,re,json,hashlib
root=Path(__file__).resolve().parent
repo=root.parents[1]
commit='ee56930a2c30456cfbd214a29bb31b12d3977204'
dirs=['research/native-moment-orthogonalization-audit']
subprocess.run(['git','cat-file','-e',commit],cwd=repo,check=True)
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',commit,'--',*dirs],cwd=repo,text=True).splitlines()
files={Path(p).stem:p for p in paths if p.endswith('.lean') and Path(p).stem!='Audit'}
dest=root/'.cache/pr41';dest.mkdir(parents=True,exist_ok=True)
done={}
def build(name):
    if name in done:return
    path=files[name]
    data=subprocess.check_output(['git','show',commit+':'+path],cwd=repo)
    source=dest/(name+'.lean');source.write_bytes(data)
    for dep in re.findall(r'^import (\S+)',data.decode(),re.M):
        if dep in files:build(dep)
    subprocess.run(['bash',str(root/'compile_module.sh'),name,str(source)],check=True)
    done[name]={'source':path,'source_sha256':hashlib.sha256(data).hexdigest(),
                'olean_sha256':hashlib.sha256((dest/'.cache'/f'{name}.olean').read_bytes()).hexdigest()}
    print('PR41 PASS '+name,flush=True)
build('SchurLogic')
(root/'evidence').mkdir(exist_ok=True)
(root/'evidence/pr41-provenance.json').write_text(json.dumps({'commit':commit,'modules':done},indent=2)+'\n')
print(f'Compiled {len(done)} unchanged PR41 modules.',flush=True)
