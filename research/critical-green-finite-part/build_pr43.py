#!/usr/bin/env python3
"""Recompile unchanged PR43 certificate sources from their published commit.
No historical working tree or source is edited; recovered copies are ignored.
"""
from pathlib import Path
import subprocess,re,json,hashlib
root=Path(__file__).resolve().parent
repo=root.parents[1]
commit='bc7f36f1bd29d0d09fc23778e9e074c2be82123d'
dirs=['research/critical-source-relative-asymptotics','research/critical-source-mixed-readout']
subprocess.run(['git','cat-file','-e',commit],cwd=repo,check=True)
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',commit,'--',*dirs],cwd=repo,text=True).splitlines()
files={Path(p).stem:p for p in paths if p.endswith('.lean') and Path(p).stem!='Audit'}
dest=root/'.cache/pr43';dest.mkdir(parents=True,exist_ok=True)
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
    print('PR43 PASS '+name,flush=True)
build('IntegralOrientation')
(root/'evidence').mkdir(exist_ok=True)
(root/'evidence/pr43-provenance.json').write_text(json.dumps({'commit':commit,'modules':done},indent=2)+'\n')
print(f'Compiled {len(done)} unchanged PR43 modules.',flush=True)
