#!/usr/bin/env python3
"""Compile actual immutable ancestor sources in dependency order."""
from pathlib import Path
import subprocess
import re
root=Path(__file__).resolve().parent
names=['first-odd-green','finite-green-crossing','mean-contrast-green','radial-green-intertwiner','radial-common-refinement','completed-trace-kernel','physical-cauchy-endpoint-domain','native-completed-pairing',
       'tfvd-green-provenance-mellin','tfvd-four-leg-mellin',
       'native-camera-tail-mellin','material-theta-tfvd-port']
files={p.stem:p for name in names for p in (root.parent/name).glob('*.lean')
       if p.stem!='Audit'}
done=set()
def build(name):
    if name in done:return
    p=files[name]
    for dep in re.findall(r'^import (\S+)',p.read_text(),re.M):
        if dep in files:build(dep)
    subprocess.run(['bash',str(root/'compile_module.sh'),name,str(p)],check=True)
    done.add(name)
    print('UPSTREAM PASS '+name,flush=True)
for target in ['OddAsymptotics']:build(target)
print(f'Compiled {len(done)} ancestor modules.',flush=True)
