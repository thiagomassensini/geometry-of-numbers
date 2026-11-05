from pathlib import Path
import os, re, subprocess, concurrent.futures, sys
GEOM = Path('/tmp/geometry-of-numbers-native-sigma-4.35-rerun')
CARRY = Path('/home/thlinux/carry-self-adjoint-operator')
OUT = GEOM/'research/native-moving-schur-sigma/.build435'
LOG = GEOM/'integration-build435'
LOG.mkdir(exist_ok=True)
OUT.mkdir(exist_ok=True)
LEAN = '/home/thlinux/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean'
LAKEPATH = ':'.join(x for x in subprocess.check_output(['bash','-lc',f'cd {GEOM} && lake env printenv LEAN_PATH'],text=True).strip().split(':') if '/.lake/packages/GreenFrame/.lake/build/lib/lean' not in x)
LIBDIRS = [Path(x) for x in LAKEPATH.split(':') if x]
FILES, ROOTS = {}, {}
def put(mod, path, root):
    FILES[mod], ROOTS[mod] = path, root
for p in (GEOM/'research').rglob('*.lean'):
    put(p.stem,p,p.parent)
for p in (GEOM/'GeometryOfNumbers').rglob('*.lean'):
    put('GeometryOfNumbers.'+'.'.join(p.relative_to(GEOM/'GeometryOfNumbers').with_suffix('').parts),p,GEOM)
for p in (GEOM/'.lake/packages/GreenFrame/GreenFrame').rglob('*.lean'):
    put('GreenFrame.'+'.'.join(p.relative_to(GEOM/'.lake/packages/GreenFrame').with_suffix('').parts),p,GEOM/'.lake/packages/GreenFrame')
for p in CARRY.rglob('*.lean'):
    rel=p.relative_to(CARRY)
    if '.lake' not in rel.parts and 'scratch_local' not in rel.parts:
        put('.'.join(rel.with_suffix('').parts),p,CARRY)
for pkg in (CARRY/'.lake/packages').iterdir():
    if not pkg.is_dir() or pkg.name in {'mathlib','batteries','aesop','Qq','Cli','proofwidgets','importGraph','LeanSearchClient','plausible'}: continue
    for p in pkg.rglob('*.lean'):
        rel=p.relative_to(pkg)
        if '.lake' not in rel.parts: put('.'.join(rel.with_suffix('').parts),p,pkg)

OVERRIDE = GEOM/'integration-overrides'
for p in OVERRIDE.rglob('*.lean'):
    rel=p.relative_to(OVERRIDE)
    pkg=OVERRIDE/rel.parts[0]
    put('.'.join(rel.with_suffix('').parts[1:]),p,pkg)
def outpath(mod): return OUT/Path(*mod.split('.')).with_suffix('.olean')
def ext_exists(mod):
    rel=Path(*mod.split('.')).with_suffix('.olean')
    return any((d/rel).is_file() for d in LIBDIRS)
EXTPREFIX=('Mathlib.','Batteries.','Aesop.','Qq.','Cli.','ProofWidgets.','ImportGraph.','LeanSearchClient.','Plausible.')
NODES, UNRESOLVED = {}, set()

def resolve(mod):
    if mod in FILES: return mod
    if '.' in mod and mod.split('.')[-1] in FILES: return mod.split('.')[-1]
    return None

def visit(mod):
    if mod in NODES: return
    key=resolve(mod)
    if key is None:
        if not ext_exists(mod) and mod not in {'Init','Lean'} and not mod.startswith(EXTPREFIX): UNRESOLVED.add(mod)
        return
    dest=outpath(key)
    if dest.is_file() or ext_exists(mod):
        NODES[key]={'done':True,'deps':set()}; return
    p=FILES[key]
    deps=set()
    for line in p.read_text(errors='replace').splitlines():
        s=line.strip()
        if not s.startswith('import '): continue
        s=s[len('import '):].split('--',1)[0]
        for dep in s.split():
            depkey=resolve(dep)
            if depkey is not None:
                deps.add(depkey); visit(depkey)
            elif not ext_exists(dep) and dep not in {'Init','Lean'} and not dep.startswith(EXTPREFIX): UNRESOLVED.add(dep)
    NODES[key]={'done':False,'deps':deps}
visit('SigmaRHHeightBridge')
if UNRESOLVED:
    print('UNRESOLVED IMPORTS:', *sorted(UNRESOLVED), sep='\n', flush=True); sys.exit(2)
for m,n in NODES.items():
    if n['done']:
        for other in NODES.values(): other['deps'].discard(m)
status=LOG/'status.log'
status.write_text(f'planned={sum(not x["done"] for x in NODES.values())} existing={sum(x["done"] for x in NODES.values())}\n')
print(status.read_text().strip(), flush=True)

def compile_one(mod):
    p, root = FILES[mod], ROOTS[mod]
    dest=outpath(mod); dest.parent.mkdir(parents=True,exist_ok=True)
    env=os.environ.copy(); env['LEAN_PATH']=str(OUT)+':'+LAKEPATH
    cmd=[LEAN,f'--root={root}','-o',str(dest),str(p)]
    r=subprocess.run(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=LOG/(mod.replace('.','_')+'.log')
    if r.stdout.strip(): log.write_text(r.stdout)
    return mod,r.returncode,r.stdout

workers=4
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
    running={}
    while True:
        ready=[m for m,n in NODES.items() if not n['done'] and not n.get('started') and not any(dep in NODES and not NODES[dep]['done'] for dep in n['deps'])]
        while ready and len(running)<workers:
            m=ready.pop(0); NODES[m]['started']=True
            fut=pool.submit(compile_one,m); running[fut]=m
        if not running:
            remaining=[m for m,n in NODES.items() if not n['done']]
            if not remaining: break
            print('STALLED:',remaining[:20],flush=True); sys.exit(3)
        done,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
        for fut in done:
            m=running.pop(fut); mod,code,out=fut.result()
            if code:
                with status.open('a') as f: f.write(f'FAIL {mod} code={code}\n{out}\n')
                print(f'FAIL {mod}',flush=True); sys.exit(code)
            NODES[mod]['done']=True
            with status.open('a') as f: f.write(f'OK {mod}\n')
            done_count=sum(n['done'] for n in NODES.values())
            if done_count%20==0 or done_count<10:
                print(f'OK {mod} [{done_count}/{len(NODES)}]',flush=True)
print(f'COMPLETE {len(NODES)} modules',flush=True)
