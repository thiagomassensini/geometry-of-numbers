#!/usr/bin/env bash
set -euo pipefail
research_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$research_dir/../.." && pwd)"
operator_root="${1:-$repo_root/../carry-self-adjoint-operator}"
evidence_dir="${2:-$research_dir/evidence}"
mkdir -p -- "$evidence_dir"
export PATH=/home/thlinux/.elan/bin:"$PATH"
export PYTHONDONTWRITEBYTECODE=1
python3 - "$repo_root" "$operator_root" <<'CHECK'
import hashlib,json,pathlib,subprocess,sys
r,o=map(pathlib.Path,sys.argv[1:])
assert subprocess.check_output(['git','-C',str(o),'rev-parse','HEAD'],text=True).strip()=='045369f6dedcb2e75e9aefed1d12c9f73b9a2532'
assert (r/'lean-toolchain').read_bytes()==(o/'lean-toolchain').read_bytes()
def pins(p):return {x['name']:x['rev'] for x in json.loads((p/'lake-manifest.json').read_text())['packages'] if x['name'] in ['mathlib','GreenFrame']}
assert pins(r)==pins(o) and len(pins(r))==2
subprocess.run(['git','-C',str(r),'diff','--exit-code','997d46291d3fb54d1a023d726890d4cc006acd2c','--','GeometryOfNumbers','scripts','research/material-central-calibration','research/material-integral-certificate','research/prime-camera-schur','research/corrected-green-source-ports','research/return-block-compatibility','lean-toolchain','lake-manifest.json'],check=True)
for folder,compiled in [('return-block-compatibility','LimitTower'),('return-block-compatibility','EighthReturnCheck'),('material-integral-certificate','IntegralCertificate'),('corrected-green-source-ports','CanonicalBlock')]:
 assert (r/'.lake/build/research'/folder/(compiled+'.olean')).is_file()
for folder in ['return-block-compatibility','corrected-green-source-ports','prime-camera-schur']:
 manifest=json.loads((r/'research'/folder/'evidence/source-manifest.json').read_text())
 for name,digest in manifest['lean_sources'].items():
  assert hashlib.sha256((r/'research'/folder/name).read_bytes()).hexdigest()==digest
print('PASS: source commits, shared pins and unchanged compiled dependencies')
CHECK
for module_name in CriticalSource PolarizedCritical CriticalMargins KnownMargins NextSourceGate Regression Audit; do
  if bash "$research_dir/compile_module.sh" "$module_name" "$operator_root" > "$evidence_dir/$module_name.log" 2>&1; then
    printf 'PASS: %s\n' "$module_name"
  else
    printf 'FAIL: %s\n' "$module_name" >&2
    cat "$evidence_dir/$module_name.log" >&2
    exit 1
  fi
done
python3 "$research_dir/check_public_roots.py"
python3 - "$research_dir" <<'CHECK'
import pathlib,re,sys
sys.path.insert(0,sys.argv[1])
from check_public_roots import lean_code
for f in pathlib.Path(sys.argv[1]).glob('*.lean'):
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',lean_code(f.read_text())),f
print('PASS: no admitted proofs, new axioms or trust escapes')
CHECK
(cd -- "$repo_root" && lake build --wfail) > "$evidence_dir/root-build.log" 2>&1
printf 'PASS: root build --wfail\n'
for zone in foundation geometry analysis; do
  (cd -- "$repo_root" && bash "scripts/audit-$zone.sh") > "$evidence_dir/$zone-audit.log" 2>&1
  printf 'PASS: %s audit\n' "$zone"
done
python3 - "$research_dir" "$repo_root" "$operator_root" "$evidence_dir" <<'CHECK'
import gzip,hashlib,json,pathlib,subprocess,sys
r,g,o,e=map(pathlib.Path,sys.argv[1:])
def head(p):return subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
manifest={'geometry_head':head(g),'base':'997d46291d3fb54d1a023d726890d4cc006acd2c','operator_head':head(o),'lean_toolchain':(g/'lean-toolchain').read_text().strip(),'lean_sources':{f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(r.glob('*.lean'))}}
(e/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
for name in ['root-build.log','foundation-audit.log','geometry-audit.log','analysis-audit.log']:
 f=e/name
 if f.exists():
  f.with_suffix(f.suffix+'.gz').write_bytes(gzip.compress(f.read_bytes(),mtime=0))
  f.unlink()
logs={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(e.iterdir()) if f.name.endswith(('.log','.gz'))}
result={'status':'pass','command':'bash research/critical-source-return/audit-critical-source-return.sh','public_roots':len((r/'public-roots.txt').read_text().splitlines()),'logs':logs}
(e/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: validation manifest and source hashes')
CHECK
