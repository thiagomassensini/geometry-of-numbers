#!/usr/bin/env bash
set -euo pipefail
research_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$research_dir/../.." && pwd)"
operator_root="${1:-$repo_root/../carry-self-adjoint-operator}"
evidence_dir="${2:-$research_dir/evidence}"
mkdir -p -- "$evidence_dir"
export PATH=/home/thlinux/.elan/bin:"$PATH"
python3 - "$repo_root" "$operator_root" <<'PY'
import json,pathlib,subprocess,sys
r,o=map(pathlib.Path,sys.argv[1:])
assert subprocess.check_output(['git','-C',str(o),'rev-parse','HEAD'],text=True).strip()=='045369f6dedcb2e75e9aefed1d12c9f73b9a2532'
assert (r/'lean-toolchain').read_bytes()==(o/'lean-toolchain').read_bytes()
def pins(p): return {x['name']:x['rev'] for x in json.loads((p/'lake-manifest.json').read_text())['packages'] if x['name'] in ['mathlib','GreenFrame']}
assert pins(r)==pins(o) and len(pins(r))==2
subprocess.run(['git','-C',str(r),'diff','--exit-code','21115c7cd51a20898fb01db40cbffb918b503d52','--','research/material-central-calibration/CanonicalComparison.lean','lean-toolchain','lake-manifest.json'],check=True)
assert (r/'.lake/build/research/material-pivot-certificate/CanonicalComparison.olean').is_file()
print('PASS: fixed operator, shared pins, unchanged cached comparison dependency')
PY
for module_name in PrimeClockBridge PrimeOverlapCanary PrimeClockSchur PrimeCameraGramComparison PrimeClockCanonicalGate LiteralCameraCanary PrimeClockGreenTransport Regression Audit; do
  if bash "$research_dir/compile_module.sh" "$module_name" "$operator_root" > "$evidence_dir/$module_name.log" 2>&1; then
    printf 'PASS: %s\n' "$module_name"
  else
    printf 'FAIL: %s\n' "$module_name" >&2
    exit 1
  fi
done
python3 "$research_dir/check_public_roots.py"
(cd -- "$repo_root" && lake build --wfail) > "$evidence_dir/root-build.log" 2>&1
printf 'PASS: root build --wfail\n'
for zone in foundation geometry analysis; do
  (cd -- "$repo_root" && bash "scripts/audit-$zone.sh") > "$evidence_dir/$zone-audit.log" 2>&1
  printf 'PASS: %s audit\n' "$zone"
done
python3 - "$research_dir" "$repo_root" "$operator_root" > "$evidence_dir/source-manifest.json" <<'PY'
import hashlib,json,pathlib,subprocess,sys
r,g,o=map(pathlib.Path,sys.argv[1:])
def head(p):return subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
print(json.dumps({'geometry_head':head(g),'operator_head':head(o),'lean_toolchain':(g/'lean-toolchain').read_text().strip(),'lean_sources':{f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(r.glob('*.lean'))}},indent=2))
PY
printf 'PASS: completed prime synthesis, Schur, camera overlap and canonical gap\n'
