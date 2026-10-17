#!/usr/bin/env bash
# Run on llm from the fixed geometry checkout; no source/pin changes.
set -euo pipefail
research_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$research_dir/../.." && pwd)"
operator_root="${1:-$repo_root/../carry-self-adjoint-operator}"
operator_root="$(cd -- "$operator_root" && pwd)"
evidence_dir="${2:-$research_dir/evidence}"
mkdir -p -- "$evidence_dir"
export PATH=/home/thlinux/.elan/bin:"$PATH"
validation_jobs="${CARRY_INTEGRAL_JOBS:-2}"
[[ "$validation_jobs" =~ ^[1-4]$ ]]
python3 - "$repo_root" "$operator_root" <<'PY'
import json,pathlib,subprocess,sys
r,o=map(pathlib.Path,sys.argv[1:])
assert subprocess.check_output(['git','-C',str(o),'rev-parse','HEAD'],text=True).strip()=='045369f6dedcb2e75e9aefed1d12c9f73b9a2532'
assert (r/'lean-toolchain').read_bytes()==(o/'lean-toolchain').read_bytes()
def pins(p):return {x['name']:x['rev'] for x in json.loads((p/'lake-manifest.json').read_text())['packages'] if x['name'] in ['mathlib','GreenFrame']}
assert pins(r)==pins(o) and len(pins(r))==2
print('PASS: fixed operator HEAD and identical shared pins')
PY
cd -- "$repo_root"
lake build --wfail > "$evidence_dir/root-build.log" 2>&1
# Recompile the unchanged PR #21/#22 dependencies, not just their caches.
lean_executable="$(lake env sh -c 'command -v lean')"
operator_lpath="$(cd -- "$operator_root" && lake env printenv LEAN_PATH)"
prior_cache="$repo_root/.lake/build/research/material-pivot-certificate"
task_cache="$repo_root/.lake/build/research/material-integral-certificate"
mkdir -p -- "$prior_cache" "$task_cache"
cd -- "$operator_root"
if [[ "${CARRY_INTEGRAL_REUSE_PR22:-0}" == 1 ]]; then
  test -f "$prior_cache/CanonicalComparison.olean"
  test -f "$prior_cache/CanonicalPivotCertificate.olean"
  git -C "$repo_root" diff --exit-code 0ec56d57651c99fa8fd24a5e1d268558bc05ac77 --     research/material-central-calibration/CanonicalComparison.lean     research/material-pivot-certificate/CanonicalPivotCertificate.lean
  printf 'PASS: reusing checked PR22 dependencies; their sources are unchanged
'
else
LEAN_PATH="$repo_root/.lake/build/lib/lean:$operator_lpath" "$lean_executable" \
  -DwarningAsError=true --root="$repo_root/research/material-central-calibration" \
  -o "$prior_cache/CanonicalComparison.olean" \
  "$repo_root/research/material-central-calibration/CanonicalComparison.lean" \
  > "$evidence_dir/pr21-comparison.log" 2>&1
LEAN_PATH="$prior_cache:$repo_root/.lake/build/lib/lean:$operator_lpath" "$lean_executable" \
  -DwarningAsError=true --root="$repo_root/research/material-pivot-certificate" \
  -o "$prior_cache/CanonicalPivotCertificate.olean" \
  "$repo_root/research/material-pivot-certificate/CanonicalPivotCertificate.lean" \
  > "$evidence_dir/pr22-certificate.log" 2>&1
fi
LEAN_PATH="$repo_root/.lake/build/lib/lean:$operator_lpath" "$lean_executable" \
  -DwarningAsError=true --root="$repo_root/research/material-pivot-certificate" \
  -o "$task_cache/IntervalHelpers.olean" \
  "$repo_root/research/material-pivot-certificate/IntervalHelpers.lean" \
  > "$evidence_dir/IntervalHelpers.log" 2>&1
compile_module() {
  if bash "$research_dir/compile_module.sh" "$1" "$operator_root" > "$evidence_dir/$1.log" 2>&1; then
    printf 'PASS: %s\n' "$1"
  else
    printf 'FAIL: %s (see dedicated log)\n' "$1" >&2
    return 1
  fi
}
run_batch() {
  local validation_running=() validation_batch_status=0 validation_pid validation_module
  for validation_module in "$@"; do
    compile_module "$validation_module" &
    validation_running+=("$!")
    if (( ${#validation_running[@]} >= validation_jobs )); then
      wait "${validation_running[0]}" || validation_batch_status=1
      validation_running=("${validation_running[@]:1}")
    fi
  done
  for validation_pid in "${validation_running[@]}"; do
    wait "$validation_pid" || validation_batch_status=1
  done
  return "$validation_batch_status"
}
for module_name in FixedInterval ThetaDerivatives WeightedQuadrature ThetaRetainedTail SourceIntegral ExponentialEnclosures CoefficientData CoefficientSupport; do
  compile_module "$module_name"
done
run_batch CoefficientStep0 CoefficientStep1 CoefficientStep2 CoefficientStep3A CoefficientStep3B
for module_name in CoefficientStep3 CoefficientCode CodeBounds SourceComputation SourceBoxes FullSourceBoxes PivotFromIntegral NumericalPivotCheck NodeCacheData CachedSourceProgram ExactGridWeights; do
  compile_module "$module_name"
done
run_batch ArgNodeChecks ModeNodeChecks
for module_name in NodeCacheEquivalence ExactSourceProgram ExactSourceProof TaylorNodeComputation QuadratureCacheData TabledSourceProgram; do
  compile_module "$module_name"
done
run_batch QuadratureNodeCheck0 QuadratureNodeCheck1 QuadratureNodeCheck2 QuadratureNodeCheck3
for module_name in QuadratureNodeChecks TabledSourceEquivalence; do
  compile_module "$module_name"
done
run_batch CachedIntegralCheck0 CachedIntegralCheck1 CachedIntegralCheck2 CachedIntegralCheck3
for module_name in CachedIntegralChecks IntegralInputChecks IntegralCertificate Regression Audit; do
  compile_module "$module_name"
done
python3 "$research_dir/generate_coefficients.py" --out "$evidence_dir/regenerated-coefficients.lean"
cmp -- "$research_dir/CoefficientData.lean" "$evidence_dir/regenerated-coefficients.lean"
bash "$research_dir/compile_module.sh" DumpNodeCache "$operator_root" > "$evidence_dir/witness-nodes.json"
python3 "$research_dir/generate_node_cache.py" --input "$evidence_dir/witness-nodes.json" --out "$evidence_dir/regenerated-node-cache.lean"
cmp -- "$research_dir/NodeCacheData.lean" "$evidence_dir/regenerated-node-cache.lean"
bash "$research_dir/compile_module.sh" DumpTaylorCache "$operator_root" > "$evidence_dir/witness-taylor.json"
python3 "$research_dir/generate_taylor_cache.py" --input "$evidence_dir/witness-taylor.json" --out "$evidence_dir/regenerated-taylor-cache.lean"
cmp -- "$research_dir/QuadratureCacheData.lean" "$evidence_dir/regenerated-taylor-cache.lean"
python3 "$research_dir/check_public_roots.py"
python3 - "$research_dir" "$repo_root" "$operator_root" > "$evidence_dir/source-manifest.json" <<'PY_MANIFEST'
import hashlib,json,pathlib,subprocess,sys
r,g,o=map(pathlib.Path,sys.argv[1:])
def head(p): return subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
print(json.dumps({'geometry_head':head(g),'operator_head':head(o),
 'lean_toolchain':(g/'lean-toolchain').read_text().strip(),
 'lean_sources':{f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(r.glob('*.lean'))}},indent=2))
PY_MANIFEST
for audit_zone in foundation geometry analysis; do
  (cd -- "$repo_root" && bash "scripts/audit-$audit_zone.sh") > "$evidence_dir/$audit_zone-audit.log" 2>&1
  printf 'PASS: %s audit\n' "$audit_zone"
done
printf 'PASS: integral certificate, fourth pivot, explicit transitive axiom guards and regressions\n'
