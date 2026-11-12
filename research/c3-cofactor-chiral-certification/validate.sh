#!/usr/bin/env bash
set -euo pipefail

task_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(cd "$task_dir/../.." && pwd)
correlation_dir="$repo_root/research/c3-cofactor-correlation-gate"
orientation_dir="$repo_root/research/c3-source-orientation"
geometry_root=${GEOMETRY_ROOT:-/home/thlinux/geometry-of-numbers}
carry_root=${CARRY_ROOT:-/home/thlinux/carry-self-adjoint-operator}
source_orientation_cache=${CARRY_PR145_CACHE:-/home/thlinux/geometry-of-numbers-c3-source-orientation/research/c3-source-orientation/.cache}
third_source_cache=${CARRY_PR146_CACHE:-/home/thlinux/geometry-of-numbers-critical-tilt-prime/research/c3-tilt-prime/.cache}

for required in "$repo_root" "$geometry_root" "$carry_root"; do
  if [[ ! -d "$required" ]]; then
    printf 'missing repository/cache root: %s\n' "$required" >&2
    exit 2
  fi
done

mkdir -p "$task_dir/.cache"

cache_paths=$(find \
  "$repo_root/research" \
  "$geometry_root/research" \
  "$carry_root/research" \
  -type d -path '*/.cache*' -printf '%p:')
research_build_paths=$(find \
  "$geometry_root/.lake/build/research" \
  "$carry_root/.lake/build/research" \
  -mindepth 1 -maxdepth 1 -type d -printf '%p:' 2>/dev/null || true)

printf 'Geometry HEAD: %s\n' "$(git -C "$repo_root" rev-parse HEAD)"
printf 'Carry HEAD: %s\n' "$(git -C "$carry_root" rev-parse HEAD)"
printf 'Toolchain: %s\n' "$(cat "$repo_root/lean-toolchain")"
cd "$carry_root"
lean --version
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir/.cache:$correlation_dir/.cache:$cache_paths$source_orientation_cache:$third_source_cache:$research_build_paths$geometry_root/.lake/build/lib/lean:$carry_root/.lake/build/lib/lean:$lake_path"

modules=(
  C3Acceleration48
  C3Power26Step
  C3Power26Tail
  C3Power26Series
  C3Boundary48Finite
  C3Boundary48Infinity
  C3Boundary48Stencil
  C3CompletionTail48
  C3Head48Jet
  C3Head48Boxes
  GeneralCofactorIdentity
  ChiralOrder11
  CofactorIdentity
  SchurGate
  IntervalGate
  C3Regression
  GammaThirteen
  CompletedBoxes48
  GammaHeadCrosswalk
  SourceGate
)

for module in "${modules[@]}"; do
  printf 'Lean: %s\n' "$module"
  lean -DwarningAsError=true --root="$task_dir" \
    -o "$task_dir/.cache/$module.olean" "$task_dir/$module.lean"
done

# The correlation validator rechecks all finite tables against the head,
# Gamma and tail semantics before any of the native sign theorems are built.
GEOMETRY_OF_NUMBERS_ROOT="$geometry_root" CARRY_SELF_ADJOINT_OPERATOR_ROOT="$carry_root" \
  bash "$correlation_dir/validate.sh"

printf 'Lean: SourceSchurShift\n'
lean -DwarningAsError=true --root="$orientation_dir" \
  -o "$task_dir/.cache/SourceSchurShift.olean" "$orientation_dir/SourceSchurShift.lean"
for module in CofactorTransport NativeOddCertificate NativeEvenCertificate CertificateAudit; do
  printf 'Lean: %s\n' "$module"
  lean -DwarningAsError=true --root="$task_dir" \
    -o "$task_dir/.cache/$module.olean" "$task_dir/$module.lean"
done

set +e
rg -n '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom\b' \
  "$task_dir" "$correlation_dir" --glob '*.lean'
scan_status=$?
set -e
if (( scan_status == 0 )); then
  printf 'forbidden proof placeholder found\n' >&2
  exit 1
elif (( scan_status != 1 )); then
  printf 'proof-placeholder scan failed with status %s\n' "$scan_status" >&2
  exit "$scan_status"
fi

printf 'Exact rational diagnostic:\n'
python3 "$task_dir/diagnose_completed_boxes48.py"

printf 'Numerical C3 head comparison (diagnostic only):\n'
python3 "$task_dir/compare_c3_heads.py"

cd "$repo_root"
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
git diff --check
