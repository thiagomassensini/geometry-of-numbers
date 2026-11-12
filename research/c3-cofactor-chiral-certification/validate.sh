#!/usr/bin/env bash
set -euo pipefail

task_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(cd "$task_dir/../.." && pwd)
geometry_root=${GEOMETRY_ROOT:-/home/thlinux/geometry-of-numbers}
carry_root=${CARRY_ROOT:-/home/thlinux/carry-self-adjoint-operator}

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

cd "$carry_root"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir/.cache:$cache_paths$research_build_paths$geometry_root/.lake/build/lib/lean:$carry_root/.lake/build/lib/lean:$lake_path"

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

set +e
rg -n '\b(sorry|admit|native_decide)\b' "$task_dir" --glob '*.lean'
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

cd "$repo_root"
git diff --check
