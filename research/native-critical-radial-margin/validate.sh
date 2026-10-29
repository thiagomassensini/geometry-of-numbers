#!/usr/bin/env bash
set -euo pipefail
task_dir=$(cd -- "$(dirname -- "$0")" && pwd)
repo=$(cd -- "$task_dir/../.." && pwd)
if (($#)); then mode=$1; else mode=--focused; fi
case "$mode" in --focused|--full) ;; *) echo "uso: $0 [--focused|--full]" >&2; exit 2;; esac
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$task_dir/evidence"
cd "$repo"
python3 research/native-summable-radial-tail/restore_ancestor_cache.py --verify-only
if grep -En '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom[[:space:]]' "$task_dir"/*.lean; then
  echo 'ERROR: proof shortcut or new axiom detected' >&2
  exit 1
fi
for m in MomentFunctional PolynomialCoordinates JacobiLogic NativeApplication SchurLogic; do
  printf 'building PR #41 %s\n' "$m"
  bash research/native-moment-orthogonalization-audit/compile_module.sh "$m" > "$task_dir/evidence/verify-pr41-$m.log" 2>&1
done
for m in ExplicitFinitePairing EffectiveResponse EffectiveOddPair EffectivePairBounds PairCurve FamilyCurve ScaledStep SummableFamily SixRegression; do
  printf 'building PR #134 %s\n' "$m"
  bash research/native-summable-radial-tail/compile_module.sh "$m" > "$task_dir/evidence/verify-pr134-$m.log" 2>&1
done
for m in SixMargin SixBoundary EightInputs EightCritical EightHead EightMargin EightSchurCore EightSign EightNative EightQuantitative Audit; do
  printf 'building %s\n' "$m"
  bash "$task_dir/compile_module.sh" "$m" > "$task_dir/evidence/verify-$m.log" 2>&1
done
python3 "$task_dir/check_axioms.py" "$task_dir/evidence/verify-Audit.log"
python3 "$task_dir/check_boxes.py" > "$task_dir/evidence/check-boxes.log"
if [[ "$mode" == --full ]]; then
  lake build --wfail > "$task_dir/evidence/root-build.log" 2>&1
  for layer in foundation geometry analysis; do
    bash "scripts/audit-$layer.sh" > "$task_dir/evidence/audit-$layer.log" 2>&1
  done
fi
printf 'PASS: focused Lean modules, 46 axioms, provenance audit and rational diagnostic (%s)\n' "$mode"
