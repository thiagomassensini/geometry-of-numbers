#!/usr/bin/env bash
set -euo pipefail
task_dir=$(cd -- "$(dirname -- "$0")" && pwd)
repo=$(cd -- "$task_dir/../.." && pwd)
if (($#)); then mode=$1; else mode=--focused; fi
case "$mode" in --focused|--full) ;; *) echo "uso: $0 [--focused|--full]" >&2; exit 2;; esac
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$task_dir/evidence"
cd "$repo"
archive="$repo/research/native-all-order-radial-tail/.cache/input-cache.tar.gz"
if [[ ! -f "$archive" && -f /tmp/native-effective-radial-budget-verified-cache.tar.gz ]]; then
  mkdir -p "$(dirname "$archive")"
  cp /tmp/native-effective-radial-budget-verified-cache.tar.gz "$archive"
fi
python3 "$task_dir/restore_ancestor_cache.py"
if grep -En '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom[[:space:]]' "$task_dir"/*.lean; then
  echo "ERROR: proof shortcut or new axiom detected" >&2
  exit 1
fi
bash research/native-all-order-radial-tail/compile_module.sh AllOrderTail > "$task_dir/evidence/verify-upstream.log" 2>&1
for m in VariationBudget RemainderVelocity FiniteVelocityBudget; do
  bash research/native-jet-variation-budget/compile_module.sh "$m" >> "$task_dir/evidence/verify-upstream.log" 2>&1
done
for m in IntegratedControl BudgetContinuity; do
  bash research/native-stencil-integrated-control/compile_module.sh "$m" >> "$task_dir/evidence/verify-upstream.log" 2>&1
done
for m in ExplicitFinitePairing EffectiveResponse EffectiveOddPair EffectivePairBounds PairCurve FamilyCurve ScaledStep SummableFamily SixRegression Examples Audit; do
  printf 'building %s\n' "$m"
  bash "$task_dir/compile_module.sh" "$m" > "$task_dir/evidence/verify-$m.log" 2>&1
done
grep -q 'Transitive source audit: 2 roots;' "$task_dir/evidence/verify-Audit.log"
if [[ "$mode" == --full ]]; then
  lake build --wfail > "$task_dir/evidence/root-build.log" 2>&1
  for layer in foundation geometry analysis; do
    bash "scripts/audit-$layer.sh" > "$task_dir/evidence/audit-$layer.log" 2>&1
  done
fi
printf 'PASS: focused native modules, axioms, transitive general audit (%s)\n' "$mode"
