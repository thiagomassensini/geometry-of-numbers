#!/usr/bin/env bash
set -euo pipefail
task_dir=$(cd -- "$(dirname -- "$0")" && pwd)
repo=$(cd -- "$task_dir/../.." && pwd)
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$task_dir/evidence"
cd "$task_dir"
python3 restore_verified_cache.py --verify-only
bash compile_module.sh AllOrderTail > evidence/lean-AllOrderTail.log 2>&1
bash compile_module.sh Audit > evidence/lean-axioms.log 2>&1
if grep -En '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom[[:space:]]' AllOrderTail.lean; then exit 1; fi
if grep -Ev '^.CarryAllOrderTail\.[a-zA-Z0-9_]+. depends on axioms: \[propext, Classical.choice, Quot.sound\]$' evidence/lean-axioms.log; then exit 1; fi
cd "$repo"
lake build --wfail > "$task_dir/evidence/root-build.log" 2>&1
for layer in foundation geometry analysis; do
  bash "scripts/audit-$layer.sh" > "$task_dir/evidence/audit-$layer.log" 2>&1
done
printf '%s\n' 'PASS: source module, #print axioms, root --wfail, Foundation/Geometry/Analysis audits.'
