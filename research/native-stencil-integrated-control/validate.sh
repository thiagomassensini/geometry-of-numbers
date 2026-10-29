#!/usr/bin/env bash
set -euo pipefail
task_dir=$(cd -- "$(dirname -- "$0")" && pwd)
repo=$(cd -- "$task_dir/../.." && pwd)
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$task_dir/evidence"
cd "$task_dir"
python3 ../native-all-order-radial-tail/restore_verified_cache.py --verify-only
bash ../native-all-order-radial-tail/compile_module.sh AllOrderTail > evidence/upstream-AllOrderTail.log 2>&1
for module in AtomicCorrectionControl VariationBudget RemainderVelocity FiniteVelocityBudget RadialExtrapolation; do
  bash ../native-jet-variation-budget/compile_module.sh "$module" > "evidence/upstream-$module.log" 2>&1
done
for module in StirlingBoundary CauchyBeta CenteredDifference StencilPair ReindexFactor SumReindex OddPairBridge OriginalSourceTransport IntegratedControl BudgetContinuity Audit TransitiveAudit; do
  bash compile_module.sh "$module" > "evidence/lean-$module.log" 2>&1
done
if grep -En '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom[[:space:]]' ./*.lean; then exit 1; fi
python3 - <<'PYTHON'
import re
from pathlib import Path
roots=re.findall(r'^#print axioms ([A-Za-z0-9_.]+)$',Path('Audit.lean').read_text(),re.M)
log=Path('evidence/lean-Audit.log').read_text()
entries=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log,re.S)
empty=re.findall(r"'([^']+)' does not depend on any axioms",log)
assert len(roots)==45 and len(entries)+len(empty)==len(roots)
assert {r for r,_ in entries} | set(empty) == set(roots)
for root,axioms in entries:
    assert set(x.strip() for x in axioms.split(',')) <= {'propext','Classical.choice','Quot.sound'}, root
assert 'Transitive source audit: 55 roots;' in Path('evidence/lean-TransitiveAudit.log').read_text()
print('PASS: 45 theorem axioms and 55 transitive roots')
PYTHON
python3 centered_identity_probe.py > evidence/probe.log
cd "$repo"
lake build --wfail > "$task_dir/evidence/root-build.log" 2>&1
for layer in foundation geometry analysis; do
  bash "scripts/audit-$layer.sh" > "$task_dir/evidence/audit-$layer.log" 2>&1
done
printf '%s\n' 'PASS: ancestor caches, new modules, axioms, root --wfail, Foundation/Geometry/Analysis, exact controls.'
