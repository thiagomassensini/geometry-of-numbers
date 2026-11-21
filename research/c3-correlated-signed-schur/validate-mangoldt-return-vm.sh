#!/usr/bin/env bash
# Re-run source-first von Mangoldt / C2 leg-center and physical native return audit.
set -euo pipefail
P="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="${GON_REPO:-/home/thlinux/geometry-of-numbers}"
CSA_REPO="${CSA_REPO:-/home/thlinux/carry-self-adjoint-operator}"
task_dir="$repo/research/native-return-boundary-deflation"
test -f "$task_dir/compile_module.sh"
test -d "$task_dir/.cache"
cd "$CSA_REPO"
eval "$(grep '^export LEAN_PATH=' "$task_dir/compile_module.sh")"
export LEAN_PATH="$P/lean:$LEAN_PATH"
for mod in PrimeDepthMangoldtBracket PrimePowerLegCenterIncidence NativeReturnPrimitiveVariation NativeReturnNontrivialDerivative AuditPrimeDepthMangoldtReturn; do
  echo "[Lean] $mod"
  lean -DwarningAsError=true --root="$P/lean" -o "$P/lean/$mod.olean" "$P/lean/$mod.lean"
done
python3 "$P/numerics/mangoldt_leg_center_arb_canaries.py"
echo "PASS: 5 Lean modules and signed C2/C5 interval canaries"
