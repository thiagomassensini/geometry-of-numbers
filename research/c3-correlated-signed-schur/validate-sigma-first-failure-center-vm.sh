#!/usr/bin/env bash
set -euo pipefail
P="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
task_dir="${SIGMA_ROOT:-/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma}"
SOURCE_CACHE="${SOURCE_CACHE:-/home/thlinux/worktrees/tfvd-bezout-order-compensation-20261110/research/tfvd-bezout-order-compensation/.cache}"
GON_LIB="${GON_LIB:-/home/thlinux/geometry-of-numbers/.lake/build/lib/lean}"
CSA_REPO="${CSA_REPO:-/home/thlinux/carry-self-adjoint-operator}"
cd "$CSA_REPO"
eval "$(grep '^export LEAN_PATH=' "$task_dir/compile_module.sh")" 2>/dev/null
export LEAN_PATH="$P/lean:$SOURCE_CACHE:$GON_LIB:$task_dir/.cache/c3-validation/c1:$task_dir/.cache/c3-validation/final-run/integration:$LEAN_PATH"
for mod in TransverseSignThresholdCenterClosure NativeSigmaFirstFailureAllOrderGate TransverseTwoWindowNotEnough AuditNativeSigmaThresholdCenterClosure; do
  echo "[lean -DwarningAsError=true] $mod"
  lean -DwarningAsError=true --root="$P/lean" -o "$P/lean/$mod.olean" "$P/lean/$mod.lean"
done
echo "PASS: transverse full-failure dimension escape -> native PSD and exact TFVD; 2x2 no-go; audit"
