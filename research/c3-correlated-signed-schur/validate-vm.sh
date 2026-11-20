#!/usr/bin/env bash
# Rebuild new research modules against existing certified VM dependencies.
set -euo pipefail
TASK="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SOURCE_REPO="${SOURCE_REPO:-/home/thlinux/geometry-of-numbers}"
CSA_REPO="${CSA_REPO:-/home/thlinux/carry-self-adjoint-operator}"
task_dir="$SOURCE_REPO/research/c3-fourteenth-tail"
repo="$SOURCE_REPO"
test -f "$task_dir/compile_module.sh"
test -d "$SOURCE_REPO/research/tfvd-bezout-schur-residual/.cache"
test -d "$CSA_REPO/.lake"
cd "$CSA_REPO"
build_env="$(grep '^export LEAN_PATH=' "$task_dir/compile_module.sh")"
test -n "$build_env"
eval "$build_env"
export LEAN_PATH="$TASK/lean:$SOURCE_REPO/research/tfvd-bezout-schur-residual/.cache:$LEAN_PATH"
export PATH="$HOME/.elan/bin:$PATH"
modules=(
 ResidualPrefixGate ResidualDominanceGate LastMomentSplit SingleModeGate
 ProjectedCauchy NativeMixedU NativeMixedCS NativeSingleModeGate
 NativeOldPrefixSignedGate SignedSourceTail GroupedSourceBudget NativeSignedGate CombinedEulerBezout
 C3CompletedJetBoxes C3TailNativeCrosswalkAny C3Certified384Boxes
 C3LinearSupport AuditC3JetBoxes
)
for mod in "${modules[@]}"; do
  echo "[Lean] $mod"
  lean -DwarningAsError=true --root="$TASK/lean" -o "$TASK/lean/$mod.olean" "$TASK/lean/$mod.lean"
done
echo "PASS: ${#modules[@]} Lean modules; audit prints standard axiom dependencies."
