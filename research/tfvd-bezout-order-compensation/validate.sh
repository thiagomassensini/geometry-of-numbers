#!/usr/bin/env bash
set -euo pipefail

task_dir=$(cd "$(dirname "$0")" && pwd)
research_dir=$(cd "$task_dir/.." && pwd)
pr70_dir="$research_dir/tfvd-bezout-schur-residual"
operator_root=${CARRY_OPERATOR_ROOT:-/home/thlinux/carry-self-adjoint-operator}

mkdir -p "$task_dir/.cache"
cd "$operator_root"
export PATH="$HOME/.elan/bin:$PATH"
base_lean_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir/.cache:$base_lean_path"

compile_pr70() {
  local module=$1
  lean -DwarningAsError=true --root="$pr70_dir" \
    -o "$task_dir/.cache/$module.olean" "$pr70_dir/$module.lean"
}

# Rebuild the exact import chain in this worktree's private module cache.
for module in SourceBezout SourceMap SourceNative SourceBlocks SchurTransport \
  SourceSchur LiteralNativeTrace LiteralTfvd KernelBudget LiteralTailBounds \
  LiteralBudgetLimit LiteralCompanion CompanionJets Repartition \
  TwoEvenSourceMargin; do
  compile_pr70 "$module"
done

for module in CoefficientLaw RankOneUpdate Regression; do
  lean -DwarningAsError=true --root="$task_dir" \
    -o "$task_dir/.cache/$module.olean" "$task_dir/$module.lean"
done
