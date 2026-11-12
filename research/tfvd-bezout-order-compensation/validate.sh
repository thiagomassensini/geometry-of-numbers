#!/usr/bin/env bash
set -euo pipefail

task_dir=$(cd "$(dirname "$0")" && pwd)
research_dir=$(cd "$task_dir/.." && pwd)
pr70_dir="$research_dir/tfvd-bezout-schur-residual"
c3_dir="$research_dir/c3-dimension-three"
operator_root=${CARRY_OPERATOR_ROOT:-/home/thlinux/carry-self-adjoint-operator}
c3_pr70_root=${CARRY_PR70_ROOT:-/home/thlinux/geometry-of-numbers/research/tfvd-bezout-schur-residual}
c3_pr143_cache=${CARRY_PR143_CACHE:-/home/thlinux/geometry-of-numbers-tfvd-uniform-relative-source/research/tfvd-uniform-relative-source/.cache}
main_repo=$(cd "$c3_pr70_root/../.." && pwd)

if rg -n '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom\b' "$task_dir" --glob '*.lean'; then
  echo "ERROR: prohibited proof escape found in research Lean source." >&2
  exit 1
else
  scan_status=$?
  if (( scan_status != 1 )); then
    exit "$scan_status"
  fi
fi

mkdir -p "$task_dir/.cache"
# C3Tail256 imports this upstream operator and its CPFormal dependency. Build
# that exact dependency closure first so the validation does not rely on a
# pre-existing local .olean cache.
(cd "$operator_root" && lake build CPFormal NativeCarrySpectralWeyl CarryGeometry GreenFrame \
  CarrySelfAdjointOperator.CompletedNativeAllOrderMomentUpperBound)
bash "$c3_dir/compile.sh" C3Tail256
cd "$operator_root"
export PATH="$HOME/.elan/bin:$PATH"
base_lean_path=$(lake env printenv LEAN_PATH)
main_research_caches=$(find "$main_repo/research" -type d \
  \( -name .cache -o -path '*/.cache/pr*' \) -printf '%p:')
main_research_builds=$(find "$main_repo/.lake/build/research" -type d -printf '%p:' 2>/dev/null || true)
export LEAN_PATH="$task_dir/.cache:$c3_dir/.cache:$c3_pr143_cache:$c3_pr70_root/.cache:$main_repo/.lake/build/lib/lean:$main_repo/.lake/build/research/carry-global-synthesis-kernels/pr38-lib:$main_research_caches:$main_research_builds:$base_lean_path"

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

for module in CoefficientLaw RankOneUpdate Regression BorderedDeterminant SchurThreshold TfvdBoundaryLaw FiniteC3Gate Audit; do
  lean -DwarningAsError=true --root="$task_dir" \
    -o "$task_dir/.cache/$module.olean" "$task_dir/$module.lean"
done
