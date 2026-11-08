#!/usr/bin/env bash
set -euo pipefail

worktree=/home/thlinux/worktrees/geometry-of-numbers-c5-zeta-csv-bridge-20261107
cd "$worktree"

task_dir="$worktree/research/native-moving-schur-sigma"
evidence="$task_dir/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-gamma-complex-upper-node-20261107"
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$task_dir/.cache/c5-gamma-complex-upper-node-reproduce-20261107"
export SIGMA_HEIGHT50_BUILD="/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-rational-node-clean-20261106:/home/thlinux/worktrees/geometry-of-numbers-c5-logq-two-20261107/research/native-moving-schur-sigma/.cache/c5-gamma-core-node-pilot:/home/thlinux/worktrees/geometry-of-numbers-c5-logq-two-20261107/research/native-moving-schur-sigma/.cache/c5-gamma-second-real-point-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-logq-two-20261107/research/native-moving-schur-sigma/.cache/c5-gamma-complex-node-clean-20261107-r1"
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean

[[ $(git -C "$SIGMA_REFERENCE_ROOT" rev-parse HEAD) == bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3 ]]
[[ $(git -C "$CARRY_LEAN_ROOT" rev-parse HEAD) == 045369f6dedcb2e75e9aefed1d12c9f73b9a2532 ]]
[[ $(cat "$CARRY_LEAN_ROOT/lean-toolchain") == leanprover/lean4:v4.32.0 ]]

mkdir -p "$SIGMA_OUTPUT_DIR" "$evidence/clean-build-reproduction"
for module in \
  SigmaC5GammaComplexNodeUpperProbe \
  SigmaC5GammaComplexNodeUpperCertificate \
  SigmaC5GammaComplexNodeUpperCombine \
  SigmaC5GammaSecondRealPointGammaCertificate \
  SigmaC5GammaComplexNodeUpperGammaCertificate
do
  log="$evidence/clean-build-reproduction/$module.log"
  if /usr/bin/time -v bash "$task_dir/compile_sigma_pade.sh" "$module" >"$log" 2>&1; then
    printf 'BUILD_EXIT=0\n' >>"$log"
  else
    code=$?
    printf 'BUILD_EXIT=%s\n' "$code" >>"$log"
    exit "$code"
  fi
done
python3 "$task_dir/check_c5_gamma_complex_upper_axioms.py" "$evidence/clean-build-reproduction"
