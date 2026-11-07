#!/usr/bin/env bash
set -euo pipefail

worktree=/home/thlinux/worktrees/geometry-of-numbers-c5-logq-two-20261107
cd "$worktree"

export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-gamma-complex-node-clean-20261107-r1"
export SIGMA_HEIGHT50_BUILD="/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-rational-node-clean-20261106:/home/thlinux/worktrees/geometry-of-numbers-c5-logq-two-20261107/research/native-moving-schur-sigma/.cache/c5-gamma-core-node-pilot:/home/thlinux/worktrees/geometry-of-numbers-c5-logq-two-20261107/research/native-moving-schur-sigma/.cache/c5-gamma-second-real-point-20261107"
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean

[[ $(git -C "$SIGMA_REFERENCE_ROOT" rev-parse HEAD) == bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3 ]]
[[ $(git -C "$CARRY_LEAN_ROOT" rev-parse HEAD) == 045369f6dedcb2e75e9aefed1d12c9f73b9a2532 ]]
[[ $(cat "$CARRY_LEAN_ROOT/lean-toolchain") == leanprover/lean4:v4.32.0 ]]

evidence="$PWD/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-gamma-complex-node-20261107"
mkdir -p "$SIGMA_OUTPUT_DIR" "$evidence/clean-build-r1"

for module in \
  SigmaC5GammaComplexNodeProbe \
  SigmaC5GammaComplexNodeCertificate \
  SigmaC5GammaComplexNodeCombine \
  SigmaC5GammaSecondRealPointGammaCertificate \
  SigmaC5GammaComplexNodeGammaCertificate
do
  log="$evidence/clean-build-r1/$module.log"
  if bash research/native-moving-schur-sigma/compile_sigma_pade.sh "$module" >"$log" 2>&1; then
    printf 'BUILD_EXIT=0\n' >>"$log"
  else
    build_status=$?
    printf 'BUILD_EXIT=%s\n' "$build_status" >>"$log"
    exit "$build_status"
  fi
done
