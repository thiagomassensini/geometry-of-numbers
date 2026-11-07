#!/usr/bin/env bash
set -euo pipefail

worktree=/home/thlinux/worktrees/geometry-of-numbers-c5-logq-two-20261107
cd "$worktree"
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-gamma-second-real-point-20261107"
export SIGMA_HEIGHT50_BUILD="/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-rational-node-clean-20261106:/home/thlinux/worktrees/geometry-of-numbers-c5-logq-two-20261107/research/native-moving-schur-sigma/.cache/c5-gamma-core-node-pilot"
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean

for module in \
  SigmaC5GammaSecondRealPointProbe \
  SigmaC5GammaSecondRealPointCertificate \
  SigmaC5GammaSecondRealPointCombine \
  SigmaC5GammaSecondRealPointGammaCertificate
do
  bash research/native-moving-schur-sigma/compile_sigma_pade.sh "$module"
done
