#!/usr/bin/env bash
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "$0")/../../../../../../" && pwd)
cd "$repo_root"
evidence="$repo_root/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-m2-dirichlet-term-stage19-20261107"
output="$repo_root/research/native-moving-schur-sigma/.cache/c5-m2-term"
mkdir -p "$evidence" "$output"
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$output"
export SIGMA_HEIGHT50_BUILD="$output:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals"
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage19ExportProbe > "$evidence/export-probe.log" 2>&1
printf 'BUILD_EXIT=0\n' >> "$evidence/export-probe.log"
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage19Certificate > "$evidence/state-stage19-build.log" 2>&1
printf 'BUILD_EXIT=0\n' >> "$evidence/state-stage19-build.log"
python3 "$evidence/check_stage19_axioms.py"
