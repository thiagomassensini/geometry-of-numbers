#!/usr/bin/env bash
set -euo pipefail

repo_root="$PWD"
task_root="$repo_root/research/native-moving-schur-sigma"
evidence_dir="$task_root/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-centered-first-term-20261107"
output_dir="$task_root/.cache/c5-centered-first-term-20261107"
mkdir -p "$evidence_dir" "$output_dir"

export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$output_dir"
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
export SIGMA_HEIGHT50_BUILD="$output_dir:/home/thlinux/worktrees/geometry-of-numbers-c5-phase0-replay-20261107/research/native-moving-schur-sigma/.cache/c5-generic-exp-recurrence-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-node-pilot-after-log2-20261107/research/native-moving-schur-sigma/.cache/c5-zero-exp-stage6-separated-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-node-pilot-after-log2-20261107/research/native-moving-schur-sigma/.cache/c5-zero-exp-stage5-separated-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-node-pilot-after-log2-20261107/research/native-moving-schur-sigma/.cache/c5-zero-exp-stage4-separated-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-node-pilot-after-log2-20261107/research/native-moving-schur-sigma/.cache/c5-zero-exp-stage3-separated-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-node-pilot-after-log2-20261107/research/native-moving-schur-sigma/.cache/c5-zero-exp-stage2-separated-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-node-pilot-after-log2-20261107/research/native-moving-schur-sigma/.cache/c5-exp-zero-integrated-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals"

if bash "$task_root/compile_sigma_pade.sh" SigmaC5CenteredFirstTerm > "$evidence_dir/build.log" 2>&1; then
  printf 'BUILD_EXIT=0\n' >> "$evidence_dir/build.log"
else
  status=$?
  printf 'BUILD_EXIT=%s\n' "$status" >> "$evidence_dir/build.log"
  exit "$status"
fi
python3 "$task_root/check_c5_centered_first_term_axioms.py" "$evidence_dir/build.log"
sha256sum \
  "$task_root/SigmaC5CenteredFirstTerm.lean" \
  "$task_root/check_c5_centered_first_term_axioms.py" \
  "$output_dir/SigmaC5CenteredFirstTerm.olean" \
  "$evidence_dir/reproduce.sh" \
  "$evidence_dir/README.md" \
  "$evidence_dir/build.log" \
  > "$evidence_dir/SHA256SUMS.txt"
