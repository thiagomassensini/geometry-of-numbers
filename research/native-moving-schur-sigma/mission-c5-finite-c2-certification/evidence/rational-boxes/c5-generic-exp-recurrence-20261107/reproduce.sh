#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
task_dir="$(cd -- "$script_dir/../../../../" && pwd)"
output_dir="$task_dir/.cache/c5-generic-exp-recurrence-20261107"
log_dir="$output_dir/logs"
mkdir -p "$log_dir"

cache_roots=(
  /home/thlinux/worktrees/geometry-of-numbers-c5-node-pilot-after-log2-20261107/research/native-moving-schur-sigma/.cache/c5-zero-exp-stage6-separated-20261107
  /home/thlinux/worktrees/geometry-of-numbers-c5-node-pilot-after-log2-20261107/research/native-moving-schur-sigma/.cache/c5-zero-exp-stage5-separated-20261107
  /home/thlinux/worktrees/geometry-of-numbers-c5-node-pilot-after-log2-20261107/research/native-moving-schur-sigma/.cache/c5-zero-exp-stage4-separated-20261107
  /home/thlinux/worktrees/geometry-of-numbers-c5-node-pilot-after-log2-20261107/research/native-moving-schur-sigma/.cache/c5-zero-exp-stage3-separated-20261107
  /home/thlinux/worktrees/geometry-of-numbers-c5-node-pilot-after-log2-20261107/research/native-moving-schur-sigma/.cache/c5-zero-exp-stage2-separated-20261107
  /home/thlinux/worktrees/geometry-of-numbers-c5-node-pilot-after-log2-20261107/research/native-moving-schur-sigma/.cache/c5-exp-zero-integrated-20261107
  /home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107
  /home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiate-20261107
  /home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107
  /home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-rational-node-20261106
  /home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-rational-node-clean-20261106
  /home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c1
  /home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration
  /home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c4-clean
  /home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c4-main-clean
)
build_dirs=()
for cache_dir in "${cache_roots[@]}"; do
  if [[ -d "$cache_dir" ]] && compgen -G "$cache_dir/*.olean" >/dev/null; then
    build_dirs+=("$cache_dir")
  fi
done
build_path="$(IFS=:; echo "${build_dirs[*]}")"

export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$output_dir"
export SIGMA_HEIGHT50_BUILD="$build_path"
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean

run_module() {
  local module="$1"
  local log="$2"
  local status
  if bash "$task_dir/compile_sigma_pade.sh" "$module" >"$log" 2>&1; then
    status=0
  else
    status=$?
  fi
  printf 'BUILD_EXIT=%s\n' "$status" >>"$log"
  if [[ $status -ne 0 ]]; then
    return "$status"
  fi
}

run_module SigmaC5ZeroExpStagesCertificate "$log_dir/stages-base-build.log"
run_module SigmaC5ZeroExpGenericRecurrence "$log_dir/generic-recurrence-build.log"
run_module SigmaC5ZeroExpGenericRecurrenceAudit "$log_dir/generic-recurrence-audit.log"
