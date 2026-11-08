#!/usr/bin/env bash
set -euo pipefail

task_dir=$(cd -- "$(dirname -- "$0")/../../../.." && pwd)
evidence="$task_dir/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-gamma-d1-upper-complex-node-20261108"
reference_root=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
carry_root=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
finite_root=/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification
logq_root=/home/thlinux/worktrees/geometry-of-numbers-c5-logq-two-20261107
upper_node_root=/home/thlinux/worktrees/geometry-of-numbers-c5-zeta-csv-bridge-20261107

[[ $(git -C "$reference_root" rev-parse HEAD) == bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3 ]]
[[ $(git -C "$carry_root" rev-parse HEAD) == 045369f6dedcb2e75e9aefed1d12c9f73b9a2532 ]]
[[ $(git -C "$finite_root" rev-parse HEAD) == bfd68781f988b5c80c54716dd332f12685d75a70 ]]
[[ $(git -C "$logq_root" rev-parse HEAD) == e535728ab29786cc3fc2aafbb5e6954711c11679 ]]
[[ $(git -C "$upper_node_root" rev-parse HEAD) == 963d3d4c66dfedc7a08f036dfe4d597bdbaa5c4d ]]
[[ $(cat "$carry_root/lean-toolchain") == leanprover/lean4:v4.32.0 ]]

run_id=${C5_RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)}
[[ "$run_id" =~ ^[A-Za-z0-9._-]+$ ]]
log_dir="$evidence/reproduction/$run_id"
output_dir="$task_dir/.cache/c5-gamma-d1-upper-complex-$run_id"
mkdir -p "$log_dir" "$output_dir"
export SIGMA_REFERENCE_ROOT="$reference_root"
export CARRY_LEAN_ROOT="$carry_root"
export SIGMA_OUTPUT_DIR="$output_dir"
export SIGMA_HEIGHT50_BUILD="$finite_root/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean:$reference_root/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:$reference_root/research/native-moving-schur-sigma/.cache/c5-rational-node-clean-20261106:$logq_root/research/native-moving-schur-sigma/.cache/c5-gamma-core-node-pilot:$logq_root/research/native-moving-schur-sigma/.cache/c5-gamma-second-real-point-20261107:$upper_node_root/research/native-moving-schur-sigma/.cache/c5-gamma-complex-upper-node-clean-20261107-r1"
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean

for module in \
  SigmaC5GammaComplexNodeDOneUpperComplexProbe \
  SigmaC5GammaComplexNodeDOneUpperComplexCertificate \
  SigmaC5GammaComplexNodeDOneUpperComplexCombine \
  SigmaC5GammaSecondRealPointGammaCertificate \
  SigmaC5GammaDOneUpperLogBounds \
  SigmaC5GammaComplexNodeDOneUpperComplexGammaCertificate
do
  log="$log_dir/$module.log"
  if /usr/bin/time -v bash "$task_dir/compile_sigma_pade.sh" "$module" >"$log" 2>&1; then
    printf 'BUILD_EXIT=0\n' >>"$log"
  else
    code=$?
    printf 'BUILD_EXIT=%s\n' "$code" >>"$log"
    exit "$code"
  fi
done
python3 "$task_dir/check_c5_gamma_d1_upper_complex_axioms.py" "$log_dir"
printf 'Build and axiom audit passed.\n' > "$log_dir/RESULT.txt"
printf 'Build and axiom audit passed. Logs: %s\n' "$log_dir"
