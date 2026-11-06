#!/usr/bin/env bash
set -euo pipefail

task_dir=$(cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(cd -- "$task_dir/../.." && pwd)
package="$task_dir/height50-certified"
out_dir=${1:-$(mktemp -d "${TMPDIR:-/tmp}/sigma-height50.XXXXXX")}
mkdir -p "$out_dir"
out_dir=$(cd -- "$out_dir" && pwd)
external_out="$out_dir/external"
integration_out="$out_dir/integration"
mkdir -p "$external_out" "$integration_out"

lean_bin=${LEAN_BIN:-$(cd -- "$repo_root" && elan which lean)}
lake_dir=${LAKE_DIR:-$repo_root/.lake}
export LEAN="$lean_bin"
export LAKE_DIR="$lake_dir"

bash "$package/hunts/rh_height_lean/lean/build.sh" --full "$external_out" \
  2>&1 | tee "$out_dir/external-build.log"
python3 "$package/hunts/rh_height_lean/lean/check_axioms.py" \
  "$out_dir/external-build.log" --full

SIGMA_OUTPUT_DIR="$integration_out" LEAN_BIN="$lean_bin" \
  bash "$task_dir/compile_c1.sh"

local_modules=(
  SigmaIsolationFactorization
  SigmaSignedPencil
  SigmaPadeCorrespondence
  SigmaTwoPoleModel
  SigmaTransverseAllOrder
  SigmaTransverseJoint
  SigmaZeroPairDecomposition
  SigmaPadeConvergence
  SigmaRemainderDescent
  SigmaRHHeightBridge
  SigmaHeight50Integration
  SigmaPadeEventualNegativity
  SigmaParityNegativeDirection
)
for module in "${local_modules[@]}"; do
  echo "== local $module" | tee -a "$out_dir/integration-build.log"
  SIGMA_HEIGHT50_BUILD="$external_out" \
    SIGMA_OUTPUT_DIR="$integration_out" \
    LEAN_BIN="$lean_bin" \
    bash "$task_dir/compile_sigma_pade.sh" "$module" \
    2>&1 | tee -a "$out_dir/integration-build.log"
done

python3 "$task_dir/generate_sigma_pade_audit.py"
awk '/^== local SigmaParityNegativeDirection$/ { exit }
  /^== local SigmaHeight50Integration$/ { copy = 1 }
  copy' \
  "$out_dir/integration-build.log" > "$out_dir/final-integration.log"
python3 "$package/check_sigma_axioms.py" "$out_dir/final-integration.log"
echo "== local SigmaPadeAudit" | tee "$out_dir/transitive-pade-audit.log"
SIGMA_HEIGHT50_BUILD="$external_out" \
  SIGMA_OUTPUT_DIR="$integration_out" \
  LEAN_BIN="$lean_bin" \
  bash "$task_dir/compile_sigma_pade.sh" SigmaPadeAudit \
  2>&1 | tee -a "$out_dir/transitive-pade-audit.log"
echo "Build outputs and audit logs: $out_dir"
