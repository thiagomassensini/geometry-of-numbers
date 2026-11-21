#!/usr/bin/env bash
set -euo pipefail
P="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CP_HOST="${CP_HOST:-/home/thlinux/carry-c2-source-raw-green}"
cd "$CP_HOST"
export LEAN_PATH="$P/lean:$(lake env printenv LEAN_PATH)"
for mod in C2ConnectedDefectSchurObstruction C2ConnectedDyadicTowerSign C2ConnectedDyadicKernelIndefinite C2ConnectedLogTfvdDyadicSign C2DepthMassNormalizedSignNoGo C2DepthRankOneRepairGate AuditC2ConnectedDepthScale; do
    echo "LEAN $mod"
    lean -DwarningAsError=true --root="$P/lean" -o "$P/lean/$mod.olean" "$P/lean/$mod.lean"
done
python3 "$P/numerics/c2_connected_depth_scale_exact.py"
echo "PASS 7 Lean modules, axiom audit and rational testing"
