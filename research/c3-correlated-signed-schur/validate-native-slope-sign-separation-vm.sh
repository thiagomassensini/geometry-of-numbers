#!/usr/bin/env bash
set -euo pipefail
P="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CSA_ROOT="${CSA_ROOT:-/home/thlinux/carry-self-adjoint-operator}"
SOURCE_CACHE="${SOURCE_CACHE:-/home/thlinux/worktrees/tfvd-bezout-order-compensation-20261110/research/tfvd-bezout-order-compensation/.cache}"
SIGMA_ROOT="${SIGMA_ROOT:-/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma}"
GON_LIB="${GON_LIB:-/home/thlinux/geometry-of-numbers/.lake/build/lib/lean}"
cd "$CSA_ROOT"
test -f "$SOURCE_CACHE/LiteralTfvd.olean"
test -f "$SIGMA_ROOT/.cache/c3-validation/final-run/integration/SigmaTwoPoleModel.olean"
export LEAN_PATH="$P/lean:$SOURCE_CACHE:$GON_LIB:$SIGMA_ROOT/.cache/c3-validation/c1:$SIGMA_ROOT/.cache/c3-validation/final-run/integration:$(lake env printenv LEAN_PATH)"
for mod in NativeQuadraticSlopeSignatureSeparation NativeSlopeResidualExactTfvdSignGate NativeTwoModeSlopeSignAdversary NativeTwoModeSamePencilOppositeSign AuditNativeSlopeSignSeparation; do
  echo "[Lean -DwarningAsError=true] $mod"
  lean -DwarningAsError=true --root="$P/lean" -o "$P/lean/$mod.olean" "$P/lean/$mod.lean"
done
echo "PASS: positive quadratic slope gauge preserves all finite PSD, C2 exact theta/TFVD signed mass gate, exact same nodes/opposite Gram sign pencil, axiom audit"
