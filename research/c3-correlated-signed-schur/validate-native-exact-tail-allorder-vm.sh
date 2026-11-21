#!/usr/bin/env bash
set -euo pipefail
P="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CSA_ROOT="${CSA_ROOT:-/home/thlinux/carry-self-adjoint-operator}"
SOURCE_CACHE="${SOURCE_CACHE:-/home/thlinux/worktrees/tfvd-bezout-order-compensation-20261110/research/tfvd-bezout-order-compensation/.cache}"
test -f "$SOURCE_CACHE/LiteralTfvd.olean"
test -f "$SOURCE_CACHE/TfvdBoundaryLaw.olean"
cd "$CSA_ROOT"
export LEAN_PATH="$P/lean:$SOURCE_CACHE:$(lake env printenv LEAN_PATH)"
for module in NativeExactTailSchurThetaGreenConservation NativeExactTailAllJetSignedMassGate NativeExactTailSignNoGo AuditNativeExactTailAllOrder; do
  echo "[Lean -DwarningAsError=true] $module"
  lean -DwarningAsError=true --root="$P/lean" -o "$P/lean/$module.olean" "$P/lean/$module.lean"
done
echo "PASS: exact head/tail 4-term Schur and all-jets theta/Green conservation, signed mass criterion, strict algebraic no-go, axioms"
