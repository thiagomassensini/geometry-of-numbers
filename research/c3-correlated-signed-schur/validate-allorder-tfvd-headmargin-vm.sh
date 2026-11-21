#!/usr/bin/env bash
set -euo pipefail
P="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CSA_REPO="${CSA_REPO:-/home/thlinux/carry-self-adjoint-operator}"
SOURCE_CACHE="${SOURCE_CACHE:-/home/thlinux/worktrees/tfvd-bezout-order-compensation-20261110/research/tfvd-bezout-order-compensation/.cache}"
test -f "$SOURCE_CACHE/TfvdBoundaryLaw.olean"
cd "$CSA_REPO"
export LEAN_PATH="$P/lean:$SOURCE_CACHE:$(lake env printenv LEAN_PATH)"
for module in AllOrderTfvdHeadMarginBootstrap AuditAllOrderTfvdHeadMarginBootstrap; do
  echo "[lean] $module"
  lean -DwarningAsError=true --root="$P/lean" -o "$P/lean/$module.olean" "$P/lean/$module.lean"
done
echo "PASS: source-first all-order TFVD head-margin bootstrap and four axiom audits"
