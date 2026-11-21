#!/usr/bin/env bash
set -euo pipefail
P="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="${GON_REPO:-/home/thlinux/geometry-of-numbers}"
CSA_REPO="${CSA_REPO:-/home/thlinux/carry-self-adjoint-operator}"
task_dir="$repo/research/native-return-boundary-deflation"
cd "$CSA_REPO"
eval "$(grep '^export LEAN_PATH=' "$task_dir/compile_module.sh")"
export LEAN_PATH="$P/lean:$LEAN_PATH"
for mod in NativeTwoPointSchurSourcePositivity NativeTwoPointTfvdSourcePositivity AuditNativeTwoPointTfvdSchur; do
    echo "[Lean, -DwarningAsError=true] $mod"
    lean -DwarningAsError=true --root="$P/lean" -o "$P/lean/$mod.olean" "$P/lean/$mod.lean"
done
echo "PASS: original physical 2-point Schur and material TFVD PSD, plus axiom audit"
