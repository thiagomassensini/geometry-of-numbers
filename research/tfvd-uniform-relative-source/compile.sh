#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
proof_root=${CARRY_PR70_ROOT:-/home/thlinux/geometry-of-numbers/research/tfvd-bezout-schur-residual}
export PATH="$HOME/.elan/bin:$PATH"
cd /home/thlinux/carry-self-adjoint-operator
mkdir -p "$here/.cache"
export LEAN_PATH="$here/.cache:$proof_root/.cache:$(lake env printenv LEAN_PATH)"
lean -DwarningAsError=true --root="$here" -o "$here/.cache/$1.olean" "$here/$1.lean"
