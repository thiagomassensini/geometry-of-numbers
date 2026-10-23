#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
task_dir=$(cd "$(dirname "$0")" && pwd)
cd /home/thlinux/carry-self-adjoint-operator
mkdir -p "$task_dir/.cache"
export LEAN_PATH="$task_dir/.cache:$(lake env printenv LEAN_PATH)"
lean -DwarningAsError=true --root="$task_dir" -o "$task_dir/.cache/$1.olean" "$task_dir/$1.lean"
