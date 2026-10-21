#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
task_dir=$(cd "$(dirname "$0")" && pwd)
operator_dir=/home/thlinux/carry-self-adjoint-operator
mkdir -p "$task_dir/.cache"
cd "$operator_dir"
export LEAN_PATH="$task_dir/.cache:$task_dir/../physical-trace-fiber/.cache:$(lake env printenv LEAN_PATH)"
lean -DwarningAsError=true --root="$task_dir" -o "$task_dir/.cache/$1.olean" "$task_dir/$1.lean"
