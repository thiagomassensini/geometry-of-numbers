#!/usr/bin/env bash
set -euo pipefail
task_dir=$(cd -- "$(dirname -- "$0")" && pwd)
export PATH="$HOME/.elan/bin:$PATH"
cd /home/thlinux/carry-self-adjoint-operator
mkdir -p "$task_dir/.cache"
export LEAN_PATH="$task_dir/.cache:$task_dir/../material-theta-tfvd-port/.cache:$(lake env printenv LEAN_PATH)"
lean -DwarningAsError=true --root="$task_dir" -o "$task_dir/.cache/$1.olean" "$task_dir/$1.lean"
