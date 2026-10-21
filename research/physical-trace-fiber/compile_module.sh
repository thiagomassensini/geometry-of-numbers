#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
task_dir=$(cd "$(dirname "$0")" && pwd)
operator_dir=/home/thlinux/carry-self-adjoint-operator
cache_dir="$task_dir/.cache"
mkdir -p "$cache_dir"
cd "$operator_dir"
export LEAN_PATH="$cache_dir:$(lake env printenv LEAN_PATH)"
lean -DwarningAsError=true --root="$task_dir" -o "$cache_dir/$1.olean" "$task_dir/$1.lean"
