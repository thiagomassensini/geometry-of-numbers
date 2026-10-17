#!/usr/bin/env bash
set -euo pipefail
research_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$research_dir/../.." && pwd)"
operator_root="${2:-$repo_root/../carry-self-adjoint-operator}"
module_name="${1:?module name required}"
[[ "$module_name" =~ ^[A-Za-z][A-Za-z0-9]*$ ]]
export PATH=/home/thlinux/.elan/bin:"$PATH"
cd -- "$operator_root"
lean_executable="$(lake env sh -c 'command -v lean')"
operator_lpath="$(lake env printenv LEAN_PATH)"
task_cache="$repo_root/.lake/build/research/corrected-green-source-ports"
prime_cache="$repo_root/.lake/build/research/prime-camera-schur"
prior_cache="$repo_root/.lake/build/research/material-pivot-certificate"
mkdir -p -- "$task_cache"
LEAN_PATH="$task_cache:$prime_cache:$prior_cache:$repo_root/.lake/build/lib/lean:$operator_lpath" \
  "$lean_executable" -DwarningAsError=true --root="$research_dir" \
  -o "$task_cache/$module_name.olean" "$research_dir/$module_name.lean"
