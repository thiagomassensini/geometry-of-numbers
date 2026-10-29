#!/usr/bin/env bash
set -euo pipefail
research_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$research_dir/../.." && pwd)"
operator_root="${2:-$repo_root/../carry-self-adjoint-operator}"
module_name="${1:?module name required}"
[[ "$module_name" =~ ^[A-Za-z][A-Za-z0-9]*$ ]]
export PATH=/home/thlinux/.elan/bin:"$PATH"
cd -- "$repo_root"
task_cache="$repo_root/.lake/build/research/native-moment-orthogonalization-audit"
mkdir -p -- "$task_cache"
operator_lpath="$(cd -- "$operator_root" && lake env printenv LEAN_PATH)"
LEAN_PATH="$task_cache:$(lake env printenv LEAN_PATH):$operator_lpath" \
  "$(lake env sh -c 'command -v lean')" -DwarningAsError=true --root="$research_dir" \
  -o "$task_cache/$module_name.olean" "$research_dir/$module_name.lean"
