#!/usr/bin/env bash
set -euo pipefail
research_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$research_dir/../.." && pwd)"
operator_root="${2:-$repo_root/../carry-self-adjoint-operator}"
module_name="${1:?module required}"
[[ "$module_name" =~ ^[A-Za-z][A-Za-z0-9]*$ ]]
export PATH=/home/thlinux/.elan/bin:"$PATH"
cd -- "$operator_root"
lean_executable="$(lake env sh -c 'command -v lean')"
operator_lpath="$(lake env printenv LEAN_PATH)"
build_root="$repo_root/.lake/build"
task_cache="$build_root/research/all-order-polarized-tail"
mkdir -p -- "$task_cache"
deps="$task_cache"
for folder in theta-fifth-odd-pattern critical-source-return return-block-compatibility corrected-green-source-ports material-integral-certificate prime-camera-schur material-pivot-certificate; do
  deps="$deps:$build_root/research/$folder"
done
LEAN_PATH="$deps:$build_root/lib/lean:$operator_lpath" \
  "$lean_executable" -DwarningAsError=true --root="$research_dir" \
  -o "$task_cache/$module_name.olean" "$research_dir/$module_name.lean"
