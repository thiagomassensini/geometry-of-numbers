#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 ModuleName" >&2
  exit 2
fi

task_dir=$(cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(cd -- "$task_dir/../.." && pwd)
reference_root=${SIGMA_REFERENCE_ROOT:-/home/thlinux/geometry-of-numbers-native-moving-schur-sigma}
carry_root=${CARRY_LEAN_ROOT:-/home/thlinux/carry-self-adjoint-operator}

if [[ ! -d "$reference_root/research" ]]; then
  reference_root=$repo_root
fi

export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$task_dir/.cache"
cd "$carry_root"

dependency_caches=$(find "$reference_root/research" -type d -name .cache -printf '%p:' 2>/dev/null || true)
research_builds=$(find "$reference_root/.lake/build/research" -mindepth 1 -maxdepth 1 -type d -printf '%p:' 2>/dev/null || true)
export LEAN_PATH="$task_dir/.cache:$dependency_caches$research_builds:$reference_root/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"

module=$1
lean -DwarningAsError=true --root="$task_dir" \
  -o "$task_dir/.cache/$module.olean" "$task_dir/$module.lean"
