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
output_dir=${SIGMA_OUTPUT_DIR:-}
height50_build=${SIGMA_HEIGHT50_BUILD:-}
lean_bin=${LEAN_BIN:-$(cd -- "$repo_root" && elan which lean)}

if [[ ! -d "$reference_root/research" ]]; then
  reference_root=$repo_root
fi

export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$task_dir/.cache"
if [[ -z "$output_dir" ]]; then
  output_dir="$task_dir/.cache"
fi
mkdir -p "$output_dir"
cd "$carry_root"

dependency_caches=$(find "$reference_root/research" -type d -name .cache -printf '%p:' 2>/dev/null || true)
research_builds=$(find "$reference_root/.lake/build/research" -mindepth 1 -maxdepth 1 -type d -printf '%p:' 2>/dev/null || true)
export LEAN_PATH="$output_dir:$height50_build:$task_dir/.cache:$dependency_caches$research_builds:$reference_root/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"

mem_gate() {
  [[ -r /proc/meminfo ]] || return 0
  while [[ "$(awk '/^MemAvailable/ {print int($2 / 1048576)}' /proc/meminfo)" -lt 30 ]]; do
    echo "== waiting: MemAvailable below 30 GiB"
    sleep 30
  done
}

module=$1
mem_gate
"$lean_bin" -DwarningAsError=true --root="$task_dir" \
  -o "$output_dir/$module.olean" "$task_dir/$module.lean"
