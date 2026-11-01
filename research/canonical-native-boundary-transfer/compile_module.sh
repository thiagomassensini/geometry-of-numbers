#!/usr/bin/env bash
set -euo pipefail
research_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$research_dir/../.." && pwd)"
operator_root="${2:-/home/thlinux/carry-self-adjoint-operator}"
module_name="${1:?module name required}"
[[ "$module_name" =~ ^[A-Za-z][A-Za-z0-9]*$ ]]
export PATH=/home/thlinux/.elan/bin:"$PATH"

if [[ ! -d "$operator_root/.lake" ]]; then
  echo "ERROR: missing active Lean project cache at $operator_root/.lake; aborting without starting a new heavy build." >&2
  exit 2
fi

if [[ ! -d "$operator_root/.lake/build/lib/lean" ]]; then
  echo "ERROR: missing Lean library cache under $operator_root/.lake/build/lib/lean; compile aborted before any additional build." >&2
  exit 2
fi

operator_cache_root="$operator_root/.lake/build"
this_cache="$operator_cache_root/research/canonical-native-boundary-transfer"
struct_cache="$operator_cache_root/research/structural-native-krylov-gap"
odd_cache="$operator_cache_root/research/sixth-odd-twelve-sources"
even_cache="$operator_cache_root/research/sixth-even-source-schur"
critical_cache="$operator_cache_root/research/critical-source-return"
pattern_cache="$operator_cache_root/research/theta-fifth-odd-pattern"
seventh_cache="$operator_cache_root/research/seventh-even-centered-source"

required_caches=(
  "$this_cache"
  "$struct_cache"
  "$odd_cache"
  "$even_cache"
  "$critical_cache"
  "$pattern_cache"
  "$seventh_cache"
  "$operator_cache_root/lib/lean"
)

for dep in "${required_caches[@]}"; do
  if [[ ! -d "$dep" ]]; then
    echo "ERROR: missing dependency cache $dep; capstone compile aborted without reconstructing the full environment." >&2
    exit 2
  fi
done

mkdir -p -- "$this_cache"
cd -- "$operator_root"
lean_executable="$(lake env sh -c 'command -v lean')"
operator_lpath="$(lake env printenv LEAN_PATH)"
LEAN_PATH="$this_cache:$struct_cache:$odd_cache:$even_cache:$critical_cache:$pattern_cache:$seventh_cache:$operator_cache_root/lib/lean:$operator_lpath" \
  "$lean_executable" -DwarningAsError=true --root="$research_dir" \
  -o "$this_cache/$module_name.olean" "$research_dir/$module_name.lean"
