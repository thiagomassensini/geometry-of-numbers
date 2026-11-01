#!/usr/bin/env bash
set -euo pipefail
research_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$research_dir/../.." && pwd)"
operator_root="${2:-/home/thlinux/carry-self-adjoint-operator}"
module_name="${1:?module name required}"
[[ "$module_name" =~ ^[A-Za-z][A-Za-z0-9]*$ ]]
export PATH=/home/thlinux/.elan/bin:"$PATH"
cd -- "$operator_root"
lean_executable="$(lake env sh -c 'command -v lean')"
operator_lpath="$(lake env printenv LEAN_PATH)"
this_cache="$repo_root/.lake/build/research/canonical-native-boundary-transfer"
struct_cache="$repo_root/.lake/build/research/structural-native-krylov-gap"
odd_cache="$repo_root/.lake/build/research/sixth-odd-twelve-sources"
even_cache="$repo_root/.lake/build/research/sixth-even-source-schur"
critical_cache="$repo_root/.lake/build/research/critical-source-return"
pattern_cache="$repo_root/.lake/build/research/theta-fifth-odd-pattern"
seventh_cache="$repo_root/.lake/build/research/seventh-even-centered-source"
mkdir -p -- "$this_cache"
LEAN_PATH="$this_cache:$struct_cache:$odd_cache:$even_cache:$critical_cache:$pattern_cache:$seventh_cache:$repo_root/.lake/build/lib/lean:$operator_lpath" \
  "$lean_executable" -DwarningAsError=true --root="$research_dir" \
  -o "$this_cache/$module_name.olean" "$research_dir/$module_name.lean"
