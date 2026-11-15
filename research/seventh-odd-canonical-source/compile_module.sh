#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
operator_root=/home/thlinux/worktrees/luna-fonte-c2-error-transport-20261115
baseline_root=/home/thlinux/geometry-of-numbers
module_name="${1:?module name required}"
[[ "$module_name" =~ ^[A-Za-z][A-Za-z0-9]*$ ]]
export PATH=/home/thlinux/.elan/bin:"$PATH"
mkdir -p "$repo_root/.lake/build/research/seventh-odd-canonical-source"
mkdir -p "$operator_root/.lake/build/lib/lean"
cd "$operator_root"
operator_lpath="$(lake env printenv LEAN_PATH)"
research_lpath="$(find "$baseline_root/.lake/build/research" -type f -name '*.olean' -printf '%h\n' | sort -u | paste -sd: -)"
LEAN_PATH="$repo_root/.lake/build/research/seventh-odd-canonical-source:$repo_root/.lake/build/lib/lean:$baseline_root/.lake/build/lib/lean:$research_lpath:/home/thlinux/carry-self-adjoint-operator/.lake/build/lib/lean:$operator_lpath" \
  lean -DwarningAsError=true --root="$repo_root/research/seventh-odd-canonical-source" \
  -o "$repo_root/.lake/build/research/seventh-odd-canonical-source/$module_name.olean" \
  "$repo_root/research/seventh-odd-canonical-source/$module_name.lean"
