#!/usr/bin/env bash
set -euo pipefail
research_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$research_dir/../.." && pwd)"
operator_root="${2:-$repo_root/../carry-self-adjoint-operator}"
module_name="${1:?module name required}"
[[ "$module_name" =~ ^[A-Za-z][A-Za-z0-9]*$ ]]
export PATH=/home/thlinux/.elan/bin:"$PATH"
cd -- "$operator_root"
task_cache="$repo_root/.lake/build/research/critical-source-coefficient-law"
mkdir -p -- "$task_cache"
research_cache="$repo_root/.lake/build/research"
previous_paths="$research_cache/critical-source-mixed-readout:$research_cache/critical-source-relative-asymptotics:$research_cache/native-moment-orthogonalization-audit:$research_cache/critical-source-return:$research_cache/return-block-compatibility:$research_cache/corrected-green-source-ports:$research_cache/material-integral-certificate:$research_cache/prime-camera-schur:$research_cache/material-pivot-certificate"
LEAN_PATH="$task_cache:$previous_paths:$repo_root/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)" \
  "$(lake env sh -c 'command -v lean')" -DwarningAsError=true --root="$research_dir" \
  -o "$task_cache/$module_name.olean" "$research_dir/$module_name.lean"
