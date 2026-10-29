#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
task_dir=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$task_dir/../.." && pwd)
cd /home/thlinux/carry-self-adjoint-operator
mkdir -p "$task_dir/.cache"
export LEAN_PATH="$task_dir/.cache:$repo/.lake/build/lib/lean:$repo/.lake/build/research/sixth-odd-twelve-sources:$repo/.lake/build/research/sixth-even-source-schur:$repo/.lake/build/research/theta-fifth-odd-pattern:$repo/.lake/build/research/critical-source-return:$repo/.lake/build/research/return-block-compatibility:$repo/.lake/build/research/corrected-green-source-ports:$repo/.lake/build/research/material-integral-certificate:$repo/.lake/build/research/prime-camera-schur:$repo/.lake/build/research/material-pivot-certificate:$(lake env printenv LEAN_PATH)"
lean -DwarningAsError=true --root="$task_dir" -o "$task_dir/.cache/$1.olean" "$task_dir/$1.lean"
