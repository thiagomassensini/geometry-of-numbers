#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
task_dir=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$task_dir/../.." && pwd)
cd /home/thlinux/carry-self-adjoint-operator
mkdir -p "$task_dir/.cache"
export LEAN_PATH="$task_dir/.cache:$task_dir/.cache/pr42:$task_dir/../completed-readout-multiplier-bounds/.cache:$task_dir/../tfvd-infinite-fourth-tail/.cache:$task_dir/../native-cell-jet-tail-bounds/.cache:$task_dir/../material-green-summation-parts/.cache:$task_dir/../tfvd-complete-green-residual/.cache:$task_dir/../native-green-phase-compensation/.cache:$task_dir/../forcing-mixed-green-slope/.cache:$task_dir/../forcing-centered-native-residual/.cache:$task_dir/../forcing-centered-native-residual/.cache/pr37:$task_dir/.cache/pr37:$task_dir/../native-cauchy-residual-return/.cache:$repo/.lake/build/research/completed-green-confluent-balance:$task_dir/../native-return-boundary-deflation/.cache:$task_dir/../native-positive-square-kernel/.cache:$task_dir/../source-euler-residual-control/.cache:$task_dir/../source-euler-residual-control/.cache/pr34:$task_dir/../native-jet-overlap-budget/.cache:$task_dir/../native-jet-overlap-budget/.cache/pr41:$repo/.lake/build/lib/lean:$task_dir/../native-fiber-transport/.cache:$task_dir/../physical-trace-fiber/.cache:$repo/.lake/build/research/sixth-odd-twelve-sources:$repo/.lake/build/research/sixth-even-source-schur:$repo/.lake/build/research/theta-fifth-odd-pattern:$repo/.lake/build/research/critical-source-return:$repo/.lake/build/research/return-block-compatibility:$repo/.lake/build/research/corrected-green-source-ports:$repo/.lake/build/research/material-integral-certificate:$repo/.lake/build/research/prime-camera-schur:$repo/.lake/build/research/material-pivot-certificate:$(lake env printenv LEAN_PATH)"
if [[ "$1" == "SourceLeading" || "$1" == "WholeSourceLimit" ]]; then
  lean -DwarningAsError=true --root="$task_dir/.cache/pr42/source" -o "$task_dir/.cache/pr42/$1.olean" "$task_dir/.cache/pr42/source/$1.lean"

else
  lean -DwarningAsError=true --root="$task_dir" -o "$task_dir/.cache/$1.olean" "$task_dir/$1.lean"
fi
