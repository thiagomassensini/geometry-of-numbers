#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
proof_root=${CARRY_PR70_ROOT:-/home/thlinux/geometry-of-numbers/research/tfvd-bezout-schur-residual}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
previous=${CARRY_PR143_CACHE:-/home/thlinux/geometry-of-numbers-tfvd-uniform-relative-source/research/tfvd-uniform-relative-source/.cache}
task_dir=$(cd "$proof_root/../c3-fourteenth-tail" && pwd)
repo=$(cd "$task_dir/../.." && pwd)
cd /home/thlinux/carry-self-adjoint-operator
mkdir -p "$task_dir/.cache"
export LEAN_PATH="$task_dir/.cache:$task_dir/../c3-gamma-jet-enclosures/.cache:$task_dir/../tfvd-two-even-jet-determinant/.cache:$task_dir/../tfvd-joint-response-transport/.cache:$task_dir/../tfvd-critical-two-port-ledger/.cache:$task_dir/../native-negative-direction-test/.cache:$task_dir/../radial-cauchy-conservative-test/.cache:$task_dir/../native-conservative-intertwiner/.cache:$task_dir/../native-conservative-intertwiner/.cache/pr42:$task_dir/.cache:$task_dir/.cache/pr42:$task_dir/../completed-readout-multiplier-bounds/.cache:$task_dir/../tfvd-infinite-fourth-tail/.cache:$task_dir/../native-cell-jet-tail-bounds/.cache:$task_dir/../material-green-summation-parts/.cache:$task_dir/../tfvd-complete-green-residual/.cache:$task_dir/../native-green-phase-compensation/.cache:$task_dir/../forcing-mixed-green-slope/.cache:$task_dir/../forcing-centered-native-residual/.cache:$task_dir/../forcing-centered-native-residual/.cache/pr37:$task_dir/.cache/pr37:$task_dir/../native-cauchy-residual-return/.cache:$repo/.lake/build/research/completed-green-confluent-balance:$task_dir/../native-return-boundary-deflation/.cache:$task_dir/../native-positive-square-kernel/.cache:$task_dir/../source-euler-residual-control/.cache:$task_dir/../source-euler-residual-control/.cache/pr34:$task_dir/../native-jet-overlap-budget/.cache:$task_dir/../native-jet-overlap-budget/.cache/pr41:$repo/.lake/build/lib/lean:$task_dir/../native-fiber-transport/.cache:$task_dir/../physical-trace-fiber/.cache:$repo/.lake/build/research/sixth-odd-twelve-sources:$repo/.lake/build/research/sixth-even-source-schur:$repo/.lake/build/research/theta-fifth-odd-pattern:$repo/.lake/build/research/critical-source-return:$repo/.lake/build/research/return-block-compatibility:$repo/.lake/build/research/corrected-green-source-ports:$repo/.lake/build/research/material-integral-certificate:$repo/.lake/build/research/prime-camera-schur:$repo/.lake/build/research/material-pivot-certificate:$(lake env printenv LEAN_PATH)"
mkdir -p "$here/.cache"
export LEAN_PATH="$here/.cache:$previous:$proof_root/.cache:$LEAN_PATH"
export LEAN_PATH="${CARRY_PR145_CACHE:-/home/thlinux/geometry-of-numbers-c3-source-orientation/research/c3-source-orientation/.cache}:$LEAN_PATH"
export LEAN_PATH="$here/.cache:${CARRY_PR146_CACHE:-/home/thlinux/geometry-of-numbers-critical-tilt-prime/research/c3-tilt-prime/.cache}:$LEAN_PATH"
lean -DwarningAsError=true --root="$here" -o "$here/.cache/$1.olean" "$here/$1.lean"
