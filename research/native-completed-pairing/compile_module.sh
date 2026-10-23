#!/usr/bin/env bash
set -euo pipefail
task_dir=$(cd -- "$(dirname -- "$0")" && pwd)
export PATH="$HOME/.elan/bin:$PATH"
cd /home/thlinux/carry-self-adjoint-operator
mkdir -p "$task_dir/.cache"
export LEAN_PATH="$task_dir/.cache:$task_dir/../tfvd-green-provenance-mellin/.cache:$task_dir/../tfvd-four-leg-mellin/.cache:$task_dir/../native-camera-tail-mellin/.cache:$task_dir/../material-theta-tfvd-port/.cache:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"
lean -DwarningAsError=true --root="$task_dir" -o "$task_dir/.cache/$1.olean" "$task_dir/$1.lean"
