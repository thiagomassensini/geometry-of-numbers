#!/usr/bin/env bash
set -euo pipefail
task_dir=$(cd -- "$(dirname -- "$0")" && pwd)
export PATH="$HOME/.elan/bin:$PATH"
cd /home/thlinux/carry-self-adjoint-operator
mkdir -p "$task_dir/.cache"
export LEAN_PATH="$task_dir/.cache:$task_dir/../native-principal-boundary-flow/.cache:$task_dir/../native-critical-address-split/.cache:$task_dir/../native-critical-squared-grid/.cache:$task_dir/../native-all-order-odd-cauchy/.cache:$task_dir/../native-cubic-odd-green-defect/.cache:$task_dir/../native-odd-green-compensation/.cache:$task_dir/../native-cross-radial-green-cubic/.cache:$task_dir/../native-cross-radial-green-leading/.cache:$task_dir/../native-cross-radial-complete-pairing/.cache:$task_dir/../native-mixed-imaginary-law/.cache:$task_dir/../native-even-odd-complete-pairing/.cache:$task_dir/../native-odd-energy-correction/.cache:$task_dir/../native-all-order-energy-correction/.cache:$task_dir/../all-order-binomial-green/.cache:$task_dir/../native-all-order-spatial-correction/.cache:$task_dir/../native-cubic-quartic-factor/.cache:$task_dir/../native-cubic-tfvd-numerator/.cache:$task_dir/../native-all-order-stencil-boundary/.cache:$task_dir/../native-linear-tfvd-traces/.cache:$task_dir/../native-quartic-boundary-sign/.cache:$task_dir/../native-curvature-green-factor/.cache:$task_dir/../native-critical-tfvd-cancellation/.cache:$task_dir/../native-commutator-mixed-control/.cache:$task_dir/../native-tfvd-completed-transport/.cache:$task_dir/../native-vertical-synthesis/.cache:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"
source_file=${2:-"$task_dir/$1.lean"}
source_dir=$(dirname -- "$source_file")
mkdir -p "$source_dir/.cache"
lean -DwarningAsError=true --root="$source_dir" -o "$source_dir/.cache/$1.olean" "$source_file"
