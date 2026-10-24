#!/usr/bin/env bash
set -euo pipefail
task_dir=$(cd -- "$(dirname -- "$0")" && pwd)
export PATH="$HOME/.elan/bin:$PATH"
cd /home/thlinux/carry-self-adjoint-operator
mkdir -p "$task_dir/.cache"
paths="$task_dir/.cache"
for name in physical-cauchy-endpoint-domain native-completed-pairing tfvd-green-provenance-mellin tfvd-four-leg-mellin native-camera-tail-mellin material-theta-tfvd-port; do
  paths="$paths:$task_dir/../$name/.cache"
done
export LEAN_PATH="$paths:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"
source_file=${2:-"$task_dir/$1.lean"}
source_dir=$(dirname -- "$source_file")
mkdir -p "$source_dir/.cache"
lean -DwarningAsError=true --root="$source_dir" -o "$source_dir/.cache/$1.olean" "$source_file"
