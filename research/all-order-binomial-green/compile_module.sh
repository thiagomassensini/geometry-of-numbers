#!/usr/bin/env bash
set -euo pipefail
task_dir=$(cd -- "$(dirname -- "$0")" && pwd)
export PATH="$HOME/.elan/bin:$PATH"
cd /home/thlinux/carry-self-adjoint-operator
mkdir -p "$task_dir/.cache"
paths="$task_dir/.cache:$task_dir/.cache/pr41/.cache"
for name in polarized-green-jet-four critical-green-finite-part interior-green-critical first-odd-green finite-green-crossing mean-contrast-green radial-green-intertwiner radial-common-refinement completed-trace-kernel physical-cauchy-endpoint-domain native-completed-pairing tfvd-green-provenance-mellin tfvd-four-leg-mellin native-camera-tail-mellin material-theta-tfvd-port; do
  paths="$paths:$task_dir/../$name/.cache"
done
for name in sixth-odd-twelve-sources sixth-even-source-schur theta-fifth-odd-pattern critical-source-return return-block-compatibility corrected-green-source-ports material-integral-certificate prime-camera-schur material-pivot-certificate; do
  paths="$paths:/home/thlinux/geometry-of-numbers/.lake/build/research/$name"
done
export LEAN_PATH="$paths:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"
source_file=${2:-"$task_dir/$1.lean"}
source_dir=$(dirname -- "$source_file")
mkdir -p "$source_dir/.cache"
lean -DwarningAsError=true --root="$source_dir" -o "$source_dir/.cache/$1.olean" "$source_file"
