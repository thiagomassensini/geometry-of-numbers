#!/usr/bin/env bash
# Usage: bash validate-radial-schur.sh /path/to/prebuilt/gon /path/to/prebuilt/csa
set -euo pipefail

if [[ $# != 2 ]]; then
  printf 'Usage: bash %s PREBUILT_GON PREBUILT_CSA\n' "$0" >&2
  exit 2
fi

root=$(cd "$(dirname "$0")/../.." && pwd)
gon=$(cd "$1" && pwd)
csa=$(cd "$2" && pwd)
research="$gon/research"
export PATH="$HOME/.elan/bin:$PATH"

for file in "$gon/.lake/build/lib/lean/CanonicalComparison.olean" \
            "$research/native-cauchy-residual-return/.cache/ResidualReturn.olean"; do
  if [[ ! -f "$file" ]]; then
    printf 'Required prebuilt module missing: %s\n' "$file" >&2
    exit 3
  fi
done

# Match the dependency precedence of native-cauchy-residual-return/compile_module.sh.
cache_dirs=(
  "$research/native-cauchy-residual-return/.cache"
  "$research/native-return-boundary-deflation/.cache"
  "$research/native-positive-square-kernel/.cache"
  "$research/source-euler-residual-control/.cache"
  "$research/source-euler-residual-control/.cache/pr34"
  "$research/native-jet-overlap-budget/.cache"
  "$research/native-jet-overlap-budget/.cache/pr41"
  "$gon/.lake/build/lib/lean"
  "$research/native-fiber-transport/.cache"
  "$research/physical-trace-fiber/.cache"
)
for dir in sixth-odd-twelve-sources sixth-even-source-schur theta-fifth-odd-pattern \
           critical-source-return return-block-compatibility corrected-green-source-ports \
           material-integral-certificate prime-camera-schur material-pivot-certificate; do
  cache_dirs+=("$gon/.lake/build/research/$dir")
done

cd "$csa"
csa_path=$(lake env printenv LEAN_PATH)
lean_exe=$(lake env sh -c 'command -v lean')
prefix=$(IFS=:; printf '%s' "${cache_dirs[*]}")
export LEAN_PATH="$prefix:$csa_path"

"$lean_exe" --version
"$lean_exe" -DwarningAsError=true \
  "$root/research/native-cauchy-residual-return/RadialPickSchur.lean"
"$lean_exe" -DwarningAsError=true \
  "$root/research/material-central-calibration/PhysicalRadialAllOrderDeterminant.lean"
