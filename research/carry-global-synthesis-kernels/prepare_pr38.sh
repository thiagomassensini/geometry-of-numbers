#!/usr/bin/env bash
set -euo pipefail
research_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$research_dir/../.." && pwd)"
operator_root="${1:-$repo_root/../carry-self-adjoint-operator}"
scale_ref=16de0ef478afb1c95c16edfe8153ac80dc035b71
export PATH=/home/thlinux/.elan/bin:"$PATH"
cd -- "$operator_root"
lean_executable="$(lake env sh -c 'command -v lean')"
operator_lpath="$(lake env printenv LEAN_PATH)"
source_cache="$repo_root/.lake/build/research/carry-global-synthesis-kernels/pr38-source"
library_cache="$repo_root/.lake/build/research/carry-global-synthesis-kernels/pr38-lib"
mkdir -p "$source_cache/GeometryOfNumbers/Analysis" "$library_cache/GeometryOfNumbers/Analysis"
# Lean resolves the GeometryOfNumbers package at its first library root.
# Copy its existing build products into this isolated overlay before replacing
# only the four PR38 modules; never write through a link to the project cache.
cp -a --reflink=auto "$repo_root/.lake/build/lib/lean/GeometryOfNumbers/." "$library_cache/GeometryOfNumbers/"
for module in CarryScaleGeometry MomentScaleElimination MomentScaleHeight LogDerivativeScale; do
  module_path="GeometryOfNumbers/Analysis/$module.lean"
  git -C "$repo_root" show "$scale_ref:$module_path" > "$source_cache/$module_path"
  LEAN_PATH="$library_cache:$repo_root/.lake/build/lib/lean:$operator_lpath" \
    "$lean_executable" -DwarningAsError=true --root="$source_cache" \
      -o "$library_cache/GeometryOfNumbers/Analysis/$module.olean" "$source_cache/$module_path"
done
git -C "$repo_root" show "$scale_ref:research/carry-scale-covariance/NativeScaleSeam.lean" > "$source_cache/NativeScaleSeam.lean"
LEAN_PATH="$library_cache:$repo_root/.lake/build/lib/lean:$operator_lpath" \
  "$lean_executable" -DwarningAsError=true --root="$source_cache" \
    -o "$library_cache/NativeScaleSeam.olean" "$source_cache/NativeScaleSeam.lean"
echo "PASS: PR38 source compiled read-only at $scale_ref; no checkout or pin changed"
