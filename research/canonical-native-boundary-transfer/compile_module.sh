#!/usr/bin/env bash
set -euo pipefail

research_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
geometry_root="/home/thlinux/geometry-of-numbers"
check_only=false

if [[ "${1:-}" == "--check" ]]; then
  check_only=true
  shift
fi

module_name="${1:?module name required}"
operator_root="${2:-/home/thlinux/carry-self-adjoint-operator}"
[[ "$module_name" =~ ^[A-Za-z][A-Za-z0-9]*$ ]]
export PATH=/home/thlinux/.elan/bin:"$PATH"

if [[ ! -d "$operator_root/.lake" ]]; then
  echo "ERROR: missing active Lean project cache at $operator_root/.lake; aborting without starting a new heavy build." >&2
  exit 2
fi

if [[ ! -d "$operator_root/.lake/build/lib/lean" ]]; then
  echo "ERROR: missing Lean library cache under $operator_root/.lake/build/lib/lean; compile aborted before any additional build." >&2
  exit 2
fi

output_cache="$operator_root/.lake/build/research/canonical-native-boundary-transfer"
mkdir -p -- "$output_cache"

geometry_dirs=(
  "$geometry_root/.lake/build/research/structural-native-krylov-gap"
  "$geometry_root/.lake/build/research/sixth-odd-twelve-sources"
  "$geometry_root/.lake/build/research/sixth-even-source-schur"
  "$geometry_root/.lake/build/research/critical-source-return"
  "$geometry_root/.lake/build/research/theta-fifth-odd-pattern"
  "$geometry_root/.lake/build/research/seventh-even-centered-source"
  "$geometry_root/.lake/build/research/return-block-compatibility"
  "$operator_root/.lake/build/lib/lean"
)

required_olean=(
  "$geometry_root/.lake/build/research/structural-native-krylov-gap/CanonicalClockGap.olean"
  "$geometry_root/.lake/build/research/structural-native-krylov-gap/Regression.olean"
  "$operator_root/.lake/build/lib/lean/CarrySelfAdjointOperator/CompletedNativeChiralBoundaryParityCoordinates.olean"
)

if [[ "$check_only" == true ]]; then
  missing_any=false
  echo "geometry_root=$geometry_root"
  echo "operator_root=$operator_root"
  echo "output_cache=$output_cache"
  for dep in "${geometry_dirs[@]}"; do
    if [[ -d "$dep" ]]; then
      echo "DEPENDENCY_DIR_OK=$dep"
    else
      echo "DEPENDENCY_DIR_MISSING=$dep"
      missing_any=true
    fi
  done
  for dep in "${required_olean[@]}"; do
    if [[ -f "$dep" ]]; then
      echo "OLEAN_OK=$dep"
    else
      echo "OLEAN_MISSING=$dep"
      missing_any=true
    fi
  done
  if [[ "$missing_any" == true ]]; then
    exit 2
  fi
  exit 0
fi

for dep in "${geometry_dirs[@]}"; do
  if [[ ! -d "$dep" ]]; then
    echo "ERROR: missing dependency cache $dep; capstone compile aborted without reconstructing the full environment." >&2
    exit 2
  fi
done

for dep in "${required_olean[@]}"; do
  if [[ ! -f "$dep" ]]; then
    echo "ERROR: missing required .olean $dep; capstone compile aborted before a new heavy build." >&2
    exit 2
  fi
done

cd -- "$operator_root"
lean_executable="$(lake env sh -c 'command -v lean')"
operator_lpath="$(lake env printenv LEAN_PATH)"
LEAN_PATH="$output_cache:$(IFS=:; echo "${geometry_dirs[*]}"):$operator_lpath" \
  "$lean_executable" -DwarningAsError=true --root="$research_dir" \
  -o "$output_cache/$module_name.olean" "$research_dir/$module_name.lean"
