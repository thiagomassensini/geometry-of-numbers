#!/usr/bin/env bash
set -euo pipefail

task_dir=$(cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(cd -- "$task_dir/../.." && pwd)
carry_root=${CARRY_LEAN_ROOT:-/home/thlinux/carry-self-adjoint-operator}
greenframe_root="$repo_root/.lake/packages/GreenFrame"
output_dir=${SIGMA_OUTPUT_DIR:-"$task_dir/.cache/c1"}
lean_bin=${LEAN_BIN:-$(cd -- "$repo_root" && elan which lean)}

[[ $(cat "$repo_root/lean-toolchain") == "leanprover/lean4:v4.32.0" ]] || {
  echo "C1 requires Lean 4.32.0" >&2
  exit 1
}
case $("$lean_bin" --version) in
  "Lean (version 4.32.0,"*) ;;
  *) echo "Selected Lean binary is not Lean 4.32.0: $lean_bin" >&2; exit 1 ;;
esac
[[ $(jq -r '.packages[] | select(.name == "mathlib").rev' "$repo_root/lake-manifest.json") == \
  "81a5d257c8e410db227a6665ed08f64fea08e997" ]] || {
  echo "C1 requires Mathlib 81a5d257c8e410db227a6665ed08f64fea08e997" >&2
  exit 1
}
[[ $(cat "$carry_root/lean-toolchain") == "leanprover/lean4:v4.32.0" ]] || {
  echo "The Carry dependency must use Lean 4.32.0" >&2
  exit 1
}
[[ $(git -C "$greenframe_root" rev-parse HEAD) == "cd2d838bee67ad23f869a02f8ed9f0a0feb926fa" ]] || {
  echo "GreenFrame checkout does not match Geometry's pinned revision" >&2
  exit 1
}

carry_mathlib=$(jq -r '.packages[] | select(.name == "mathlib").rev' "$carry_root/lake-manifest.json")
carry_cpformal=$(jq -r '.packages[] | select(.name == "CPFormal").rev' "$carry_root/lake-manifest.json")
carry_geometry=$(jq -r '.packages[] | select(.name | contains("geometry-of-numbers")).rev' "$carry_root/lake-manifest.json")
carry_crosswalk=$(jq -r '.packages[] | select(.name == "NativeCarryC3Crosswalk").rev' "$carry_root/lake-manifest.json")
[[ $carry_mathlib == "81a5d257c8e410db227a6665ed08f64fea08e997" ]] || {
  echo "Carry Mathlib pin mismatch: $carry_mathlib" >&2
  exit 1
}
[[ $carry_cpformal == "65d50f6db1208708e109982ba97e1d51d3039956" ]] || {
  echo "Carry CPFormal pin mismatch: $carry_cpformal" >&2
  exit 1
}
[[ $carry_geometry == "d7cc54f5c485320f1fada33118e9e6101488819a" ]] || {
  echo "Carry geometry pin mismatch: $carry_geometry" >&2
  exit 1
}
[[ $carry_crosswalk == "150cfc7fb08da96bf8117f15869cc2b819d593c2" ]] || {
  echo "Carry crosswalk pin mismatch: $carry_crosswalk" >&2
  exit 1
}

carry_pin=045369f6dedcb2e75e9aefed1d12c9f73b9a2532
for source in \
  CarrySelfAdjointOperator/NativeBoundaryArchimedeanDressingSeparation.lean \
  CarrySelfAdjointOperator/NativeScalarGenuineIdentification.lean \
  CarrySelfAdjointOperator/CompletedNativePositiveJacobiResolventAnalytic.lean \
  CarrySelfAdjointOperator/NativeScalarZetaIdentification.lean \
  CarrySelfAdjointOperator/CompletedGreenJetCoefficientRecurrence.lean \
  CarrySelfAdjointOperator/NativeSourceAllOrderSchur.lean \
  CarrySelfAdjointOperator/CompletedNativeChiralEvenBoundaryStieltjesGate.lean \
  CarrySelfAdjointOperator/NativeCompletedCenteredReflection.lean \
  CarrySelfAdjointOperator/CompletedNativeRealWeylMoments.lean \
  CarrySelfAdjointOperator/CompletedGreenMomentJets.lean \
  CarrySelfAdjointOperator/CompletedNativeCentralChiralQuotientCurvature.lean \
  CarrySelfAdjointOperator/CompletedNativeTfvdWronskianMoments.lean; do
  expected=$(git -C "$carry_root" show "$carry_pin:$source" | sha256sum | cut -d ' ' -f 1)
  actual=$(sha256sum "$carry_root/$source" | cut -d ' ' -f 1)
  [[ $actual == "$expected" ]] || {
    echo "Carry source differs from pinned main: $source" >&2
    exit 1
  }
done
cpformal_root="$carry_root/.lake/packages/CPFormal"
[[ $(git -C "$cpformal_root" rev-parse HEAD) == "$carry_cpformal" ]] || {
  echo "CPFormal checkout does not match Carry manifest" >&2
  exit 1
}
[[ $(git -C "$carry_root/.lake/packages/mathlib" rev-parse HEAD) == "$carry_mathlib" ]] || {
  echo "Carry Mathlib checkout does not match Carry manifest" >&2
  exit 1
}
cpformal_source=CPFormal/Analytic/CpGenuineRealAxisPositivity.lean
expected=$(git -C "$cpformal_root" show "$carry_cpformal:$cpformal_source" | sha256sum | cut -d ' ' -f 1)
actual=$(sha256sum "$cpformal_root/$cpformal_source" | cut -d ' ' -f 1)
[[ $actual == "$expected" ]] || {
  echo "CPFormal source differs from Carry's pinned revision: $cpformal_source" >&2
  exit 1
}

mkdir -p "$output_dir"
exec > >(tee "$output_dir/build.log") 2>&1
target_lean_path=$(cd -- "$repo_root" && lake env printenv LEAN_PATH)
carry_lean_path=$(cd -- "$carry_root" && lake env printenv LEAN_PATH)
# Keep the pinned package search paths first. Lean's namespace package routing
# otherwise treats the fresh output root as the sole GreenFrame package root;
# placing it last still lets it provide modules rebuilt from source when a
# pinned package cache has no artifact.
export LEAN_PATH="$target_lean_path:$carry_lean_path:$output_dir"

mem_gate() {
  [[ -r /proc/meminfo ]] || return 0
  while (( $(awk '/^MemAvailable/ {print $2}' /proc/meminfo) < 30 * 1024 * 1024 )); do
    echo "== waiting: MemAvailable below 30 GiB"
    sleep 30
  done
}

compile() {
  local root="$1" rel="$2" source="$3"
  shift 3
  mkdir -p "$(dirname "$output_dir/${rel//.//}.olean")"
  mem_gate
  echo "== $rel"
  (cd "$root" && "$lean_bin" -j 2 -DwarningAsError=true "$@" --root="$root" \
    "$source" -o "$output_dir/${rel//.//}.olean")
}

compile_greenframe() {
  local rel="$1" source="$2"
  local output="$greenframe_root/.lake/build/lib/lean/${rel//.//}.olean"
  mkdir -p "$(dirname "$output")"
  mem_gate
  echo "== $rel (pinned GreenFrame package)"
  (cd "$greenframe_root" && "$lean_bin" -j 2 -DwarningAsError=true --root="$greenframe_root" \
    "$source" -o "$output")
}

sixth="$repo_root/research/native-sixth-explicit-sigma"
moment="$repo_root/research/native-moment-orthogonalization-audit"
moving="$repo_root/research/native-moving-schur-sigma"
cert="$moving/height50-certified"
zeta_lean="$cert/lean"
first_zero="$cert/hunts/hardy_first_zero/lean"

# Rebuild the local source closure of the current-main sigma interfaces from
# tracked sources. External imports resolve only through pinned Geometry,
# Mathlib, GreenFrame, and Carry package builds.
compile "$moment" MomentFunctional MomentFunctional.lean
compile "$moment" JacobiLogic JacobiLogic.lean
compile "$moment" PolynomialCoordinates PolynomialCoordinates.lean
# Carry's boundary gate imports this pinned GreenFrame chain, which is not part
# of the root library target. Compile missing modules into GreenFrame's package
# build directory from its pinned sources.
compile_greenframe GreenFrame.Concrete.Analysis.NormalizedSplit GreenFrame/Concrete/Analysis/NormalizedSplit.lean
compile_greenframe GreenFrame.Concrete.Analysis.ExternalRange GreenFrame/Concrete/Analysis/ExternalRange.lean
compile_greenframe GreenFrame.Concrete.Analysis.StaticPoisson GreenFrame/Concrete/Analysis/StaticPoisson.lean
compile_greenframe GreenFrame.Concrete.Analysis.RestrictedGraph GreenFrame/Concrete/Analysis/RestrictedGraph.lean
compile_greenframe GreenFrame.Concrete.Analysis.AmbientPoisson GreenFrame/Concrete/Analysis/AmbientPoisson.lean
compile "$moment" NativeApplication NativeApplication.lean
compile "$moment" SchurLogic SchurLogic.lean
compile "$sixth" SigmaParity SigmaParity.lean
compile "$sixth" SigmaCenterZero SigmaCenterZero.lean
compile "$sixth" SigmaCenterAll SigmaCenterAll.lean
compile "$sixth" SigmaGreenCurvature SigmaGreenCurvature.lean
compile "$sixth" SigmaOffcenter SigmaOffcenter.lean
compile "$sixth" SigmaOffcenterBridge SigmaOffcenterBridge.lean
compile "$sixth" SigmaCurvature SigmaCurvature.lean
compile "$sixth" SigmaQuadratic SigmaQuadratic.lean
compile "$moving" MatrixJetCalculus MatrixJetCalculus.lean
compile "$moving" SigmaNeighborhood SigmaNeighborhood.lean

# The moment realization and conditional obstruction are ported as Lean source
# and compiled afresh in this output directory.
compile "$moving" MomentComplexification MomentComplexification.lean
compile "$moving" MomentLogConvexity MomentLogConvexity.lean
compile "$moving" SigmaZeroObstruction SigmaZeroObstruction.lean
compile "$moving" SigmaNativeContinuation SigmaNativeContinuation.lean
compile "$moving" SigmaNativeZeroBridge SigmaNativeZeroBridge.lean

# Compile only the first-zero certificate's import closure, not the height-50
# count or the nine additional ordinate boxes.
compile "$zeta_lean" ZetaLean.Rigor ZetaLean/Rigor.lean
compile "$zeta_lean" ZetaLean.IntervalExp ZetaLean/IntervalExp.lean
compile "$zeta_lean" ZetaLean.IntervalCExp ZetaLean/IntervalCExp.lean
compile "$zeta_lean" ZetaLean.HardyZ ZetaLean/HardyZ.lean
compile "$first_zero" HardyFirstZero.Spine HardyFirstZero/Spine.lean -DautoImplicit=false -DrelaxedAutoImplicit=false
compile "$first_zero" HardyFirstZero.Phase HardyFirstZero/Phase.lean -DautoImplicit=false -DrelaxedAutoImplicit=false
compile "$first_zero" HardyFirstZero.EulerMaclaurin HardyFirstZero/EulerMaclaurin.lean -DautoImplicit=false -DrelaxedAutoImplicit=false
compile "$first_zero" HardyFirstZero.BoxSupport HardyFirstZero/BoxSupport.lean -DautoImplicit=false -DrelaxedAutoImplicit=false
compile "$first_zero" HardyFirstZero.Boxes HardyFirstZero/Boxes.lean -DautoImplicit=false -DrelaxedAutoImplicit=false
compile "$first_zero" HardyFirstZero.FirstZero HardyFirstZero/FirstZero.lean -DautoImplicit=false -DrelaxedAutoImplicit=false
compile "$moving" SigmaCertifiedNegativeDirection SigmaCertifiedNegativeDirection.lean
compile "$moving" SigmaPersistentNegativeDirection SigmaPersistentNegativeDirection.lean

echo "== C1 source scan"
if rg -n '\b(sorry|admit|native_decide|sorryAx)\b|^\s*axiom\s' \
  "$moving/SigmaZeroObstruction.lean" "$moving/MomentComplexification.lean" \
  "$moving/MomentLogConvexity.lean" "$moving/SigmaNativeContinuation.lean" \
  "$moving/SigmaNativeZeroBridge.lean" "$moving/SigmaCertifiedNegativeDirection.lean" \
  "$moving/SigmaPersistentNegativeDirection.lean" \
  "$cert/lean/ZetaLean" "$cert/hunts/hardy_first_zero/lean/HardyFirstZero"; then
  exit 1
else
  status=$?
  (( status == 1 )) || exit "$status"
fi

python3 "$task_dir/check_c1_axioms.py" "$output_dir/build.log"
echo "C1/C1B sources, certificate, and axiom reports passed."
