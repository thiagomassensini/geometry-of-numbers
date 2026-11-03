#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../.."
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$here/evidence"
for module in MomentosHankel.SchurPivotCurvature MomentosHankel.PivotSecondDerivative MomentosHankel.SchurVectorSmoothness MomentosHankel.PivotLocalTransport MatrixJetCalculus SigmaNeighborhood MovingSchur SectorRegression MomentLogConvexity SigmaZeroObstruction Audit; do
  printf 'BUILD %s\n' "$module"
  bash "$here/compile_module.sh" "$module" > "$here/evidence/$module.log" 2>&1 || { cat "$here/evidence/$module.log"; exit 1; }
  printf 'PASS %s\n' "$module"
done
lake build --wfail > "$here/evidence/root-build.log" 2>&1
printf 'PASS lake build --wfail\n'
for layer in foundation geometry analysis; do
  bash "scripts/audit-$layer.sh" > "$here/evidence/audit-$layer.log" 2>&1
  printf 'PASS audit %s\n' "$layer"
done
if rg -n '\b(sorry|admit|unsafe|native_decide|sorryAx|implemented_by)\b|^\s*axiom\s' "$here" --glob '*.lean'; then
  exit 1
else
  status=$?
  if ((status != 1)); then exit "$status"; fi
fi
printf 'PASS source scan\n'
