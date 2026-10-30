#!/usr/bin/env bash
set -euo pipefail
TASK=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$TASK/../.." && pwd)
mkdir -p "$TASK/evidence"
for module in CriticalCoefficient RadialPairs RadialCutoff SigmaParity SigmaCenterZero SigmaCenterAll SigmaGreenCurvature SigmaOffcenter SigmaOffcenterBridge SigmaCurvature SigmaQuadratic Audit; do
  printf 'Compile %s\n' "$module"
  bash "$TASK/compile_module.sh" "$module" >"$TASK/evidence/${module}.log" 2>&1 || { cat "$TASK/evidence/${module}.log"; exit 1; }
  printf 'PASS %s\n' "$module"
done
printf 'Root lake build --wfail\n'
(cd "$REPO" && "$HOME/.elan/bin/lake" build --wfail) >"$TASK/evidence/root-build.log" 2>&1 || { tail -100 "$TASK/evidence/root-build.log"; exit 1; }
tail -5 "$TASK/evidence/root-build.log"
printf 'PASS root build --wfail\n'
