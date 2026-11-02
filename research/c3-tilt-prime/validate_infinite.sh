#!/usr/bin/env bash
# Validação do canal adicionado (derivação sob o limite). Não altera os módulos
# anteriores: apenas compila as raízes novas sobre os .cache existentes.
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
for module in MixedInfinite MixedTransverse MixedInfiniteAudit OfflineObstruction CriticalConcavity CriticalCurvature LogOperatorBridge NativeLogOperatorBridge LpNormBridge AccumulationMechanism SourceDecomposition TiltCurvatureBridge TiltLogDerivative CompletedFirstVariation OfflineObstructionAudit; do
  printf '\n--- %s ---\n' "$module"
  bash "$here/compile.sh" "$module"
done
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*axiom([[:space:]]|$)' \
    "$here/MixedInfinite.lean" "$here/MixedTransverse.lean" "$here/MixedInfiniteAudit.lean" \
    "$here/OfflineObstruction.lean" "$here/CriticalConcavity.lean" "$here/CriticalCurvature.lean" "$here/LogOperatorBridge.lean" "$here/NativeLogOperatorBridge.lean" "$here/LpNormBridge.lean" "$here/AccumulationMechanism.lean" "$here/SourceDecomposition.lean" "$here/TiltCurvatureBridge.lean" "$here/TiltLogDerivative.lean" "$here/CompletedFirstVariation.lean" "$here/OfflineObstructionAudit.lean"; then
  echo "PROIBIDO: sorry/admit/axiom/native_decide encontrado" >&2
  exit 1
fi
echo "OK: MixedInfinite e MixedInfiniteAudit compilam; sem sorry/admit/axiom/native_decide."
