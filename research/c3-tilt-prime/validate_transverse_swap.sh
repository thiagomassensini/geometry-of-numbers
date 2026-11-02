#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
for module in TiltPhase TiltQuant TiltBounds TransverseBound TransverseSwap SwapCapstone InfiniteTiltLedger DerivativeLedger TransverseSwapAudit; do
  printf '\n--- %s ---\n' "$module"
  bash "$here/compile.sh" "$module"
done
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*axiom([[:space:]]|$)' \
  "$here/TiltPhase.lean" "$here/TiltQuant.lean" "$here/TiltBounds.lean" \
  "$here/TransverseBound.lean" "$here/TransverseSwap.lean" "$here/SwapCapstone.lean" \
  "$here/InfiniteTiltLedger.lean" "$here/DerivativeLedger.lean" "$here/TransverseSwapAudit.lean"; then
  exit 1
fi
