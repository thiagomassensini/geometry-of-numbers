#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
for module in CriticalTiltSlice MixedTilt MixedPhase MixedPhaseJets MixedFinite MixedTail MixedPrime CriticalTiltBridge NativeTiltJets PrimeRecurrence TiltSourceGate PrimeCarryGate TransverseLedger TiltAudit; do
  printf '\n--- %s ---\n' "$module"
  bash "$here/compile.sh" "$module"
done
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*axiom([[:space:]]|$)' "$here"/*.lean; then exit 1; fi
