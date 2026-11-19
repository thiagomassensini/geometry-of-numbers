#!/usr/bin/env bash
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
csa_root="${CSA_ROOT:-/home/thlinux/carry-self-adjoint-operator}"
cpformal_root="$csa_root/.lake/packages/CPFormal"
cpformal_commit="$(git -C "$cpformal_root" rev-parse --short=7 HEAD)"
if [[ "$cpformal_commit" != "65d50f6" ]]; then
  echo "ERROR: CPFormal pin differs from validated 65d50f6: $cpformal_commit" >&2
  exit 2
fi
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_PATH="$(cd "$csa_root" && lake env printenv LEAN_PATH)"
cd "$repo"
for name in ReflectedGreenPolarizationGate CompactBracketKernelEnergyTest GreenAngularCorrectionAtZeros TfvdMixedGreenExactTransport; do
  f="research/projective-chiral-complex-cauchy/$name.lean"
  outfile="/tmp/green-polarization-${name}-$$.log"
  echo "[lean] $f"
  lean -DwarningAsError=true "$f" > "$outfile" 2>&1
  if grep -Eq 'sorryAx|error:' "$outfile"; then
    cat "$outfile" >&2
    echo "ERROR: theorem axiom audit or compilation failed in $name" >&2
    exit 3
  fi
  grep "depends on axioms" "$outfile" || true
  rm -f "$outfile"
done
echo "PASS: all 4 Lean files, no sorryAx, pin=$cpformal_commit"
