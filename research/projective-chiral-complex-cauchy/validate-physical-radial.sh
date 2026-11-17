#!/usr/bin/env bash
# Reproduce the cross-repository C2 radial physical sign transport.
# Usage: validate-physical-radial.sh /path/to/carry-self-adjoint-operator
# Does not modify either repository's Lake manifests or imports.
set -euo pipefail
gon_root="$(cd "$(dirname "$0")/../.." && pwd)"
if [ "$#" -lt 1 ]; then
  echo "Usage: $0 /path/to/carry-self-adjoint-operator" >&2
  exit 2
fi
csa_root="$(cd "$1" && pwd)"
python3 - "$gon_root" "$csa_root" <<'PY'
import json, pathlib, sys
gon,csa=map(pathlib.Path,sys.argv[1:])
assert (gon/"lean-toolchain").read_bytes() == (csa/"lean-toolchain").read_bytes()
def pins(root):
    d=json.loads((root/"lake-manifest.json").read_text())
    return {pkg["name"]:pkg["rev"] for pkg in d["packages"]
            if pkg["name"] in ("mathlib","GreenFrame")}
assert pins(gon) == pins(csa), (pins(gon),pins(csa))
print("Lean and shared mathlib/GreenFrame pins match.")
PY
(cd "$gon_root" && lake build GeometryOfNumbers.Analysis.CarryMaterialComplexPickSignGate >/dev/null)
csa_path="$(cd "$csa_root" && lake env printenv LEAN_PATH)"
lean_exe="$(cd "$csa_root" && lake env sh -c 'command -v lean')"
log="${TMPDIR:-/tmp}/gon-c2-physical-radial-validation.log"
(
  cd "$csa_root"
  LEAN_PATH="$gon_root/.lake/build/lib/lean:$csa_path" "$lean_exe" \
    -DwarningAsError=true \
    "$gon_root/research/material-central-calibration/CanonicalComparison.lean"
) >"$log" 2>&1
if grep -Eq 'error:|sorryAx' "$log"; then
  tail -50 "$log" >&2
  exit 1
fi
grep -A2 -E 'physicalC2Radial.*depends on axioms' "$log"
echo "PASS: source-first two-point PSD, all-finite radial sewing, third determinant > 0."
