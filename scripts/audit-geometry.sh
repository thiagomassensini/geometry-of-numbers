#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

if ! command -v rg >/dev/null; then
  echo "ERROR: ripgrep (rg) is required for the source audit." >&2
  exit 1
fi

if rg -n '\b(sorry|admit|unsafe|native_decide|sorryAx|implemented_by|classical)\b|Classical\.choice|^[[:space:]]*axiom\b' GeometryOfNumbers/Geometry --glob '*.lean'; then
  echo "ERROR: prohibited trust escape or choice found in Geometry source." >&2
  exit 1
else
  scan_status=$?
  if (( scan_status != 1 )); then
    exit "$scan_status"
  fi
fi

while IFS= read -r proof_name; do
  for audit_command in assert_geometry_axioms 'print axioms'; do
    if ! rg -q "^#${audit_command} ${proof_name}$" GeometryOfNumbers/Geometry/Audit.lean; then
      echo "ERROR: geometrical theorem missing from audit: ${proof_name}" >&2
      exit 1
    fi
  done
done < <(rg --no-filename --only-matching --replace '$1' \
  '^theorem ([A-Za-z0-9_]+)' GeometryOfNumbers/Geometry --glob '*.lean')

lake env lean --run scripts/check-foundation-imports.lean
lake env lean --run scripts/check-geometry-imports.lean
lake build GeometryOfNumbers.Geometry GeometryOfNumbers.Geometry.Audit
lake env lean GeometryOfNumbers/Geometry/Audit.lean
git diff --check
echo "PASS: discrete geometry audit; only propext/Quot.sound permitted (NOT axiom-free)."
