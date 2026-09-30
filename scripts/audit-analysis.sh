#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

if ! command -v rg >/dev/null; then
  echo "ERROR: ripgrep (rg) is required for the source audit."
  exit 1
fi

# Every public analytical theorem reports its footprint and permits only the
# standard axioms. This does NOT replace the separate empty-footprint audit.
while IFS= read -r proof_name; do
  for audit_command in assert_analysis_axioms 'print axioms'; do
    if ! rg -q "^#${audit_command} ${proof_name}$" GeometryOfNumbers/Analysis/Audit.lean; then
      echo "ERROR: analytical theorem missing from audit: ${proof_name}" >&2
      exit 1
    fi
  done
done < <(rg --no-filename --only-matching --replace '$1' \
  '^theorem ([A-Za-z0-9_]+)' GeometryOfNumbers/Analysis --glob '*.lean')

lake build GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.Audit
lake env lean GeometryOfNumbers/Analysis/Audit.lean
echo "PASS: real analysis build and standard-axiom audit (NOT axiom-free)."
