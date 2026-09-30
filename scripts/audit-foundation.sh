#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

if ! command -v rg >/dev/null; then
  echo "ERROR: ripgrep (rg) is required for the source audit." >&2
  exit 1
fi

# Inspect source text as well as kernel dependencies. A scan error must fail.
if rg -n '\b(sorry|admit|unsafe|native_decide|sorryAx|implemented_by)\b|^[[:space:]]*axiom\b' GeometryOfNumbers --glob '*.lean'; then
  echo "ERROR: prohibited trust escape found in Lean source." >&2
  exit 1
else
  scan_status=$?
  if (( scan_status != 1 )); then
    exit "$scan_status"
  fi
fi

# Every public foundational theorem must participate in the kernel audit.
# Match declarations rather than private implementation lemmas or examples.
while IFS= read -r proof_name; do
  if ! rg -q "^#assert_no_axioms ${proof_name}$" GeometryOfNumbers/Foundation/Audit.lean; then
    echo "ERROR: public theorem missing from axiom audit: ${proof_name}" >&2
    exit 1
  fi
done < <(rg --no-filename --only-matching --replace '$1' \
  '^theorem ([A-Za-z0-9_]+)' GeometryOfNumbers/Foundation --glob '*.lean')

lake build
lake env lean GeometryOfNumbers/Foundation/Audit.lean
git diff --check

echo "PASS: foundation build and empty-axiom audit."
