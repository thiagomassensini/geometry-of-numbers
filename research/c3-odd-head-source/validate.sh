#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$here/evidence"
for module in GammaExtendedRationals GammaNinePolynomial GammaNineReference GammaNineValue HeadNine OddHeadMargin CompletedHeadEight FinalAudit; do
  printf 'BUILD %s\n' "$module"
  if ! bash "$here/compile.sh" "$module" > "$here/evidence/$module.log" 2>&1; then
    cat "$here/evidence/$module.log"
    exit 1
  fi
  printf 'PASS %s\n' "$module"
done
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*axiom([[:space:]]|$)' "$here"/*.lean; then
  exit 1
else
  rc=$?
  if ((rc != 1)); then exit "$rc"; fi
fi
printf 'PASS no forbidden shortcuts or new axioms\n'
