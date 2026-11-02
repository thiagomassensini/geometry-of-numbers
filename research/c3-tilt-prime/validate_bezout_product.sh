#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
for module in BezoutSourceProduct BezoutSourceProductAudit; do
  printf '\n--- %s ---\n' "$module"
  bash "$here/compile.sh" "$module"
done
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*axiom([[:space:]]|$)' "$here/BezoutSourceProduct.lean" "$here/BezoutSourceProductAudit.lean"; then
  exit 1
fi
printf 'PASS: produto de Bézout, blocos e auditoria.\n'
