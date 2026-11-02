#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
for module in NativeProductFactor NativeProductTransport NativeProductTransportAudit; do
  printf '\n--- %s ---\n' "$module"
  bash "$here/compile.sh" "$module"
done
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*axiom([[:space:]]|$)' "$here/NativeProductFactor.lean" "$here/NativeProductTransport.lean" "$here/NativeProductTransportAudit.lean"; then
  exit 1
fi
printf 'PASS: produto literal, cruzamentos, cauda e auditoria.\n'
