#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
for module in ThirdSourcePrefix ThirdSourcePrefixAudit; do
  printf '\n--- %s ---\n' "$module"
  bash "$here/compile.sh" "$module"
done
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*axiom([[:space:]]|$)' "$here/ThirdSourcePrefix.lean" "$here/ThirdSourcePrefixAudit.lean"; then
  exit 1
fi
printf 'PASS: prefixos da terceira direção e auditoria.\n'
