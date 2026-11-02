#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
for module in FullTransverseCancellation FullTfvdTransverse FullTransverseCancellationAudit; do
  printf '\n--- %s ---\n' "$module"
  bash "$here/compile.sh" "$module"
done
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*axiom([[:space:]]|$)' "$here/FullTransverseCancellation.lean" "$here/FullTfvdTransverse.lean" "$here/FullTransverseCancellationAudit.lean"; then
  exit 1
fi
printf 'PASS: pesquisa transversal, auditoria e busca de atalhos proibidos.\n'
