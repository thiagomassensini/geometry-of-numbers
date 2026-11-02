#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
for module in NativeBudgetRate NativeFiniteHeadMargin NativeExplicitHeadMargin NativeHeadMarginAudit; do
  printf '\n--- %s ---\n' "$module"
  bash "$here/compile.sh" "$module"
done
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|native_decide)([^[:alnum:]_]|$)|^[[:space:]]*axiom([[:space:]]|$)' "$here/NativeBudgetRate.lean" "$here/NativeFiniteHeadMargin.lean" "$here/NativeExplicitHeadMargin.lean" "$here/NativeHeadMarginAudit.lean"; then
  exit 1
fi
printf 'PASS: margem finita, taxa explícita e auditoria.\n'
