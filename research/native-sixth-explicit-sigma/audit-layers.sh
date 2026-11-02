#!/usr/bin/env bash
set -euo pipefail
TASK=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$TASK/../.." && pwd)
export PATH="$HOME/.elan/bin:$PATH"
cd "$REPO"
if rg -n '\b(sorry|admit|native_decide)\b|^\s*axiom\s' "$TASK"/*.lean; then
  echo 'FAIL forbidden shortcut or axiom' >&2
  exit 1
fi
printf 'PASS research source scan\n'
for layer in foundation geometry analysis; do
  printf 'Audit %s\n' "$layer"
  bash "scripts/audit-$layer.sh" >"$TASK/evidence/audit-$layer.log" 2>&1 || { tail -50 "$TASK/evidence/audit-$layer.log"; exit 1; }
  tail -1 "$TASK/evidence/audit-$layer.log"
done
