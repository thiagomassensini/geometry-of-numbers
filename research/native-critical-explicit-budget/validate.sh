#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
cd "$here/../.."
mkdir -p "$here/evidence"
for module in GeneralBudget CriticalCoefficient NumericCutoff RelativeGate RelativeCertificate Audit; do
  printf 'BUILD %s\n' "$module"
  bash "$here/compile_module.sh" "$module" > "$here/evidence/validate-$module.log" 2>&1
  printf 'PASS %s\n' "$module"
done
PATH="$HOME/.elan/bin:$PATH" lake build --wfail > "$here/evidence/root-build.log" 2>&1
printf 'PASS lake build --wfail\n'
if rg -n '\b(sorry|admit|native_decide)\b|^\s*axiom\s' "$here"/*.lean; then
  printf 'FAILED: forbidden declaration or shortcut\n' >&2
  exit 1
fi
printf 'PASS no forbidden shortcuts or axioms\n'
