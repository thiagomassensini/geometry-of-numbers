#!/usr/bin/env bash
set -euo pipefail
research_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$research_dir/../.." && pwd)"
operator_root="${1:-$repo_root/../carry-self-adjoint-operator}"
evidence_dir="${2:-$research_dir/evidence}"
mkdir -p -- "$evidence_dir"
export PATH=/home/thlinux/.elan/bin:"$PATH"
export PYTHONDONTWRITEBYTECODE=1
python3 "$research_dir/verify_provenance.py" "$repo_root" "$operator_root"
for module_name in SourceTail UniformCutoff CriticalScale BoundaryControl BudgetScale Regression Audit; do
  if bash "$research_dir/compile_module.sh" "$module_name" "$operator_root" > "$evidence_dir/$module_name.log" 2>&1; then
    printf 'PASS: %s\n' "$module_name"
  else
    cat "$evidence_dir/$module_name.log" >&2
    exit 1
  fi
done
python3 "$research_dir/check_public_roots.py"
(cd -- "$repo_root" && lake build --wfail) > "$evidence_dir/root-build.log" 2>&1
printf 'PASS: root build --wfail\n'
for zone in foundation geometry analysis; do
  (cd -- "$repo_root" && bash "scripts/audit-$zone.sh") > "$evidence_dir/$zone-audit.log" 2>&1
  printf 'PASS: %s audit\n' "$zone"
done
python3 "$research_dir/package_evidence.py" "$research_dir" "$repo_root" "$operator_root" "$evidence_dir"
