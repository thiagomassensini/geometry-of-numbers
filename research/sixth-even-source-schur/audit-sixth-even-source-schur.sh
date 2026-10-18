#!/usr/bin/env bash
set -euo pipefail
research_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$research_dir/../.." && pwd)"
evidence_dir="${1:-$research_dir/evidence}"
mkdir -p -- "$evidence_dir"
export PATH=/home/thlinux/.elan/bin:"$PATH"
export PYTHONDONTWRITEBYTECODE=1
python3 "$research_dir/verify_provenance.py"
python3 "$research_dir/check_public_roots.py"
modules=(ThetaTwentyTwo)
for j in {0..11}; do modules+=("ThetaCheck$j"); done
modules+=(ThetaInputs SourceEnclosures SixthEvenCertificate VariationalSchur Regression Audit)
# Sequential kernel reduction bounds peak memory. Cached historical modules
# are reused only after their source manifests and pinned commits are checked.
for module_name in "${modules[@]}"; do
  if /usr/bin/time -f 'elapsed=%e maxrss_kb=%M' bash "$research_dir/compile_module.sh" "$module_name" > "$evidence_dir/$module_name.log" 2>&1; then
    printf 'PASS: %s\n' "$module_name"
  else
    cat "$evidence_dir/$module_name.log" >&2
    exit 1
  fi
done
(cd -- "$repo_root" && lake build --wfail) > "$evidence_dir/root-build.log" 2>&1
printf 'PASS: root build --wfail\n'
for zone in foundation geometry analysis; do
  (cd -- "$repo_root" && bash "scripts/audit-$zone.sh") > "$evidence_dir/$zone-audit.log" 2>&1
  printf 'PASS: %s audit\n' "$zone"
done
python3 "$research_dir/package_evidence.py"
