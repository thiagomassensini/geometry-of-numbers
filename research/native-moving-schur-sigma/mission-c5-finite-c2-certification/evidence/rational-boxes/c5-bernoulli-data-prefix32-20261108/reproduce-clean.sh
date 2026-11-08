#!/usr/bin/env bash
set -euo pipefail

C5_EVIDENCE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
C5_SOURCE_ROOT=$(cd -- "$C5_EVIDENCE/../../../.." && pwd)
C5_REFERENCE_ROOT=${SIGMA_REFERENCE_ROOT:-/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106}
C5_CARRY_ROOT=${CARRY_LEAN_ROOT:-/home/thlinux/worktrees/carry-sigma-c2-pinned-045369}
C5_CACHE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache
C5_EXTRA_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean
C5_OUTPUT="$C5_SOURCE_ROOT/.cache/c5-bernoulli-data-prefix32-clean-20261108-$$"
C5_LEAN_BIN=${LEAN_BIN:-/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}
mkdir -p "$C5_OUTPUT"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT"
export CARRY_LEAN_ROOT="$C5_CARRY_ROOT"
export SIGMA_OUTPUT_DIR="$C5_OUTPUT"
export SIGMA_HEIGHT50_BUILD="$C5_CACHE_ROOT/c5-centered-node-clean-20261107:$C5_CACHE_ROOT/c5-node-instantiation-clean-20261107:$C5_EXTRA_BUILD"
export LEAN_BIN="$C5_LEAN_BIN"

for C5_MODULE in SigmaC5BernoulliDataProbe SigmaC5BernoulliDataTable SigmaC5BernoulliDataCertificate SigmaC5BernoulliDataCertificateAudit; do
  if bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" "$C5_MODULE" \
      > "$C5_EVIDENCE/$C5_MODULE-clean-build.log" 2>&1; then
    printf 'BUILD_EXIT=0\n' >> "$C5_EVIDENCE/$C5_MODULE-clean-build.log"
  else
    C5_STATUS=$?
    printf 'BUILD_EXIT=%s\n' "$C5_STATUS" >> "$C5_EVIDENCE/$C5_MODULE-clean-build.log"
    exit "$C5_STATUS"
  fi
done

python3 "$C5_EVIDENCE/check-data-table.py" \
  "$C5_EVIDENCE/SigmaC5BernoulliDataProbe-clean-build.log" \
  "$C5_SOURCE_ROOT/SigmaC5BernoulliDataTable.lean" \
  > "$C5_EVIDENCE/data-table-check.log"
python3 "$C5_EVIDENCE/check-axioms.py" \
  "$C5_EVIDENCE/SigmaC5BernoulliDataCertificateAudit-clean-build.log" \
  > "$C5_EVIDENCE/axiom-audit.log"
printf 'CLEAN_BUILD=PASS\nAXIOM_AUDIT=PASS\n' > "$C5_EVIDENCE/RESULT.txt"
sha256sum \
  "$C5_SOURCE_ROOT/SigmaC5BernoulliDataProbe.lean" \
  "$C5_SOURCE_ROOT/SigmaC5BernoulliDataTable.lean" \
  "$C5_SOURCE_ROOT/SigmaC5BernoulliDataCertificate.lean" \
  "$C5_SOURCE_ROOT/SigmaC5BernoulliDataCertificateAudit.lean" \
  "$C5_EVIDENCE/README.md" \
  "$C5_EVIDENCE/reproduce-clean.sh" \
  "$C5_EVIDENCE/check-axioms.py" \
  "$C5_EVIDENCE/check-data-table.py" \
  "$C5_EVIDENCE/bernoulli-table-probe.log" \
  "$C5_EVIDENCE/attempts/full-table-monolithic-proof.log" \
  "$C5_EVIDENCE/attempts/prefix32-full-table-expansion.md" \
  "$C5_EVIDENCE/SigmaC5BernoulliDataTable-clean-build.log" \
  "$C5_EVIDENCE/SigmaC5BernoulliDataProbe-clean-build.log" \
  "$C5_EVIDENCE/SigmaC5BernoulliDataCertificate-clean-build.log" \
  "$C5_EVIDENCE/SigmaC5BernoulliDataCertificateAudit-clean-build.log" \
  "$C5_EVIDENCE/axiom-audit.log" \
  "$C5_EVIDENCE/data-table-check.log" \
  "$C5_EVIDENCE/RESULT.txt" \
  > "$C5_EVIDENCE/SHA256SUMS.txt"
