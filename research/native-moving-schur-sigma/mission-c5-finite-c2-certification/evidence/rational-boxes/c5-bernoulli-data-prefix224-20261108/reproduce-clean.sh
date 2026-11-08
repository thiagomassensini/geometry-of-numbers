#!/usr/bin/env bash
set -euo pipefail

C5_EVIDENCE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
C5_SOURCE_ROOT=$(cd -- "$C5_EVIDENCE/../../../.." && pwd)
C5_REFERENCE_ROOT=${SIGMA_REFERENCE_ROOT:-/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106}
C5_CARRY_ROOT=${CARRY_LEAN_ROOT:-/home/thlinux/worktrees/carry-sigma-c2-pinned-045369}
C5_CACHE_ROOT=${C5_REFERENCE_ROOT}/research/native-moving-schur-sigma/.cache
C5_EXTRA_BUILD=${C5_EXTRA_BUILD:-/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean}
C5_PREFIX64_CACHE=${C5_PREFIX64_CACHE:-/home/thlinux/worktrees/geometry-of-numbers-c5-zeta-bernoulli-prefix64-20261108/research/native-moving-schur-sigma/.cache/c5-bernoulli-data-prefix64-clean-20261108-1084239}
C5_PREFIX96_CACHE=${C5_PREFIX96_CACHE:-/home/thlinux/worktrees/geometry-of-numbers-c5-zeta-bernoulli-prefix96-20261108/research/native-moving-schur-sigma/.cache/c5-bernoulli-data-prefix96-clean-20261108-1105893}
C5_PREFIX128_CACHE=${C5_PREFIX128_CACHE:-/home/thlinux/worktrees/geometry-of-numbers-c5-zeta-bernoulli-prefix128-20261108/research/native-moving-schur-sigma/.cache/c5-bernoulli-data-prefix128-clean-20261108-1144056}
C5_PREFIX160_CACHE=${C5_PREFIX160_CACHE:-/home/thlinux/worktrees/geometry-of-numbers-c5-zeta-bernoulli-prefix128-20261108/research/native-moving-schur-sigma/.cache/c5-bernoulli-data-prefix160-clean-20261108-16476}
C5_PREFIX192_CACHE=${C5_PREFIX192_CACHE:-/home/thlinux/worktrees/geometry-of-numbers-c5-zeta-bernoulli-prefix192-20261108/research/native-moving-schur-sigma/.cache/c5-bernoulli-data-prefix192-clean-20261108-57495}
C5_PREFIX192_OLEAN="$C5_PREFIX192_CACHE/SigmaC5BernoulliDataCertificate192.olean"
C5_EXPECTED_PREFIX192_SHA=$(sed -n 's/^PREFIX192_OLEAN_SHA256=//p' "$C5_EVIDENCE/pins.txt")
C5_ACTUAL_PREFIX192_SHA=$(sha256sum "$C5_PREFIX192_OLEAN" | cut -d' ' -f1)
if [[ -z "$C5_EXPECTED_PREFIX192_SHA" || "$C5_ACTUAL_PREFIX192_SHA" != "$C5_EXPECTED_PREFIX192_SHA" ]]; then
  echo "prefix-192 .olean SHA-256 mismatch" >&2
  exit 2
fi
C5_OUTPUT="$C5_SOURCE_ROOT/.cache/c5-bernoulli-data-prefix224-clean-$$"
C5_LEAN_BIN=${LEAN_BIN:-/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}
mkdir -p "$C5_OUTPUT"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT"
export CARRY_LEAN_ROOT="$C5_CARRY_ROOT"
export SIGMA_OUTPUT_DIR="$C5_OUTPUT"
export SIGMA_HEIGHT50_BUILD="$C5_PREFIX192_CACHE:$C5_PREFIX160_CACHE:$C5_PREFIX128_CACHE:$C5_PREFIX96_CACHE:$C5_PREFIX64_CACHE:$C5_CACHE_ROOT/c5-centered-node-clean-20261107:$C5_CACHE_ROOT/c5-node-instantiation-clean-20261107:$C5_EXTRA_BUILD"
export LEAN_BIN="$C5_LEAN_BIN"

for C5_MODULE in \
    SigmaC5BernoulliDataCertificate224 \
    SigmaC5BernoulliDataCertificate224Audit; do
  if /usr/bin/time -v bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" "$C5_MODULE" \
      > "$C5_EVIDENCE/$C5_MODULE-clean-build.log" 2>&1; then
    printf 'BUILD_EXIT=0\n' >> "$C5_EVIDENCE/$C5_MODULE-clean-build.log"
  else
    C5_STATUS=$?
    printf 'BUILD_EXIT=%s\n' "$C5_STATUS" >> "$C5_EVIDENCE/$C5_MODULE-clean-build.log"
    exit "$C5_STATUS"
  fi
done

python3 "$C5_EVIDENCE/check-axioms.py" \
  "$C5_EVIDENCE/SigmaC5BernoulliDataCertificate224Audit-clean-build.log" \
  > "$C5_EVIDENCE/axiom-audit.log"
printf 'CLEAN_BUILD=PASS\nAXIOM_AUDIT=PASS\n' > "$C5_EVIDENCE/RESULT.txt"

(
  cd "$C5_EVIDENCE"
  sha256sum \
    ../../../../SigmaC5BernoulliDataCertificate224.lean \
    ../../../../SigmaC5BernoulliDataCertificate224Audit.lean \
    ../../../../SigmaC5BernoulliDataTable.lean \
    README.md pins.txt reproduce-clean.sh run-detached.sh run-under-tmux.sh \
    check-axioms.py runner-status.txt run-state.txt reproduce-runner.log \
    SigmaC5BernoulliDataCertificate224-clean-build.log \
    SigmaC5BernoulliDataCertificate224Audit-clean-build.log axiom-audit.log RESULT.txt \
    > SHA256SUMS.txt
)
