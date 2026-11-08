#!/usr/bin/env bash
set -u

C5_EVIDENCE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
C5_STATUS_FILE="$C5_EVIDENCE/runner-status.txt"
C5_STATE_FILE="$C5_EVIDENCE/run-state.txt"
C5_RUNNER_LOG="$C5_EVIDENCE/reproduce-runner.log"

bash "$C5_EVIDENCE/reproduce-clean.sh" > "$C5_RUNNER_LOG" 2>&1
C5_EXIT=$?
printf 'EXIT=%s\n' "$C5_EXIT" > "$C5_STATUS_FILE.tmp"
mv "$C5_STATUS_FILE.tmp" "$C5_STATUS_FILE"
if [[ "$C5_EXIT" -ne 0 ]]; then
  if grep -q '^BUILD_EXIT=[1-9]' "$C5_EVIDENCE/SigmaC5BernoulliDataCertificate224-clean-build.log"; then
    printf 'CLEAN_BUILD=FAIL\nAXIOM_AUDIT=NOT_RUN\nEXIT=%s\n' "$C5_EXIT" > "$C5_EVIDENCE/RESULT.txt"
  elif grep -q '^BUILD_EXIT=[1-9]' "$C5_EVIDENCE/SigmaC5BernoulliDataCertificate224Audit-clean-build.log"; then
    printf 'CLEAN_BUILD=PASS\nAXIOM_AUDIT=FAIL\nEXIT=%s\n' "$C5_EXIT" > "$C5_EVIDENCE/RESULT.txt"
  else
    printf 'CLEAN_BUILD=PASS\nAXIOM_AUDIT=FAIL\nEXIT=%s\n' "$C5_EXIT" > "$C5_EVIDENCE/RESULT.txt"
  fi
fi
(
  cd "$C5_EVIDENCE"
  {
    sha256sum \
      ../../../../SigmaC5BernoulliDataCertificate224.lean \
      ../../../../SigmaC5BernoulliDataCertificate224Audit.lean \
      ../../../../SigmaC5BernoulliDataTable.lean
    find . -type f ! -name SHA256SUMS.txt -print0 | sort -z | xargs -0 sha256sum
  } > SHA256SUMS.txt.tmp
  mv SHA256SUMS.txt.tmp SHA256SUMS.txt
)
exit "$C5_EXIT"
