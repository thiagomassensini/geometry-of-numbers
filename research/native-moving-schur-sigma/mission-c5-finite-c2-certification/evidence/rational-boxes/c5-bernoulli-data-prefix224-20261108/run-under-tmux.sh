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
(
  cd "$C5_EVIDENCE"
  sha256sum runner-status.txt run-state.txt reproduce-runner.log >> SHA256SUMS.txt
)
exit "$C5_EXIT"
