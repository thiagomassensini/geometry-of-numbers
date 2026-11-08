#!/usr/bin/env bash
set -euo pipefail

C5_EVIDENCE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
export C5_EVIDENCE
C5_STATUS_FILE="$C5_EVIDENCE/runner-status.txt"
C5_STATE_FILE="$C5_EVIDENCE/run-state.txt"
C5_RUNNER_LOG="$C5_EVIDENCE/reproduce-runner.log"

if [[ -f "$C5_STATUS_FILE" ]] && grep -q '^RUNNING$' "$C5_STATUS_FILE"; then
  echo "A C5 prefix-160 reproduction is already marked RUNNING." >&2
  exit 3
fi

printf 'RUNNING\n' > "$C5_STATUS_FILE"
printf 'STARTED_UTC=%s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" > "$C5_STATE_FILE"

nohup bash -c '
set +e
bash "$1"
C5_EXIT=$?
printf "EXIT=%s\n" "$C5_EXIT" > "$2.tmp"
mv "$2.tmp" "$2"
sha256sum "$2" "$C5_EVIDENCE/run-state.txt" "$C5_EVIDENCE/reproduce-runner.log" \
  >> "$C5_EVIDENCE/SHA256SUMS.txt"
exit "$C5_EXIT"
' _ "$C5_EVIDENCE/reproduce-clean.sh" "$C5_STATUS_FILE" > "$C5_RUNNER_LOG" 2>&1 < /dev/null &

C5_PID=$!
printf 'PID=%s\n' "$C5_PID" >> "$C5_STATE_FILE"
printf 'PID=%s\n' "$C5_PID"
