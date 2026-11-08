#!/usr/bin/env bash
set -euo pipefail

C5_EVIDENCE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
C5_STATUS_FILE="$C5_EVIDENCE/runner-status.txt"
C5_STATE_FILE="$C5_EVIDENCE/run-state.txt"
C5_SESSION_NAME=c5-bernoulli-prefix224-20261108

if [[ -f "$C5_STATUS_FILE" ]] && grep -q '^RUNNING$' "$C5_STATUS_FILE"; then
  echo "A C5 prefix-224 reproduction is already marked RUNNING." >&2
  exit 3
fi
if tmux has-session -t "$C5_SESSION_NAME" 2>/dev/null; then
  echo "A tmux session for the C5 prefix-224 reproduction already exists." >&2
  exit 3
fi

printf 'RUNNING\n' > "$C5_STATUS_FILE"
printf 'STARTED_UTC=%s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" > "$C5_STATE_FILE"
if ! tmux new-session -d -s "$C5_SESSION_NAME" "bash $C5_EVIDENCE/run-under-tmux.sh"; then
  printf 'LAUNCH_FAILED\n' > "$C5_STATUS_FILE"
  exit 1
fi
C5_PID=$(tmux display-message -p -t "$C5_SESSION_NAME" '#{pane_pid}')
printf 'PID=%s\n' "$C5_PID" >> "$C5_STATE_FILE"
printf 'TMUX_SESSION=%s\nPID=%s\n' "$C5_SESSION_NAME" "$C5_PID"
