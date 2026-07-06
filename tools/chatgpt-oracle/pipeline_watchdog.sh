#!/usr/bin/env bash
# Pipeline supervisor watchdog (runs inside the WSL distro).
#
# Idempotent "ensure-alive" check: if pipeline_supervisor.py is already
# running it does nothing; if it has died (crash, distro restart, or a
# single-paper run that completed) it relaunches it detached with the
# configured arguments. The supervisor's own singleton guard makes a
# double-launch harmless, so this script is safe to run on any schedule.
#
# Intended to be fired every few minutes by a Windows Scheduled Task:
#   wsl.exe -d NyxIDUbuntu2404Cli -e bash -lc \
#     /mnt/d/omega/automath/tools/chatgpt-oracle/pipeline_watchdog.sh
#
# Running the distro via the scheduled task also boots it if it was
# shut down, so this covers both "supervisor died" and "WSL stopped".

set -u

# ── Config ────────────────────────────────────────────────────────────
REPO="/mnt/d/omega/automath"
# Arguments the supervisor is (re)started with. Keep in sync with the
# command you want kept alive. Omitting --paper makes the supervisor run
# the whole runnable queue (its inner pool gets --all automatically) with
# --parallel worker slots; add `--paper <dir>` to pin to one paper.
SUPERVISOR_ARGS=(
  --parallel 3
  --poll-interval 120
  --no-auto-commit
  --no-server-spawn
  --no-pi-review
)
# ──────────────────────────────────────────────────────────────────────

SCRIPT_DIR="${REPO}/tools/chatgpt-oracle"
PID_FILE="${SCRIPT_DIR}/.pipeline_supervisor.pid"
LOG="${SCRIPT_DIR}/supervisor_logs/watchdog.log"
LOCK="${SCRIPT_DIR}/.pipeline_watchdog.lock"

mkdir -p "${SCRIPT_DIR}/supervisor_logs"
ts() { date -u +%Y-%m-%dT%H:%M:%S%z; }
log() { echo "[$(ts)] $*" >>"$LOG"; }

# Single watchdog at a time.
exec 9>"$LOCK"
if ! flock -n 9; then
  exit 0
fi

# Is a supervisor already alive? Read pid from the supervisor's own record.
alive=0
if [ -f "$PID_FILE" ]; then
  pid="$(python3 - "$PID_FILE" <<'PY' 2>/dev/null
import json, sys
try:
    raw = open(sys.argv[1], encoding="utf-8").read().strip()
    data = json.loads(raw) if raw.startswith("{") else {"pid": int(raw)}
    print(int(data.get("pid") or 0))
except Exception:
    print(0)
PY
)"
  if [ -n "${pid:-}" ] && [ "${pid}" -gt 0 ] 2>/dev/null; then
    # Verify it is alive AND really a supervisor (guard against PID reuse).
    if kill -0 "$pid" 2>/dev/null && \
       tr '\0' ' ' < "/proc/$pid/cmdline" 2>/dev/null | grep -q "pipeline_supervisor.py"; then
      alive=1
    elif command -v powershell.exe >/dev/null 2>&1; then
      # The preferred supervisor may be the Windows process launched by Codex.
      # WSL cannot see that PID in /proc, so ask Windows before relaunching a
      # duplicate Linux supervisor.
      win_alive="$(powershell.exe -NoProfile -NonInteractive -Command "\
\$p = Get-CimInstance Win32_Process -Filter 'ProcessId=$pid' -ErrorAction SilentlyContinue; \
if (\$p -and \$p.CommandLine -like '*pipeline_supervisor.py*') { '1' } else { '0' }" 2>/dev/null | tr -d '\r' | tail -n 1)"
      if [ "$win_alive" = "1" ]; then
        alive=1
      fi
    fi
  fi
fi

if [ "$alive" = "1" ]; then
  # Healthy — nothing to do. (Quiet to keep the log small.)
  exit 0
fi

# Dead or never started: relaunch detached.
cd "$REPO" || { log "FATAL: cannot cd to $REPO"; exit 1; }
log "supervisor not alive — relaunching: pipeline_supervisor.py ${SUPERVISOR_ARGS[*]}"
nohup python3 tools/chatgpt-oracle/pipeline_supervisor.py "${SUPERVISOR_ARGS[@]}" \
  >>"${SCRIPT_DIR}/supervisor_logs/supervisor.log" 2>&1 &
log "relaunched, new pid=$!"
exit 0
