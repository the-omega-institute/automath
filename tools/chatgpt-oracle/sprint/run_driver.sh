#!/bin/bash
# Single-instance guard: mkdir is atomic, so only one driver can claim the lock dir.
D=/d/omega/automath/tools/chatgpt-oracle/sprint
exec >> "$D/driver.log" 2>&1
LOCK="$D/driver.lock.d"
# stale lock (owner gone) is reclaimed
if [ -d "$LOCK" ]; then
  old=$(cat "$LOCK/pid" 2>/dev/null)
  if [ -n "$old" ] && kill -0 "$old" 2>/dev/null; then
    echo "=== driver start refused $(date): pid $old holds the lock ==="
    exit 0
  fi
  rm -rf "$LOCK"
fi
if ! mkdir "$LOCK" 2>/dev/null; then
  echo "=== driver start refused $(date): lock race lost ==="
  exit 0
fi
echo $$ > "$LOCK/pid"
trap 'rm -rf "$LOCK"' EXIT INT TERM
echo "=== driver started $(date) pid=$$ ==="
# exec, not a child: the recorded pid must BE the driver, so killing the lock
# owner actually stops it instead of orphaning a running loop
exec bash "$D/driver.sh"
