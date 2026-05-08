#!/usr/bin/env python3
"""outreach_error_monitor — token-saving log watcher.

Designed for unattended-mode operation. Tails the outreach pipeline's
log files; fires a macOS notification (osascript) ONLY when an error
pattern is observed. No claude / codex calls — this monitor never spends
LLM tokens. Rate-limited: identical signatures within COALESCE_WINDOW_S
collapse into a single notification.

Watched logs (path-glob, all under outreach_state/):

  supervisor_logs/supervisor.log
  supervisor_logs/inner_research.log
  supervisor_logs/inner_task_runner.log
  supervisor_logs/probe_*.log
  supervisor_logs/refill_*.log
  research_loop_logs/research_loop.log
  research_loop_logs/supervise_*.log
  task_runner_logs/task_runner.log
  task_runner_logs/draft_*.stdout.txt
  task_runner_logs/*.stderr.txt
  board_refill_logs/board_refill.log

Error patterns detected (regex-OR):

  - "^! "                            (LaTeX / shell error pattern)
  - "Traceback "                     (Python stack trace)
  - "ERROR\b" (case-sensitive)       (uppercase error tag)
  - "rc=([1-9][0-9]*)"               (non-zero return code, except whitelisted)
  - "FAIL(ED)?\b"                    (test/build failure)
  - "oracle poll timed out"          (board refill specific)
  - "MEMORYERROR|UnicodeError|FileNotFoundError|TimeoutExpired"

Heartbeat: writes "monitor alive" to its own log every HEARTBEAT_S so
the operator can confirm the watcher itself is running.

Stop by: touching .outreach_monitor_stop or sending SIGINT/SIGTERM.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
STATE_DIR = SCRIPT_DIR / "outreach_state"
MONITOR_LOG_DIR = STATE_DIR / "monitor_logs"
MONITOR_LOG = MONITOR_LOG_DIR / "monitor.log"
STOP_FILE = SCRIPT_DIR / ".outreach_monitor_stop"

WATCH_GLOBS = [
    "supervisor_logs/supervisor.log",
    "supervisor_logs/inner_research.log",
    "supervisor_logs/inner_task_runner.log",
    "supervisor_logs/probe_*.log",
    "supervisor_logs/refill_*.log",
    "research_loop_logs/research_loop.log",
    "research_loop_logs/supervise_*.log",
    "task_runner_logs/task_runner.log",
    "task_runner_logs/draft_*.stderr.txt",
    "task_runner_logs/*_stderr.txt",
    "board_refill_logs/board_refill.log",
]

ERROR_PATTERNS = [
    re.compile(r"^! "),
    re.compile(r"Traceback "),
    re.compile(r"\bERROR\b"),
    re.compile(r"\brc=([1-9][0-9]*)"),
    re.compile(r"\bFAIL(?:ED)?\b"),
    re.compile(r"oracle poll timed out"),
    re.compile(r"MemoryError|UnicodeError|FileNotFoundError|TimeoutExpired"),
    re.compile(r"\bABORTED\b"),
    re.compile(r"\bgate fail:"),  # task_runner gate failures
]

# Whitelist substrings — if a candidate error line contains any of these,
# it's NOT an error (e.g. "rc=0" obviously, but also FAIL inside a benign
# context like "no fail to report").
WHITELIST_PATTERNS = [
    re.compile(r"\brc=0\b"),
    re.compile(r"no fail"),
    re.compile(r"no error"),
    re.compile(r"FAILED \(0\)"),
    re.compile(r"# ERROR HANDLING"),
]

POLL_INTERVAL_S = 5
HEARTBEAT_S = 3600
COALESCE_WINDOW_S = 600  # same error sig within 10 min → 1 notification
MAX_LINE_LEN = 240


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _log(msg: str) -> None:
    MONITOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {msg}"
    try:
        with open(MONITOR_LOG, "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except OSError:
        pass


def _macos_notify(title: str, body: str) -> None:
    if sys.platform != "darwin":
        return
    safe_title = title.replace('"', '\\"')[:200]
    safe_body = body.replace('"', '\\"')[:300]
    script = f'display notification "{safe_body}" with title "{safe_title}"'
    try:
        subprocess.run(
            ["osascript", "-e", script],
            timeout=5,
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    except Exception:
        pass


def _is_error_line(line: str) -> bool:
    for w in WHITELIST_PATTERNS:
        if w.search(line):
            return False
    for p in ERROR_PATTERNS:
        if p.search(line):
            return True
    return False


def _err_signature(file: str, line: str) -> str:
    """Coalescing signature: file basename + first 80 chars of squashed line."""
    norm = re.sub(r"[0-9a-f]{6,}", "<hex>", line)
    norm = re.sub(r"\d+", "<n>", norm)
    norm = norm.strip()[:80]
    base = os.path.basename(file)
    h = hashlib.sha256(f"{base}|{norm}".encode("utf-8", errors="ignore")).hexdigest()[:12]
    return h


def _resolve_files() -> list[Path]:
    out: list[Path] = []
    for pattern in WATCH_GLOBS:
        for p in STATE_DIR.glob(pattern):
            if p.is_file():
                out.append(p)
    return sorted(set(out))


def _install_signal_handlers(stop: dict) -> None:
    def _h(signum, frame):
        stop["stop"] = True

    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            signal.signal(sig, _h)
        except (OSError, ValueError):
            pass


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--once", action="store_true",
                   help="scan once + exit (useful for cron-style invocation)")
    p.add_argument("--quiet", action="store_true",
                   help="suppress macOS notifications; log-only")
    p.add_argument("--coalesce-window-s", type=int, default=COALESCE_WINDOW_S)
    p.add_argument("--poll-interval-s", type=int, default=POLL_INTERVAL_S)
    p.add_argument("--heartbeat-s", type=int, default=HEARTBEAT_S)
    args = p.parse_args(argv)

    if STOP_FILE.exists():
        STOP_FILE.unlink()
    MONITOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    _log("error_monitor starting (pid={}, quiet={})".format(os.getpid(), args.quiet))

    stop = {"stop": False}
    _install_signal_handlers(stop)

    # Per-file read positions (offset bytes already consumed).
    positions: dict[str, int] = {}
    last_seen_at: dict[str, float] = {}  # signature → last fire time
    last_heartbeat = time.time()
    cycle = 0

    # Initial pass: jump to end-of-file for each existing log so we don't
    # re-fire on already-known historical errors.
    for f in _resolve_files():
        try:
            positions[str(f)] = f.stat().st_size
        except OSError:
            positions[str(f)] = 0

    _log(f"baselined {len(positions)} log files; tailing for new lines")

    while not stop["stop"] and not STOP_FILE.exists():
        cycle += 1
        files = _resolve_files()
        for f in files:
            sf = str(f)
            try:
                size = f.stat().st_size
            except OSError:
                continue
            old = positions.get(sf, 0)
            if size < old:
                # truncated / rotated — read from start
                old = 0
            if size == old:
                continue
            try:
                with open(f, "rb") as fh:
                    fh.seek(old)
                    chunk = fh.read(size - old)
            except OSError:
                continue
            positions[sf] = size
            try:
                text = chunk.decode("utf-8", errors="replace")
            except Exception:
                continue
            for raw in text.splitlines():
                line = raw.strip()
                if not line:
                    continue
                if not _is_error_line(line):
                    continue
                sig = _err_signature(sf, line)
                now = time.time()
                last = last_seen_at.get(sig, 0)
                if now - last < args.coalesce_window_s:
                    continue
                last_seen_at[sig] = now
                short = line[:MAX_LINE_LEN]
                _log(f"ERROR_DETECT {os.path.basename(sf)}: {short}")
                if not args.quiet:
                    _macos_notify(
                        f"outreach error: {os.path.basename(sf)}",
                        short,
                    )

        if time.time() - last_heartbeat > args.heartbeat_s:
            _log(f"heartbeat — alive, watched={len(positions)} files, cycles={cycle}")
            last_heartbeat = time.time()

        if args.once:
            break

        time.sleep(args.poll_interval_s)

    if STOP_FILE.exists():
        try:
            STOP_FILE.unlink()
        except OSError:
            pass
    _log("error_monitor exiting")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
