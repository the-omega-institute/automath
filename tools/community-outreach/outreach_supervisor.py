#!/usr/bin/env python3
"""Community-outreach supervisor — outer loop that keeps the pipeline awake.

Mirrors tools/bedc-deep/supervisor.py for the outreach domain. Differences:

- No managed inner loop. The outreach pipeline runs as discrete subcommands
  (arxiv_watch, lit_staleness, oracle_consultant, codex_compose_paper) rather
  than a persistent worker. The PI agent dispatches them autonomously when
  the snapshot warrants.

- Server health is advisory only. outreach_oracle_server (port 8766) is
  optional — the supervisor reports status but does not auto-spawn it.

- Stale cleanup operates on the single GIT_OPS_LOCK file rather than per-
  target .in_progress markers (outreach_pipeline.py does not use those).

- Auto-commit is path-scoped to OUTREACH_LOG.md and RESEARCH_BOARD.md only.
  drafts/ files are user-reviewed and never auto-committed.

Stop the supervisor by creating tools/community-outreach/.outreach_stop or
sending SIGINT.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import signal
import subprocess
import sys
import time
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_DIR = SCRIPT_DIR / "outreach_state"
SUPERVISOR_LOG_DIR = STATE_DIR / "supervisor_logs"
STOP_FILE = SCRIPT_DIR / ".outreach_stop"
GIT_OPS_LOCK = STATE_DIR / ".git_ops.lock"

ORACLE_SERVER_URL = "http://localhost:8766"

DEFAULT_POLL_INTERVAL = 300        # seconds between supervisor ticks
DEFAULT_PI_REVIEW_HOURS = 6
DEFAULT_INBOX_WATCH_HOURS = 1
DEFAULT_LOCK_STALE_HOURS = 1
TARGET_BRANCH = "outreach-clean"

AUTO_COMMIT_PATHS = [
    "tools/community-outreach/OUTREACH_LOG.md",
    "tools/community-outreach/RESEARCH_BOARD.md",
]

sys.path.insert(0, str(SCRIPT_DIR))


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------


def _now() -> float:
    return time.time()


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def supervisor_log(msg: str) -> None:
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {msg}"
    print(line, flush=True)
    with open(SUPERVISOR_LOG_DIR / "supervisor.log", "a", encoding="utf-8") as f:
        f.write(line + "\n")


def _git(args: list[str], capture: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=str(REPO_ROOT),
        capture_output=capture,
        text=True,
    )


def macos_notify(title: str, body: str) -> None:
    if sys.platform != "darwin":
        return
    safe_title = title.replace('"', '\\"')
    safe_body = body.replace('"', '\\"')
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


# ---------------------------------------------------------------------------
# health probes
# ---------------------------------------------------------------------------


def server_status(timeout: int = 3) -> dict:
    try:
        with urllib.request.urlopen(f"{ORACLE_SERVER_URL}/status", timeout=timeout) as r:
            return json.loads(r.read().decode("utf-8"), strict=False)
    except Exception:
        return {}


def report_server_status() -> None:
    s = server_status()
    if not s:
        supervisor_log("oracle_server: not responding (advisory; not auto-spawning)")
    else:
        diag = s.get("diagnosis") or "ok"
        active = len(s.get("active_recent_agents") or [])
        queued = len(s.get("queued_tasks") or [])
        supervisor_log(f"oracle_server: diag={diag} active={active} queued={queued}")


def run_inbox_watcher() -> bool:
    """Foreground call (~10-30s on a 14-day window). Returns True if process
    completed (rc==0)."""
    watcher = SCRIPT_DIR / "outreach_inbox_watcher.py"
    if not watcher.exists():
        return False
    try:
        proc = subprocess.run(
            ["python3", str(watcher)],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=120,
        )
    except Exception as exc:
        supervisor_log(f"inbox_watcher error: {exc}")
        return False
    if proc.returncode != 0:
        supervisor_log(f"inbox_watcher rc={proc.returncode}: {(proc.stderr or '')[:200]}")
        return False
    head = (proc.stdout or "").splitlines()[:1]
    supervisor_log(f"inbox_watcher: {head[0] if head else 'no output'}")
    return True


def cleanup_stale_lock(stale_hours: float) -> bool:
    if not GIT_OPS_LOCK.exists():
        return False
    try:
        age = _now() - GIT_OPS_LOCK.stat().st_mtime
    except OSError:
        return False
    if age < stale_hours * 3600:
        return False
    try:
        GIT_OPS_LOCK.unlink()
        supervisor_log(f"removed stale GIT_OPS_LOCK (age {age / 3600:.1f}h > {stale_hours}h)")
        return True
    except OSError as exc:
        supervisor_log(f"failed to remove GIT_OPS_LOCK: {exc}")
        return False


# ---------------------------------------------------------------------------
# auto-commit
# ---------------------------------------------------------------------------


def commit_and_push_if_changed() -> bool:
    diff = _git(["status", "--porcelain", *AUTO_COMMIT_PATHS])
    if not diff.stdout.strip():
        return False
    files: list[str] = []
    for line in diff.stdout.splitlines():
        parts = line.strip().split(None, 1)
        if len(parts) == 2:
            files.append(parts[1])
    if not files:
        return False
    branch = _git(["branch", "--show-current"]).stdout.strip()
    if branch != TARGET_BRANCH:
        supervisor_log(f"auto-commit skipped: on branch {branch!r}, refusing to push to {TARGET_BRANCH}")
        return False
    supervisor_log(f"auto-commit: {len(files)} changed files: {', '.join(files)}")
    _git(["add", *files], capture=False)
    msg = f"outreach supervisor: board snapshot {_now_iso()}"
    rc = _git(["commit", "-m", msg]).returncode
    if rc != 0:
        supervisor_log("auto-commit: git commit returned non-zero (race or empty)")
        return False
    push = _git(["push", "origin", branch], capture=False)
    if push.returncode != 0:
        supervisor_log(f"auto-commit: push failed rc={push.returncode}")
        return False
    supervisor_log(f"auto-commit + push complete on {branch}")
    return True


# ---------------------------------------------------------------------------
# PI agent review
# ---------------------------------------------------------------------------


def run_pi_review(supervisor_state: dict) -> dict | None:
    import outreach_pi_agent as pi

    def _adjust_cooldown_cb(args: dict) -> None:
        if not isinstance(args, dict):
            return
        for key, target in (
            ("pi_review_hours", "pi_review_hours"),
            ("arxiv_watch_hours", "arxiv_watch_hours"),
            ("lit_staleness_hours", "lit_staleness_hours"),
            ("inbox_watcher_hours", "inbox_watcher_hours"),
        ):
            if key in args:
                try:
                    supervisor_state[target] = float(args[key])
                    supervisor_log(f"pi: cooldown adjusted {target}={args[key]}")
                except (TypeError, ValueError):
                    pass

    def _restart_inner_cb() -> None:
        supervisor_log("pi: restart_inner requested but no managed inner loop in v0")

    callbacks = {
        "adjust_cooldown": _adjust_cooldown_cb,
        "restart_inner": _restart_inner_cb,
    }
    plan = pi.run_review(supervisor_callbacks=callbacks)
    if plan is None:
        supervisor_log("pi review returned no plan")
        return None
    health = plan.get("loop_health") or "unknown"
    autonomous_n = len(plan.get("autonomous_actions") or [])
    inbox_n = len(plan.get("human_inbox") or [])
    concerns_n = len(plan.get("concerns") or [])
    supervisor_log(
        f"pi verdict: health={health} autonomous={autonomous_n} inbox={inbox_n} concerns={concerns_n}"
    )
    if health == "blocked":
        macos_notify(
            "outreach supervisor: pipeline blocked",
            f"PI flagged {inbox_n} inbox items + {concerns_n} concerns — see .outreach_human_inbox.md",
        )
    return plan


# ---------------------------------------------------------------------------
# main loop
# ---------------------------------------------------------------------------


def _install_signal_handlers() -> None:
    def _handler(signum, frame):
        try:
            STOP_FILE.write_text(f"signal {signum} at {_now_iso()}\n", encoding="utf-8")
        except OSError:
            pass

    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            signal.signal(sig, _handler)
        except (OSError, ValueError):
            pass


def main() -> int:
    parser = argparse.ArgumentParser(description="Community-outreach supervisor")
    parser.add_argument("--poll-interval", type=int, default=DEFAULT_POLL_INTERVAL,
                        help=f"seconds between ticks (default {DEFAULT_POLL_INTERVAL})")
    parser.add_argument("--pi-review-hours", type=float, default=DEFAULT_PI_REVIEW_HOURS,
                        help=f"hours between PI agent reviews (default {DEFAULT_PI_REVIEW_HOURS})")
    parser.add_argument("--inbox-watch-hours", type=float, default=DEFAULT_INBOX_WATCH_HOURS,
                        help=f"hours between Apple Mail Inbox sweeps (default {DEFAULT_INBOX_WATCH_HOURS})")
    parser.add_argument("--no-inbox-watcher", action="store_true",
                        help="disable periodic inbox watcher")
    parser.add_argument("--lock-stale-hours", type=float, default=DEFAULT_LOCK_STALE_HOURS,
                        help=f"hours after which GIT_OPS_LOCK is considered stale (default {DEFAULT_LOCK_STALE_HOURS})")
    parser.add_argument("--no-auto-commit", action="store_true",
                        help="disable auto-commit + push of OUTREACH_LOG.md / RESEARCH_BOARD.md")
    parser.add_argument("--no-pi-review", action="store_true",
                        help="disable periodic PI agent review")
    parser.add_argument("--once", action="store_true",
                        help="run a single tick (PI review forced) then exit")
    args = parser.parse_args()

    if STOP_FILE.exists():
        supervisor_log(f"clearing stale STOP_FILE {STOP_FILE}")
        STOP_FILE.unlink()

    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    _install_signal_handlers()
    supervisor_log(
        f"supervisor starting (poll={args.poll_interval}s pi_review={args.pi_review_hours}h "
        f"auto_commit={'off' if args.no_auto_commit else 'on'} pi_review_enabled={not args.no_pi_review})"
    )

    supervisor_state: dict = {
        "pi_review_hours": args.pi_review_hours,
        "arxiv_watch_hours": 12.0,
        "lit_staleness_hours": 24.0,
        "inbox_watcher_hours": args.inbox_watch_hours,
    }

    last_pi_review_ts = 0.0
    last_inbox_watch_ts = 0.0

    try:
        while not STOP_FILE.exists():
            tick_started = _now()

            report_server_status()
            cleanup_stale_lock(args.lock_stale_hours)

            if not args.no_inbox_watcher:
                since_inbox_h = (_now() - last_inbox_watch_ts) / 3600.0
                if args.once or since_inbox_h >= supervisor_state["inbox_watcher_hours"]:
                    try:
                        run_inbox_watcher()
                    except Exception as exc:
                        supervisor_log(f"inbox watcher error: {exc}")
                    last_inbox_watch_ts = _now()

            if not args.no_auto_commit:
                try:
                    commit_and_push_if_changed()
                except Exception as exc:
                    supervisor_log(f"auto-commit error: {exc}")

            if not args.no_pi_review:
                since_pi_h = (_now() - last_pi_review_ts) / 3600.0
                if args.once or since_pi_h >= supervisor_state["pi_review_hours"]:
                    supervisor_log("running PI agent review")
                    try:
                        run_pi_review(supervisor_state)
                    except Exception as exc:
                        supervisor_log(f"pi review error (continuing): {exc}")
                    last_pi_review_ts = _now()

            if args.once:
                break

            elapsed = _now() - tick_started
            sleep_for = max(5.0, args.poll_interval - elapsed)
            time.sleep(sleep_for)

    except KeyboardInterrupt:
        supervisor_log("supervisor interrupted")
    finally:
        if STOP_FILE.exists():
            try:
                STOP_FILE.unlink()
            except OSError:
                pass
        supervisor_log("supervisor exiting")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
