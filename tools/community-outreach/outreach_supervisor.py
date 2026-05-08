#!/usr/bin/env python3
"""Community-outreach supervisor — outer loop that keeps the pipeline alive.

Pattern adapted from tools/bedc-deep/supervisor.py (AlyciaBHZ commits on
newmath@bedc-claim-packet-pipeline). Loning-side wrappers (loning_watch,
paper_review) intentionally omitted: outreach has no cross-pipeline analog.

Responsibilities:

  1. Server health: ensure outreach_oracle_server.py is running on :8766.
  2. Stale cleanup: prune dead .in_progress claims + stale GIT_OPS_LOCK each pass.
  3. Inner loop manager: spawn outreach_research_loop.py --loop, restart on
     crash with backoff. Drains RESEARCH_BOARD.md Backlog one target at a
     time via dispatch_worktree --supervise.
  4. Cooldown-driven short tasks (fire-and-forget subprocess):
       - arxiv_watch (NyxID-routed paper sweep)
       - outreach_inbox_watcher (Apple Mail Inbox sweep for replies)
       - lit_staleness (per-target staleness re-check)
       - outreach_board_refill (ChatGPT Project oracle → new T-NN candidates;
         currently a stub until the Project URL is wired in)
  5. Tab health alert: macOS notify when outreach_oracle_server reports
     `queue_waiting_for_browser_agent` longer than 5 minutes.
  6. Auto-commit: detect changes in OUTREACH_LOG.md / RESEARCH_BOARD.md only
     (drafts/ files are never auto-committed — they need user review).
  7. PI agent review: periodic claude consultation via outreach_pi_agent;
     accepts adjust_cooldown autonomous actions.

All external sends remain user-gated. Drafts go to drafts/, the operator
reviews and ships manually. The supervisor never posts to GitHub / Apple
Mail / X / forums.

Stop the supervisor by creating tools/community-outreach/.outreach_stop or
sending SIGINT. On exit the inner loop is killed cleanly via SIGTERM.
"""

from __future__ import annotations

import argparse
import json
import os
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
RESEARCH_CLAIMS_DIR = STATE_DIR / "research_claims"
STOP_FILE = SCRIPT_DIR / ".outreach_stop"
GIT_OPS_LOCK = STATE_DIR / ".git_ops.lock"

ORACLE_SERVER_URL = "http://localhost:8766"
ORACLE_SERVER_SCRIPT = SCRIPT_DIR / "outreach_oracle_server.py"
RESEARCH_LOOP_SCRIPT = SCRIPT_DIR / "outreach_research_loop.py"
TASK_RUNNER_SCRIPT = SCRIPT_DIR / "outreach_task_runner.py"
ARXIV_WATCH = SCRIPT_DIR / "arxiv_watch.py"
LIT_STALENESS = SCRIPT_DIR / "lit_staleness.py"
INBOX_WATCHER = SCRIPT_DIR / "outreach_inbox_watcher.py"
BOARD_REFILL = SCRIPT_DIR / "outreach_board_refill.py"

DEFAULT_PARALLEL = 1
DEFAULT_POLL_INTERVAL = 300
DEFAULT_PI_REVIEW_HOURS = 6
DEFAULT_INBOX_WATCH_HOURS = 1
DEFAULT_ARXIV_WATCH_HOURS = 12
DEFAULT_LIT_STALENESS_HOURS = 24
DEFAULT_BOARD_REFILL_HOURS = 24
DEFAULT_LOCK_STALE_HOURS = 1
DEFAULT_INNER_RESTART_BACKOFF_S = 30
TAB_STUCK_THRESHOLD_S = 300
TARGET_BRANCH = "openproblem-target"

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


def _now_tag_safe() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


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
# server health
# ---------------------------------------------------------------------------


def server_status(timeout: int = 3) -> dict:
    try:
        with urllib.request.urlopen(f"{ORACLE_SERVER_URL}/status", timeout=timeout) as r:
            return json.loads(r.read().decode("utf-8"), strict=False)
    except Exception:
        return {}


def server_alive(timeout: int = 3) -> bool:
    return server_status(timeout).get("port") == 8766


def ensure_server() -> int | None:
    if server_alive():
        return None
    if not ORACLE_SERVER_SCRIPT.exists():
        supervisor_log(f"oracle_server: {ORACLE_SERVER_SCRIPT.name} missing — cannot auto-spawn")
        return None
    supervisor_log("server not responding; spawning outreach_oracle_server.py")
    proc = subprocess.Popen(
        ["python3", str(ORACLE_SERVER_SCRIPT)],
        cwd=str(REPO_ROOT),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )
    time.sleep(3)
    if not server_alive():
        supervisor_log("server still not responding after spawn; check manually")
        return None
    supervisor_log(f"server spawned pid={proc.pid}")
    return proc.pid


def _active_tab_count() -> int:
    s = server_status()
    return len(s.get("active_recent_agents") or [])


def queue_stuck_too_long(threshold_seconds: int) -> bool:
    s = server_status()
    if s.get("diagnosis") != "queue_waiting_for_browser_agent":
        return False
    queued = s.get("queued_tasks") or []
    return any((t.get("age_seconds") or 0) > threshold_seconds for t in queued)


# ---------------------------------------------------------------------------
# stale cleanup
# ---------------------------------------------------------------------------


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


def stale_research_cleanup() -> int:
    """Sweep stale .in_progress research claims via outreach_research_loop."""
    try:
        from outreach_research_loop import cleanup_stale_claims  # noqa: PLC0415
    except ImportError:
        return 0
    try:
        return cleanup_stale_claims()
    except Exception as exc:
        supervisor_log(f"stale_research_cleanup error: {exc}")
        return 0


# ---------------------------------------------------------------------------
# inner loop manager
# ---------------------------------------------------------------------------


def _spawn_inner(script: Path, *, log_name: str, label: str, extra_args: list[str] | None = None) -> subprocess.Popen:
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    if not script.exists():
        supervisor_log(
            f"{label}: {script.name} missing — supervisor will idle on this slot; "
            f"periodic short tasks still run"
        )
        proc = subprocess.Popen(
            ["python3", "-c", "import sys; sys.exit(0)"],
            cwd=str(REPO_ROOT),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return proc
    log_handle = open(SUPERVISOR_LOG_DIR / log_name, "ab")
    log_handle.write(
        f"\n=== {label} spawn at {_now_iso()} ===\n".encode()
    )
    log_handle.flush()
    cmd = ["python3", str(script), "--loop", *(extra_args or [])]
    proc = subprocess.Popen(
        cmd,
        cwd=str(REPO_ROOT),
        stdout=log_handle,
        stderr=subprocess.STDOUT,
        start_new_session=True,
    )
    supervisor_log(f"{label}: spawned pid={proc.pid}")
    return proc


def spawn_research_loop(parallel: int) -> subprocess.Popen:
    return _spawn_inner(
        RESEARCH_LOOP_SCRIPT,
        log_name="inner_research.log",
        label="research_loop",
        extra_args=["--parallel", str(parallel)],
    )


def spawn_task_runner() -> subprocess.Popen:
    return _spawn_inner(
        TASK_RUNNER_SCRIPT,
        log_name="inner_task_runner.log",
        label="task_runner",
        extra_args=[],
    )


def stop_inner(inner: subprocess.Popen, grace_seconds: int = 30) -> None:
    if inner.poll() is not None:
        return
    try:
        os.killpg(inner.pid, signal.SIGTERM)
        supervisor_log(f"sent SIGTERM to inner pid={inner.pid}")
    except (ProcessLookupError, OSError):
        return
    try:
        inner.wait(timeout=grace_seconds)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(inner.pid, signal.SIGKILL)
            supervisor_log(f"escalated to SIGKILL on inner pid={inner.pid}")
        except (ProcessLookupError, OSError):
            pass


# ---------------------------------------------------------------------------
# fire-and-forget short-task triggers
# ---------------------------------------------------------------------------


def _spawn_short_task(script: Path, label: str, extra_args: list[str] | None = None) -> None:
    if not script.exists():
        supervisor_log(f"{label}: {script.name} missing, skipping")
        return
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_path = SUPERVISOR_LOG_DIR / f"{label}_{_now_tag_safe()}.log"
    cmd = ["python3", str(script), *(extra_args or [])]
    with open(log_path, "ab") as logf:
        subprocess.Popen(
            cmd,
            cwd=str(REPO_ROOT),
            stdout=logf,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
    supervisor_log(f"{label}: spawned ({script.name})")


def trigger_arxiv_watch() -> None:
    _spawn_short_task(ARXIV_WATCH, "arxiv_watch", ["--since", "7d"])


def trigger_inbox_watcher() -> None:
    _spawn_short_task(INBOX_WATCHER, "inbox_watcher")


def trigger_lit_staleness() -> None:
    _spawn_short_task(LIT_STALENESS, "lit_staleness")


def trigger_board_refill() -> None:
    _spawn_short_task(BOARD_REFILL, "board_refill")


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
        supervisor_log(
            f"auto-commit skipped: on branch {branch!r}, refusing to push to {TARGET_BRANCH}"
        )
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
    try:
        import outreach_pi_agent as pi  # noqa: PLC0415
    except ImportError as exc:
        supervisor_log(f"outreach_pi_agent import failed: {exc}")
        return None

    def _adjust_cooldown_cb(args: dict) -> str | None:
        if not isinstance(args, dict):
            return "args not dict"
        applied: list[str] = []
        for key in (
            "pi_review_hours",
            "arxiv_watch_hours",
            "lit_staleness_hours",
            "inbox_watcher_hours",
            "board_refill_hours",
        ):
            if key in args:
                try:
                    supervisor_state[key] = float(args[key])
                    applied.append(f"{key}={args[key]}")
                except (TypeError, ValueError):
                    pass
        return ", ".join(applied) or "no recognized cooldown keys"

    def _restart_inner_cb() -> str | None:
        stopped = []
        for slot in ("inner_research", "inner_task"):
            proc: subprocess.Popen | None = supervisor_state.get(slot)
            if proc is not None and proc.poll() is None:
                stop_inner(proc, grace_seconds=20)
                stopped.append(slot)
            supervisor_state[slot] = None
        return f"stopped {stopped}; supervisor will respawn" if stopped else "no live inner to stop"

    callbacks = {
        "adjust_cooldown": _adjust_cooldown_cb,
        "restart_inner": _restart_inner_cb,
    }
    try:
        plan = pi.run_review(supervisor_callbacks=callbacks)
    except Exception as exc:
        supervisor_log(f"pi review error: {exc}")
        return None
    if plan is None:
        supervisor_log("pi review returned no plan")
        return None
    health = plan.get("loop_health") or "unknown"
    autonomous_n = len(plan.get("autonomous_actions") or [])
    inbox_n = len(plan.get("human_inbox") or [])
    concerns_n = len(plan.get("concerns") or [])
    supervisor_log(
        f"pi verdict: health={health} autonomous={autonomous_n} "
        f"inbox={inbox_n} concerns={concerns_n}"
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
    parser.add_argument("--parallel", type=int, default=DEFAULT_PARALLEL,
                        help=f"inner research loop parallelism (default {DEFAULT_PARALLEL})")
    parser.add_argument("--poll-interval", type=int, default=DEFAULT_POLL_INTERVAL,
                        help=f"seconds between supervisor ticks (default {DEFAULT_POLL_INTERVAL})")
    parser.add_argument("--pi-review-hours", type=float, default=DEFAULT_PI_REVIEW_HOURS)
    parser.add_argument("--inbox-watch-hours", type=float, default=DEFAULT_INBOX_WATCH_HOURS)
    parser.add_argument("--arxiv-watch-hours", type=float, default=DEFAULT_ARXIV_WATCH_HOURS)
    parser.add_argument("--lit-staleness-hours", type=float, default=DEFAULT_LIT_STALENESS_HOURS)
    parser.add_argument("--board-refill-hours", type=float, default=DEFAULT_BOARD_REFILL_HOURS,
                        help="cooldown for outreach_board_refill (currently a stub)")
    parser.add_argument("--lock-stale-hours", type=float, default=DEFAULT_LOCK_STALE_HOURS)
    parser.add_argument("--inner-restart-backoff", type=int, default=DEFAULT_INNER_RESTART_BACKOFF_S)
    parser.add_argument("--no-auto-commit", action="store_true")
    parser.add_argument("--no-pi-review", action="store_true")
    parser.add_argument("--no-inner", action="store_true",
                        help="do not spawn either inner daemon (research_loop + task_runner); only run short-task triggers")
    parser.add_argument("--no-research-loop", action="store_true",
                        help="skip the research_loop inner (drains RESEARCH_BOARD T-NN entries)")
    parser.add_argument("--no-task-runner", action="store_true",
                        help="skip the task_runner inner (drains outreach_state/task_queue/*.json)")
    parser.add_argument("--no-server-spawn", action="store_true",
                        help="do not auto-spawn outreach_oracle_server even if dead")
    parser.add_argument("--once", action="store_true",
                        help="run a single tick (PI + all short tasks forced) then exit")
    args = parser.parse_args()

    if STOP_FILE.exists():
        supervisor_log(f"clearing stale STOP_FILE {STOP_FILE}")
        STOP_FILE.unlink()

    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    RESEARCH_CLAIMS_DIR.mkdir(parents=True, exist_ok=True)
    _install_signal_handlers()
    supervisor_log(
        f"supervisor starting (parallel={args.parallel} poll={args.poll_interval}s "
        f"pi_review={'off' if args.no_pi_review else f'{args.pi_review_hours}h'} "
        f"auto_commit={'off' if args.no_auto_commit else 'on'} "
        f"inner={'off' if args.no_inner else 'on'} "
        f"server_spawn={'off' if args.no_server_spawn else 'on'})"
    )

    supervisor_state: dict = {
        "inner_research": None,
        "inner_task": None,
        "pi_review_hours": args.pi_review_hours,
        "arxiv_watch_hours": args.arxiv_watch_hours,
        "lit_staleness_hours": args.lit_staleness_hours,
        "inbox_watcher_hours": args.inbox_watch_hours,
        "board_refill_hours": args.board_refill_hours,
    }

    last_pi_ts = 0.0
    last_inbox_ts = 0.0
    last_arxiv_ts = 0.0
    last_lit_ts = 0.0
    last_refill_ts = 0.0
    last_tab_alert_ts = 0.0
    last_research_exit_ts = 0.0
    last_task_exit_ts = 0.0

    try:
        while not STOP_FILE.exists():
            tick_started = _now()

            if not args.no_server_spawn:
                ensure_server()

            cleanup_stale_lock(args.lock_stale_hours)
            cleaned = stale_research_cleanup()
            if cleaned:
                supervisor_log(f"cleaned {cleaned} stale research claims")

            if not args.no_inner:
                # research_loop slot
                if not args.no_research_loop:
                    proc = supervisor_state.get("inner_research")
                    if proc is None or proc.poll() is not None:
                        if proc is not None:
                            rc = proc.poll()
                            since = _now() - last_research_exit_ts
                            if since < args.inner_restart_backoff:
                                pass  # in backoff window — try again next tick
                            else:
                                supervisor_log(f"research_loop exited rc={rc}; respawning")
                                supervisor_state["inner_research"] = spawn_research_loop(args.parallel)
                                last_research_exit_ts = _now()
                        else:
                            supervisor_state["inner_research"] = spawn_research_loop(args.parallel)
                # task_runner slot
                if not args.no_task_runner:
                    proc = supervisor_state.get("inner_task")
                    if proc is None or proc.poll() is not None:
                        if proc is not None:
                            rc = proc.poll()
                            since = _now() - last_task_exit_ts
                            if since < args.inner_restart_backoff:
                                pass
                            else:
                                supervisor_log(f"task_runner exited rc={rc}; respawning")
                                supervisor_state["inner_task"] = spawn_task_runner()
                                last_task_exit_ts = _now()
                        else:
                            supervisor_state["inner_task"] = spawn_task_runner()

            since_inbox_h = (_now() - last_inbox_ts) / 3600.0
            if args.once or since_inbox_h >= supervisor_state["inbox_watcher_hours"]:
                trigger_inbox_watcher()
                last_inbox_ts = _now()

            since_arxiv_h = (_now() - last_arxiv_ts) / 3600.0
            if args.once or since_arxiv_h >= supervisor_state["arxiv_watch_hours"]:
                trigger_arxiv_watch()
                last_arxiv_ts = _now()

            since_lit_h = (_now() - last_lit_ts) / 3600.0
            if args.once or since_lit_h >= supervisor_state["lit_staleness_hours"]:
                trigger_lit_staleness()
                last_lit_ts = _now()

            since_refill_h = (_now() - last_refill_ts) / 3600.0
            if args.once or since_refill_h >= supervisor_state["board_refill_hours"]:
                trigger_board_refill()
                last_refill_ts = _now()

            if queue_stuck_too_long(TAB_STUCK_THRESHOLD_S):
                if _now() - last_tab_alert_ts > 600:
                    supervisor_log(
                        "tab health: queue_waiting_for_browser_agent > 5min — verify ChatGPT tabs ACTIVE"
                    )
                    macos_notify(
                        "outreach supervisor: tab stuck",
                        "ChatGPT outreach Project tab stuck > 5 min — open the project tab and click Start",
                    )
                    last_tab_alert_ts = _now()

            if not args.no_auto_commit:
                try:
                    commit_and_push_if_changed()
                except Exception as exc:
                    supervisor_log(f"auto-commit error: {exc}")

            if not args.no_pi_review:
                since_pi_h = (_now() - last_pi_ts) / 3600.0
                if args.once or since_pi_h >= supervisor_state["pi_review_hours"]:
                    plan = run_pi_review(supervisor_state)
                    last_pi_ts = _now()
                    if plan:
                        for entry in plan.get("autonomous_actions") or []:
                            action = (entry.get("action") or "").strip()
                            if action == "run_arxiv_watch":
                                last_arxiv_ts = _now()
                            elif action == "run_lit_staleness":
                                last_lit_ts = _now()
                            elif action == "run_inbox_watcher":
                                last_inbox_ts = _now()

            if args.once:
                break

            elapsed = _now() - tick_started
            time.sleep(max(5.0, args.poll_interval - elapsed))

    except KeyboardInterrupt:
        supervisor_log("supervisor interrupted")
    finally:
        for slot in ("inner_research", "inner_task"):
            proc = supervisor_state.get(slot)
            if proc is not None:
                stop_inner(proc, grace_seconds=20)
        if STOP_FILE.exists():
            try:
                STOP_FILE.unlink()
            except OSError:
                pass
        supervisor_log("supervisor exiting")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
