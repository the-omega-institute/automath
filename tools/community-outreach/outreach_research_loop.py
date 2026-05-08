#!/usr/bin/env python3
"""Outreach research inner loop — drains RESEARCH_BOARD.md Backlog targets.

Spawned as a daemon by outreach_supervisor.py (`--loop` mode), or run once
on a single target for testing (`--once --todo-id T-NN`). For each
actionable T-NN entry on the board:

  1. Acquire a claim marker:
       outreach_state/research_claims/<slug>/.in_progress
  2. Dispatch the canonical safe local experiment + research pass:
       python3 dispatch_worktree.py --supervise --supervise-id <id> --run
  3. Write a thin summary for the operator:
       drafts/<slug>_research_summary.md
     (User reviews + approves before any external send.)
  4. Mark the board entry `Pending User Approval`.
  5. Release the claim.

Hard rules carried from project conventions:
  - never edits drafts/ files belonging to other targets (only writes its
    own <slug>_research_summary.md)
  - never sends anything externally
  - skips targets whose Status contains CLOSED / DISCARDED / OVERTAKEN /
    SOLVED / "Pending User Approval"
  - skips targets that already have a recent (< 24h) summary (cooldown)

Stale claims (default > 4h since marker mtime, no live process) are reaped
by cleanup_stale_claims(); the supervisor calls this every tick.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_DIR = SCRIPT_DIR / "outreach_state"
RESEARCH_CLAIMS_DIR = STATE_DIR / "research_claims"
RESEARCH_LOOP_LOG_DIR = STATE_DIR / "research_loop_logs"
RESEARCH_LOOP_STATUS = STATE_DIR / "research_loop.status.json"
RESEARCH_BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"
DRAFTS_DIR = SCRIPT_DIR / "drafts"
TARGETS_DIR = SCRIPT_DIR / "targets"
DISPATCH_WORKTREE = SCRIPT_DIR / "dispatch_worktree.py"

DEFAULT_PARALLEL = 1
DEFAULT_POLL_INTERVAL = 120
DEFAULT_CLAIM_STALE_HOURS = 4
DEFAULT_TARGET_TIMEOUT_S = 7200  # 2h hard cap per target
SUMMARY_COOLDOWN_HOURS = 24

# Regex matchers for board status filtering. Case-insensitive substring tests.
SKIP_STATUS_PATTERNS = [
    "🔴",  # red status emoji used for closed/discarded
    "🟠",  # orange status emoji used for overtaken
    "CLOSED",
    "DISCARDED",
    "OVERTAKEN",
    "SOLVED",
    "DROP",
    "Pending User Approval",
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


def loop_log(msg: str) -> None:
    RESEARCH_LOOP_LOG_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {msg}"
    print(line, flush=True)
    with open(RESEARCH_LOOP_LOG_DIR / "research_loop.log", "a", encoding="utf-8") as f:
        f.write(line + "\n")


# ---------------------------------------------------------------------------
# board parsing (delegated to dispatch_worktree)
# ---------------------------------------------------------------------------


def _parse_board_safe():
    """Best-effort parse_board call. Returns dict[todo_id, TodoSpec] or {}."""
    try:
        from outreach_board_parser import parse_board  # noqa: PLC0415
    except Exception as exc:
        loop_log(f"outreach_board_parser import failed: {exc}")
        return {}
    try:
        return parse_board(RESEARCH_BOARD_PATH)
    except Exception as exc:
        loop_log(f"parse_board failed: {exc}")
        return {}


def _is_skipped(status: str) -> bool:
    s = (status or "")
    s_lower = s.lower()
    for pat in SKIP_STATUS_PATTERNS:
        if pat.lower() in s_lower:
            return True
    # Status field can also start with a check or be Backlog-only — both pass.
    return False


def _summary_path(slug: str) -> Path:
    return DRAFTS_DIR / f"{slug}_research_summary.md"


def _has_recent_summary(slug: str, cooldown_hours: float) -> bool:
    p = _summary_path(slug)
    if not p.exists():
        return False
    try:
        age = _now() - p.stat().st_mtime
    except OSError:
        return False
    return age < cooldown_hours * 3600


# ---------------------------------------------------------------------------
# claim semantics
# ---------------------------------------------------------------------------


def _claim_dir(slug: str) -> Path:
    return RESEARCH_CLAIMS_DIR / slug


def _claim_marker(slug: str) -> Path:
    return _claim_dir(slug) / ".in_progress"


def _claim_pid_file(slug: str) -> Path:
    return _claim_dir(slug) / ".pid"


def claim(slug: str) -> bool:
    """Atomically place an .in_progress marker. Returns True iff acquired."""
    d = _claim_dir(slug)
    d.mkdir(parents=True, exist_ok=True)
    marker = _claim_marker(slug)
    if marker.exists():
        return False
    try:
        # O_EXCL ensures atomic create.
        fd = os.open(str(marker), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        os.write(fd, f"claimed_at={_now_iso()}\npid={os.getpid()}\n".encode())
        os.close(fd)
    except FileExistsError:
        return False
    except OSError as exc:
        loop_log(f"claim({slug}) failed: {exc}")
        return False
    try:
        _claim_pid_file(slug).write_text(str(os.getpid()), encoding="utf-8")
    except OSError:
        pass
    return True


def release(slug: str) -> None:
    for p in (_claim_marker(slug), _claim_pid_file(slug)):
        try:
            p.unlink()
        except FileNotFoundError:
            pass
        except OSError as exc:
            loop_log(f"release({slug}) cleanup error on {p.name}: {exc}")


def _pid_alive(pid: int) -> bool:
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
        return True
    except (ProcessLookupError, OSError):
        return False


def cleanup_stale_claims(stale_hours: float = DEFAULT_CLAIM_STALE_HOURS) -> int:
    """Sweep .in_progress markers older than stale_hours OR with dead pid.

    Called by the supervisor every tick. Returns count of claims released.
    """
    if not RESEARCH_CLAIMS_DIR.exists():
        return 0
    released = 0
    cutoff = _now() - stale_hours * 3600
    for d in RESEARCH_CLAIMS_DIR.iterdir():
        if not d.is_dir():
            continue
        marker = d / ".in_progress"
        if not marker.exists():
            continue
        try:
            mtime = marker.stat().st_mtime
        except OSError:
            continue
        pid = 0
        pid_file = d / ".pid"
        if pid_file.exists():
            try:
                pid = int((pid_file.read_text(encoding="utf-8").strip() or "0"))
            except (OSError, ValueError):
                pid = 0
        if mtime > cutoff and _pid_alive(pid):
            continue
        # stale claim: either too old or pid is gone
        try:
            marker.unlink()
        except OSError:
            pass
        try:
            pid_file.unlink()
        except (FileNotFoundError, OSError):
            pass
        released += 1
    return released


# ---------------------------------------------------------------------------
# board status update (mark Pending User Approval)
# ---------------------------------------------------------------------------


def mark_pending_user_approval(todo_id: str, note: str = "") -> bool:
    """Update the | Status | row of the matching ### todo block.

    Conservative: only flips the status when current value does not already
    contain `Pending User Approval`. Returns True on a write.
    """
    if not RESEARCH_BOARD_PATH.exists():
        return False
    text = RESEARCH_BOARD_PATH.read_text(encoding="utf-8")
    # Find the todo's ### block.
    block_re = re.compile(
        rf"(### {re.escape(todo_id)} ·.*?)(?=\n### T-|\Z)", re.DOTALL
    )
    m = block_re.search(text)
    if not m:
        loop_log(f"mark_pending_user_approval: {todo_id} block not found")
        return False
    block = m.group(1)
    status_row_re = re.compile(r"^\| Status \| (.+?) \|\s*$", re.MULTILINE)
    sm = status_row_re.search(block)
    if not sm:
        loop_log(f"mark_pending_user_approval: {todo_id} status row not found")
        return False
    current = sm.group(1)
    if "Pending User Approval" in current:
        return False
    new_status = (
        f"**Pending User Approval** — research_loop completed {_now_iso()}"
        + (f" · {note}" if note else "")
    )
    new_block = block[: sm.start(1)] + new_status + block[sm.end(1) :]
    new_text = text[: m.start(1)] + new_block + text[m.end(1) :]
    RESEARCH_BOARD_PATH.write_text(new_text, encoding="utf-8")
    loop_log(f"marked {todo_id} Pending User Approval")
    return True


# ---------------------------------------------------------------------------
# work dispatch
# ---------------------------------------------------------------------------


def _spawn_supervise(todo_id: str, timeout_s: int) -> tuple[int, str]:
    """Run dispatch_worktree.py --supervise --supervise-id <id> --run.

    Returns (returncode, stdout_path). On timeout returns rc=124.
    """
    if not DISPATCH_WORKTREE.exists():
        return 127, ""
    RESEARCH_LOOP_LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_path = RESEARCH_LOOP_LOG_DIR / f"supervise_{todo_id}_{_now_tag_safe()}.log"
    cmd = [
        "python3", str(DISPATCH_WORKTREE),
        "--supervise",
        "--supervise-id", todo_id,
        "--run",
    ]
    with open(log_path, "ab") as logf:
        proc = subprocess.Popen(
            cmd,
            cwd=str(REPO_ROOT),
            stdout=logf,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        try:
            rc = proc.wait(timeout=timeout_s)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except (ProcessLookupError, OSError):
                pass
            time.sleep(5)
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except (ProcessLookupError, OSError):
                pass
            return 124, str(log_path)
    return rc, str(log_path)


def _write_summary(todo_id: str, slug: str, rc: int, log_path: str) -> Path:
    DRAFTS_DIR.mkdir(parents=True, exist_ok=True)
    p = _summary_path(slug)
    target_dir = TARGETS_DIR / slug
    research_md = target_dir / "research.md"
    submission_draft = target_dir / "submission_draft_final.md"
    body_lines = [
        f"# Research loop summary — {todo_id} ({slug})",
        "",
        f"**Run completed**: {_now_iso()}",
        f"**dispatch_worktree --supervise rc**: {rc}",
        f"**Run log**: `{log_path}`",
        "",
        "## Status",
        "",
        "**Pending User Approval** — review artifacts below before any external action.",
        "",
        "## Artifacts on disk",
        "",
        f"- `targets/{slug}/research.md`: "
        + ("present" if research_md.exists() else "missing"),
        f"- `targets/{slug}/submission_draft_final.md`: "
        + ("present" if submission_draft.exists() else "missing"),
        "",
        "## Operator next steps",
        "",
        "1. Read `targets/" + slug + "/research.md` if present.",
        "2. Skim `submission_draft_final.md`.",
        "3. If OK → ship via the appropriate channel (gh comment / Apple Mail draft / forum).",
        "4. If needs more work → drop a note here and re-queue or escalate.",
        "",
        "**Reminder**: this loop never sends anything; user approval is the gate.",
    ]
    p.write_text("\n".join(body_lines) + "\n", encoding="utf-8")
    return p


def process_one(todo_id: str, slug: str, *, timeout_s: int) -> dict:
    """Claim → dispatch → write summary → mark board → release."""
    started = _now()
    if not claim(slug):
        return {"todo_id": todo_id, "slug": slug, "skipped": "already_claimed"}
    try:
        loop_log(f"claimed {todo_id} ({slug}); dispatching --supervise")
        rc, log_path = _spawn_supervise(todo_id, timeout_s)
        loop_log(f"{todo_id}: dispatch_worktree --supervise rc={rc} ({log_path})")
        summary_path = _write_summary(todo_id, slug, rc, log_path)
        marked = mark_pending_user_approval(
            todo_id,
            note=f"rc={rc}",
        )
        elapsed = _now() - started
        return {
            "todo_id": todo_id,
            "slug": slug,
            "rc": rc,
            "log": log_path,
            "summary": str(summary_path),
            "elapsed_s": round(elapsed, 1),
            "board_marked": marked,
        }
    finally:
        release(slug)


# ---------------------------------------------------------------------------
# selection policy
# ---------------------------------------------------------------------------


def select_next_target() -> Optional[tuple[str, str]]:
    """Return (todo_id, slug) of the next actionable target, or None."""
    todos = _parse_board_safe()
    if not todos:
        return None
    # Sort by topic_score desc then todo_id asc for determinism.
    def _key(item):
        _, t = item
        topic = getattr(t, "topic_score", None) or 0
        fit = getattr(t, "fit_score", None) or 0
        return (-(topic + fit), t.todo_id)

    for tid, todo in sorted(todos.items(), key=_key):
        status = getattr(todo, "status", "") or ""
        if _is_skipped(status):
            continue
        slug = todo.slug()
        if _claim_marker(slug).exists():
            continue
        if _has_recent_summary(slug, SUMMARY_COOLDOWN_HOURS):
            continue
        return tid, slug
    return None


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def _write_status(payload: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    try:
        RESEARCH_LOOP_STATUS.write_text(
            json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8"
        )
    except OSError as exc:
        loop_log(f"status write failed: {exc}")


def _install_signal_handlers(stop_flag: dict) -> None:
    def _handler(signum, frame):
        stop_flag["stop"] = True

    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            signal.signal(sig, _handler)
        except (OSError, ValueError):
            pass


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--loop", action="store_true",
                   help="run continuously, polling for next actionable target")
    p.add_argument("--once", action="store_true",
                   help="select one actionable target, run it, exit")
    p.add_argument("--todo-id", default="",
                   help="explicit T-NN to run (forces selection); use with --once")
    p.add_argument("--parallel", type=int, default=DEFAULT_PARALLEL,
                   help=f"max concurrent targets (default {DEFAULT_PARALLEL}; >1 not yet supported)")
    p.add_argument("--poll-interval", type=int, default=DEFAULT_POLL_INTERVAL,
                   help=f"seconds between polls when no target available (default {DEFAULT_POLL_INTERVAL})")
    p.add_argument("--target-timeout-s", type=int, default=DEFAULT_TARGET_TIMEOUT_S,
                   help=f"hard cap per target (default {DEFAULT_TARGET_TIMEOUT_S}s)")
    p.add_argument("--cleanup-only", action="store_true",
                   help="just sweep stale claims and exit")
    args = p.parse_args(argv)

    if args.cleanup_only:
        n = cleanup_stale_claims()
        print(f"released {n} stale claim(s)")
        return 0

    if not args.loop and not args.once:
        p.error("specify --loop or --once")

    stop_flag: dict = {"stop": False}
    _install_signal_handlers(stop_flag)

    loop_log(
        f"research_loop starting "
        f"(loop={args.loop} once={args.once} todo_id={args.todo_id or 'auto'} "
        f"parallel={args.parallel} timeout={args.target_timeout_s}s)"
    )

    if args.parallel > 1:
        loop_log("--parallel > 1 not yet supported, falling back to 1")

    iteration = 0
    while not stop_flag["stop"]:
        iteration += 1

        cleanup_stale_claims()

        # Pick target.
        if args.todo_id:
            todos = _parse_board_safe()
            todo = todos.get(args.todo_id)
            if todo is None:
                loop_log(f"--todo-id {args.todo_id} not found on board, exiting")
                return 1
            slug = todo.slug()
            if _is_skipped(getattr(todo, "status", "") or ""):
                loop_log(f"{args.todo_id} status indicates skip; exiting")
                return 1
            picked: Optional[tuple[str, str]] = (args.todo_id, slug)
        else:
            picked = select_next_target()

        if picked is None:
            loop_log(f"no actionable target this poll (iter={iteration})")
            _write_status({
                "iter": iteration,
                "last_poll": _now_iso(),
                "picked": None,
            })
            if args.once:
                return 0
            time.sleep(args.poll_interval)
            continue

        todo_id, slug = picked
        loop_log(f"iter={iteration} picked {todo_id} ({slug})")
        result = process_one(todo_id, slug, timeout_s=args.target_timeout_s)
        loop_log(f"{todo_id} result: {result}")
        _write_status({
            "iter": iteration,
            "last_completed": _now_iso(),
            "result": result,
        })

        if args.once:
            return 0

        # If the selection was forced via --todo-id, we still loop normally
        # in --loop mode to keep parity with auto-selection.
        if args.todo_id:
            args.todo_id = ""

    loop_log("research_loop exiting (stop signal)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
