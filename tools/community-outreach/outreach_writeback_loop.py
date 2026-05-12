#!/usr/bin/env python3
"""outreach_writeback_loop — Claude/Codex writeback backflow daemon.

Phase 2 of the operator-designed agent allocation:
  - codex / oracle / claude do the heavy thinking and drafting
  - the operator reviews each draft (gated_ready → user approval)
  - **this loop** writes the approved deliverable into the main paper
    using Claude with the /killo-golden skill when available, or Codex as an
    audited fallback when Claude is quota-limited/unavailable.

Invocation gate: a task must EXPLICITLY transition to status='writeback_pending'
before this loop will touch the main paper. The operator does that
manually — no auto-trigger off `gated_ready`. This preserves the
inbound-then-draft-then-approve workflow the operator memory pinned.

Per-task config (in task JSON):

  "backflow": {
    "target_paper_root": "theory/2026_golden_ratio_..._emergence",
    "target_section_hint": "appendix/<slug>",   # path or grep keyword
    "skill_args_extra": "<short note to add to /killo-golden $ARGUMENTS>"
  }

Stop with `touch tools/community-outreach/.outreach_stop` (shared with
supervisor) or SIGINT/SIGTERM.
"""

from __future__ import annotations

import argparse
import os
import shutil
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
WRITEBACK_CLAIMS_DIR = STATE_DIR / "writeback_claims"
WRITEBACK_LOG_DIR = STATE_DIR / "writeback_logs"
STOP_FILE = SCRIPT_DIR / ".outreach_stop"

DEFAULT_POLL_INTERVAL = 180
DEFAULT_CLAIM_STALE_HOURS = 6
DEFAULT_TIMEOUT_S = 7200  # 2h cap per writeback (claude + skill can think long)

CLAUDE_PATH = shutil.which("claude") or "/opt/homebrew/bin/claude"

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_task_spec import (  # noqa: E402
    TASK_QUEUE_DIR,
    TaskSpec,
    list_tasks,
    load_task,
    save_task,
)


# ---------------------------------------------------------------------------
# logging
# ---------------------------------------------------------------------------


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def writeback_log(msg: str) -> None:
    WRITEBACK_LOG_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {msg}"
    print(line, flush=True)
    with open(WRITEBACK_LOG_DIR / "writeback.log", "a", encoding="utf-8") as f:
        f.write(line + "\n")


# ---------------------------------------------------------------------------
# claim semantics (mirrors task_runner pattern, separate dir to avoid collision)
# ---------------------------------------------------------------------------


def _claim_dir(task_id: str) -> Path:
    return WRITEBACK_CLAIMS_DIR / task_id


def _claim_marker(task_id: str) -> Path:
    return _claim_dir(task_id) / ".in_progress"


def _claim_pid_file(task_id: str) -> Path:
    return _claim_dir(task_id) / ".pid"


def claim(task_id: str) -> bool:
    d = _claim_dir(task_id)
    d.mkdir(parents=True, exist_ok=True)
    marker = _claim_marker(task_id)
    if marker.exists():
        return False
    try:
        fd = os.open(str(marker), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        os.write(fd, f"claimed_at={_now_iso()}\npid={os.getpid()}\n".encode())
        os.close(fd)
    except FileExistsError:
        return False
    except OSError as exc:
        writeback_log(f"claim({task_id}) failed: {exc}")
        return False
    try:
        _claim_pid_file(task_id).write_text(str(os.getpid()), encoding="utf-8")
    except OSError:
        pass
    return True


def release(task_id: str) -> None:
    for p in (_claim_marker(task_id), _claim_pid_file(task_id)):
        try:
            p.unlink()
        except FileNotFoundError:
            pass


def _pid_alive(pid: int) -> bool:
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
        return True
    except (ProcessLookupError, OSError):
        return False


def cleanup_stale_claims(stale_hours: float = DEFAULT_CLAIM_STALE_HOURS) -> int:
    if not WRITEBACK_CLAIMS_DIR.exists():
        return 0
    released = 0
    cutoff = time.time() - stale_hours * 3600
    for d in WRITEBACK_CLAIMS_DIR.iterdir():
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
# claude + /killo-golden invocation
# ---------------------------------------------------------------------------


def _build_skill_args(task: TaskSpec) -> str:
    bf = (task.context or {}).get("backflow") or {}
    target_root = bf.get("target_paper_root") or (
        "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence"
    )
    section_hint = bf.get("target_section_hint") or ""
    extra = bf.get("skill_args_extra") or ""
    deliverable = task.deliverable_paths[0] if task.deliverable_paths else ""
    parts = [
        f"Write back the operator-approved deliverable from `{deliverable}`",
        f"into the main paper rooted at `{target_root}`.",
    ]
    if section_hint:
        parts.append(f"Target section hint: `{section_hint}`.")
    parts.append(
        "Read the deliverable in full, then locate the closest existing section "
        "where the material belongs. Integrate as continuous academic prose; "
        "do NOT introduce 'newly added' / 'supplement' prefixes; do NOT add "
        "time-stamps or change-log notes; do NOT exceed 600 lines per file "
        "(create a new sibling file if needed); do NOT auto-compile PDF."
    )
    if extra:
        parts.append(f"Operator note: {extra}")
    return " ".join(parts)


def _looks_like_claude_limit(text: str) -> bool:
    lower = (text or "").lower()
    return any(
        needle in lower
        for needle in (
            "hit your limit",
            "usage limit",
            "rate limit",
            "quota",
            "too many requests",
            "try again later",
            "resets ",
        )
    )


def _run_codex_writeback_fallback(task: TaskSpec, *, reason: str) -> tuple[bool, str]:
    if not task.deliverable_paths:
        return False, "task.deliverable_paths empty"
    deliverable_abs = (
        task.deliverable_paths[0]
        if Path(task.deliverable_paths[0]).is_absolute()
        else REPO_ROOT / task.deliverable_paths[0]
    )
    if not deliverable_abs.exists():
        return False, f"deliverable missing on disk: {task.deliverable_paths[0]}"
    try:
        from outreach_codex_track import codex_exec  # noqa: PLC0415
    except Exception as exc:
        return False, f"codex fallback import failed: {exc}"

    bf = (task.context or {}).get("backflow") or {}
    target_root = bf.get("target_paper_root") or (
        "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence"
    )
    section_hint = bf.get("target_section_hint") or ""
    extra = bf.get("skill_args_extra") or ""
    prompt = f"""You are Codex acting as the fallback writeback backend for the Omega outreach pipeline.

Claude /killo-golden is unavailable for this writeback, so perform the same writeback discipline directly.

Fallback reason: {reason}

Task id: {task.id}
Deliverable: {task.deliverable_paths[0]}
Target paper root: {target_root}
Target section hint: {section_hint or "(none)"}
Operator note: {extra or "(none)"}

Instructions:
- Read the deliverable in full before editing.
- Locate the closest existing section where the material belongs.
- Integrate as continuous academic prose; do not add visible patch traces, timestamps, changelog notes, or "newly added" / "supplement" prefixes.
- Do not overclaim. Preserve all caveats, proof/evidence limits, and operator constraints from the deliverable.
- Do not send email, post externally, push, or commit.
- Keep edits scoped to the target paper root unless the existing include structure requires a sibling file.
- Do not exceed 600 lines per edited file; create a new sibling file if needed and wire it into the local include structure only when necessary.
- At the end, report files changed and any verification you ran.
"""
    writeback_log(f"{task.id}: Claude unavailable; invoking Codex writeback fallback ({reason})")
    result = codex_exec(
        prompt,
        timeout=DEFAULT_TIMEOUT_S,
        log_tag=f"writeback_fallback_{task.id}",
    )
    if not result.ok:
        return False, f"codex fallback failed: {result.error or result.raw[:500]}"
    return True, f"writeback complete via codex fallback ({len(result.raw or '')} chars; reason={reason})"


def _run_writeback(task: TaskSpec) -> tuple[bool, str]:
    if not CLAUDE_PATH or not Path(CLAUDE_PATH).exists():
        return _run_codex_writeback_fallback(
            task,
            reason=f"claude CLI not found at {CLAUDE_PATH}",
        )
    if not task.deliverable_paths:
        return False, "task.deliverable_paths empty"
    deliverable_abs = (task.deliverable_paths[0]
                       if Path(task.deliverable_paths[0]).is_absolute()
                       else REPO_ROOT / task.deliverable_paths[0])
    if not deliverable_abs.exists():
        return False, f"deliverable missing on disk: {task.deliverable_paths[0]}"

    skill_args = _build_skill_args(task)
    # Slash command invocation: `claude -p "/killo-golden <args>"`. Skills
    # under .claude/skills/ are auto-discovered by the local claude CLI.
    prompt = f"/killo-golden {skill_args}"

    WRITEBACK_LOG_DIR.mkdir(parents=True, exist_ok=True)
    ts = _now_tag()
    prompt_log = WRITEBACK_LOG_DIR / f"{task.id}_{ts}.prompt.txt"
    stdout_log = WRITEBACK_LOG_DIR / f"{task.id}_{ts}.stdout.txt"
    stderr_log = WRITEBACK_LOG_DIR / f"{task.id}_{ts}.stderr.txt"
    prompt_log.write_text(prompt, encoding="utf-8")

    cmd = [CLAUDE_PATH, "-p", "--dangerously-skip-permissions"]
    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    writeback_log(f"{task.id}: invoking claude /killo-golden …")
    try:
        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, cwd=str(REPO_ROOT), env=env,
            encoding="utf-8", errors="replace", start_new_session=True,
        )
        try:
            out, err = proc.communicate(input=prompt, timeout=DEFAULT_TIMEOUT_S)
            rc = proc.returncode
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
            stdout_log.write_text("(killed on timeout)\n", encoding="utf-8")
            return _run_codex_writeback_fallback(
                task,
                reason=f"claude writeback timed out after {DEFAULT_TIMEOUT_S}s",
            )
    except Exception as exc:
        return _run_codex_writeback_fallback(task, reason=f"claude spawn failed: {exc}")

    stdout_log.write_text(out or "", encoding="utf-8")
    stderr_log.write_text(err or "", encoding="utf-8")
    if rc != 0:
        failure = "\n".join([out or "", err or ""])
        reason = "claude quota/limit" if _looks_like_claude_limit(failure) else f"claude rc={rc}"
        return _run_codex_writeback_fallback(task, reason=reason)
    body = (out or "").strip()
    if _looks_like_claude_limit(body):
        return _run_codex_writeback_fallback(task, reason="claude quota/limit")
    return True, f"writeback complete ({len(body)} chars stdout; logs={stdout_log.name})"


# ---------------------------------------------------------------------------
# orchestrator
# ---------------------------------------------------------------------------


def select_next() -> Optional[TaskSpec]:
    for t in sorted(list_tasks(), key=lambda x: x.last_run_iso or ""):
        if t.status != "writeback_pending":
            continue
        if _claim_marker(t.id).exists():
            continue
        if not t.deliverable_paths:
            continue
        return t
    return None


def process_one(task: TaskSpec) -> dict:
    if not claim(task.id):
        return {"task_id": task.id, "skipped": "already_claimed"}
    started = time.time()
    try:
        task.status = "writeback_in_progress"
        task.last_run_iso = _now_iso()
        save_task(task)
        ok, msg = _run_writeback(task)
        task.last_run_iso = _now_iso()
        if ok:
            task.status = "writeback_done"
            task.last_verdict = "writeback_pass"
            task.last_reason = msg
            save_task(task)
            writeback_log(f"{task.id}: writeback_done ({msg})")
            return {"task_id": task.id, "verdict": "pass", "elapsed_s": round(time.time() - started, 1)}
        # failure path
        task.retries += 1
        task.last_verdict = "writeback_fail"
        task.last_reason = msg
        if task.retries >= task.max_retries:
            task.status = "writeback_failed"
        else:
            task.status = "writeback_pending"  # retry next loop
        save_task(task)
        writeback_log(f"{task.id}: writeback_fail ({msg}); retries={task.retries} status={task.status}")
        return {"task_id": task.id, "verdict": "fail", "reason": msg, "status": task.status}
    finally:
        release(task.id)


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
    p.add_argument("--loop", action="store_true", help="continuous polling daemon")
    p.add_argument("--once", action="store_true", help="select one task, run it, exit")
    p.add_argument("--task-id", default="", help="explicit task id (use with --once)")
    p.add_argument("--poll-interval", type=int, default=DEFAULT_POLL_INTERVAL)
    p.add_argument("--cleanup-only", action="store_true",
                   help="sweep stale claims and exit")
    args = p.parse_args(argv)

    if args.cleanup_only:
        n = cleanup_stale_claims()
        print(f"released {n} stale writeback claim(s)")
        return 0

    if not args.loop and not args.once:
        p.error("specify --loop or --once")

    stop: dict = {"stop": False}
    _install_signal_handlers(stop)
    writeback_log(f"writeback_loop starting (loop={args.loop} once={args.once} task_id={args.task_id or 'auto'})")

    while not stop["stop"] and not STOP_FILE.exists():
        cleanup_stale_claims()

        picked: Optional[TaskSpec] = None
        if args.task_id:
            picked = load_task(args.task_id)
            if picked is None or picked.status != "writeback_pending":
                writeback_log(f"--task-id {args.task_id} not found or not in writeback_pending; exit")
                return 1
        else:
            picked = select_next()

        if picked is None:
            if args.once:
                return 0
            time.sleep(args.poll_interval)
            continue

        result = process_one(picked)
        writeback_log(f"result: {result}")
        if args.once:
            return 0
        if args.task_id:
            args.task_id = ""

    writeback_log("writeback_loop exiting")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
