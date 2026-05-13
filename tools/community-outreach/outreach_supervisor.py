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
  6. Git uploads are opt-in only: --auto-commit detects changes in
     OUTREACH_LOG.md / RESEARCH_BOARD.md only. Drafts and intermediate
     artifacts are never auto-committed.
  7. PI agent review: periodic Claude supervision via outreach_pi_agent.
     Claude is otherwise reserved for explicit writeback.

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
import re
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
WRITEBACK_LOOP_SCRIPT = SCRIPT_DIR / "outreach_writeback_loop.py"
ARXIV_WATCH = SCRIPT_DIR / "arxiv_watch.py"
LIT_STALENESS = SCRIPT_DIR / "lit_staleness.py"
INBOX_WATCHER = SCRIPT_DIR / "outreach_inbox_watcher.py"
BOARD_REFILL = SCRIPT_DIR / "outreach_board_refill.py"
CONTEXT_REFRESH = SCRIPT_DIR / "outreach_context_refresh.py"
X_OPENPROBLEM_WATCH = SCRIPT_DIR / "x_openproblem_watch.py"
PROFILE_JUDGE = SCRIPT_DIR / "outreach_profile_judge.py"
SCIENCE_GATE = SCRIPT_DIR / "outreach_science_gate.py"
IMPACT_GATE = SCRIPT_DIR / "outreach_impact_gate.py"
FRESHNESS_JUDGE = SCRIPT_DIR / "outreach_freshness_judge.py"
ORACLE_RECONCILE = SCRIPT_DIR / "outreach_oracle_reconcile.py"
REVIEW_QUEUE = SCRIPT_DIR / "outreach_review_queue.py"

DEFAULT_PARALLEL = 2
DEFAULT_POLL_INTERVAL = 300
DEFAULT_PI_REVIEW_HOURS = 6
DEFAULT_INBOX_WATCH_HOURS = 1
DEFAULT_ARXIV_WATCH_HOURS = 12
DEFAULT_LIT_STALENESS_HOURS = 24
DEFAULT_BOARD_REFILL_HOURS = 24
DEFAULT_CONTEXT_REFRESH_HOURS = 1
DEFAULT_X_OPENPROBLEM_WATCH_HOURS = 24
DEFAULT_PROFILE_JUDGE_HOURS = 24
DEFAULT_SCIENCE_GATE_HOURS = 1
DEFAULT_FRESHNESS_JUDGE_HOURS = 168
DEFAULT_LOCK_STALE_HOURS = 1
DEFAULT_INNER_RESTART_BACKOFF_S = 30
TAB_STUCK_THRESHOLD_S = 300
PREFLIGHT_REPAIR_COOLDOWN_S = 600
FRONTIER_HARNESS_COOLDOWN_S = 600
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


def oracle_idle() -> bool:
    s = server_status()
    if not s:
        return False
    return int(s.get("queue_length") or 0) == 0 and int(s.get("agents_busy") or 0) == 0


def oracle_has_capacity() -> bool:
    s = server_status()
    if not s:
        return False
    busy = int(s.get("agents_busy") or 0)
    queued = int(s.get("queue_length") or 0)
    max_agents = int(s.get("max_agents") or 1)
    if queued != 0 or busy >= max_agents:
        return False
    # A browser tab can still be generating a cancelled/abandoned task even
    # after the server queue is empty. Treat those tabs as occupying Oracle
    # capacity; otherwise background board-refill can steal the next available
    # ChatGPT tab while a high-priority research follow-up is waiting.
    for rec in (s.get("recent_agents") or {}).values():
        if not isinstance(rec, dict) or not rec.get("recent"):
            continue
        metrics = rec.get("metrics") if isinstance(rec.get("metrics"), dict) else {}
        generation = metrics.get("generation") if isinstance(metrics.get("generation"), dict) else {}
        phase = str(metrics.get("phase") or "")
        if generation.get("generating") or phase in {
            "clicking_send",
            "sent_waiting_for_generation",
            "waiting_for_prompt_input",
            "waiting_for_send_button",
            "prompt_entered",
            "send_button_not_ready",
        }:
            return False
    return True


def _process_running(pattern: str) -> bool:
    try:
        proc = subprocess.run(
            ["ps", "-axo", "command"],
            capture_output=True,
            text=True,
            timeout=5,
            check=False,
        )
    except Exception:
        return False
    return any(pattern in line for line in (proc.stdout or "").splitlines())


def _script_running(script_name: str) -> bool:
    return _process_running(f"tools/community-outreach/{script_name}") or _process_running(f"/{script_name}")


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


def stale_task_cleanup() -> tuple[int, int]:
    """Sweep stale task claims and recover orphan task JSON states."""
    try:
        import outreach_task_runner as task_runner  # noqa: PLC0415
    except ImportError:
        return 0, 0
    claims = 0
    states = 0
    try:
        claims = task_runner.cleanup_stale_claims()
    except Exception as exc:
        supervisor_log(f"stale_task_claim_cleanup error: {exc}")
    try:
        states = len(task_runner.cleanup_stale_in_progress_tasks())
    except Exception as exc:
        supervisor_log(f"stale_task_state_cleanup error: {exc}")
    return claims, states


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
        extra_args=["--parallel", str(parallel), "--oracle-refill-reserve", "1"],
    )


def spawn_task_runner() -> subprocess.Popen:
    return _spawn_inner(
        TASK_RUNNER_SCRIPT,
        log_name="inner_task_runner.log",
        label="task_runner",
        extra_args=[],
    )


def spawn_writeback_loop() -> subprocess.Popen:
    return _spawn_inner(
        WRITEBACK_LOOP_SCRIPT,
        log_name="inner_writeback.log",
        label="writeback_loop",
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


def _spawn_short_task(
    script: Path,
    label: str,
    extra_args: list[str] | None = None,
    *,
    timeout_s: int | None = None,
) -> None:
    if not script.exists():
        supervisor_log(f"{label}: {script.name} missing, skipping")
        return
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_path = SUPERVISOR_LOG_DIR / f"{label}_{_now_tag_safe()}.log"
    cmd = ["python3", str(script), *(extra_args or [])]
    if timeout_s is not None:
        runner = (
            "import subprocess,sys; "
            f"cmd={cmd!r}; "
            f"sys.exit(subprocess.run(cmd, timeout={int(timeout_s)}).returncode)"
        )
        cmd = ["python3", "-c", runner]
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
    _spawn_short_task(ARXIV_WATCH, "arxiv_watch", ["--since", "7d"], timeout_s=420)


def trigger_inbox_watcher() -> None:
    _spawn_short_task(INBOX_WATCHER, "inbox_watcher")


def trigger_lit_staleness() -> None:
    _spawn_short_task(LIT_STALENESS, "lit_staleness", timeout_s=360)


def trigger_board_refill() -> None:
    if _script_running("outreach_board_refill.py"):
        supervisor_log("board_refill: already running, skip duplicate trigger")
        return
    _spawn_short_task(BOARD_REFILL, "board_refill", ["--candidate-inbox", "--timeout-s", "3600"], timeout_s=3720)


def trigger_context_refresh() -> None:
    _spawn_short_task(CONTEXT_REFRESH, "context_refresh", ["--write"], timeout_s=90)


def trigger_x_openproblem_watch() -> None:
    _spawn_short_task(
        X_OPENPROBLEM_WATCH,
        "x_openproblem_watch",
        ["--write", "--budget-usd", "1.0"],
    )


def trigger_profile_judge() -> None:
    if _script_running("outreach_profile_judge.py"):
        supervisor_log("profile_judge: already running, skip duplicate trigger")
        return
    _spawn_short_task(
        PROFILE_JUDGE,
        "profile_judge",
        ["--generate-board-batch-with-codex", "--top", "4", "--min-score", "12"],
    )
    _spawn_short_task(
        PROFILE_JUDGE,
        "profile_judge_inbox",
        ["--graduate-inbox-with-codex", "--top", "2"],
    )


def trigger_science_gate() -> None:
    if _script_running("outreach_science_gate.py"):
        supervisor_log("science_gate: already running, skip duplicate trigger")
        return
    _spawn_short_task(
        SCIENCE_GATE,
        "science_gate",
        ["--write-ledger"],
        timeout_s=120,
    )


def trigger_impact_gate() -> None:
    if _script_running("outreach_impact_gate.py"):
        supervisor_log("impact_gate: already running, skip duplicate trigger")
        return
    _spawn_short_task(
        IMPACT_GATE,
        "impact_gate",
        ["--write-ledger"],
        timeout_s=120,
    )


def trigger_freshness_judge(*, retry_uncertain: bool = False, top: int = 2) -> None:
    if _script_running("outreach_freshness_judge.py"):
        supervisor_log("freshness_judge: already running, skip duplicate trigger")
        return
    if _script_running("outreach_board_refill.py"):
        supervisor_log("freshness_judge: skipped because board_refill is active")
        return
    if not oracle_idle():
        supervisor_log("freshness_judge: skipped because Oracle is busy or queued")
        return
    args = ["auto", "--top", str(top), "--timeout-s", "900"]
    if retry_uncertain:
        args.append("--retry-uncertain")
    _spawn_short_task(
        FRESHNESS_JUDGE,
        "freshness_judge",
        args,
        timeout_s=960,
    )


def trigger_oracle_reconcile() -> None:
    _spawn_short_task(
        ORACLE_RECONCILE,
        "oracle_reconcile",
        ["--freshness"],
        timeout_s=120,
    )


def run_oracle_reconcile_sync(*, include_deep: bool = False) -> dict:
    if not ORACLE_RECONCILE.exists():
        return {}
    combined: dict = {"freshness": {}, "deep": {}}
    try:
        proc = subprocess.run(
            ["python3", str(ORACLE_RECONCILE), "--freshness", "--json"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=120,
            check=False,
        )
    except Exception as exc:
        supervisor_log(f"oracle_reconcile: error {exc}")
        return {}
    if proc.returncode != 0:
        supervisor_log(f"oracle_reconcile: rc={proc.returncode} {(proc.stderr or proc.stdout)[:300]}")
    else:
        try:
            payload = json.loads(proc.stdout or "{}")
        except json.JSONDecodeError:
            supervisor_log(f"oracle_reconcile: invalid json {(proc.stdout or '')[:300]}")
            payload = {}
        written = payload.get("written") or []
        if written:
            supervisor_log(
                "oracle_reconcile: wrote "
                + ", ".join(f"{r.get('todo_id')}={r.get('verdict')}" for r in written)
            )
        combined["freshness"] = payload

    if not include_deep:
        return combined

    try:
        proc = subprocess.run(
            ["python3", str(ORACLE_RECONCILE), "--deep", "--json"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )
    except Exception as exc:
        supervisor_log(f"oracle_reconcile_deep: error {exc}")
        return combined
    try:
        payload = json.loads(proc.stdout or "{}")
    except json.JSONDecodeError:
        supervisor_log(f"oracle_reconcile_deep: invalid json {(proc.stdout or '')[:300]}")
        return combined
    if proc.returncode != 0:
        supervisor_log(f"oracle_reconcile_deep: rc={proc.returncode} {(proc.stderr or proc.stdout)[:300]}")
        return combined
    written = payload.get("written") or []
    if written:
        supervisor_log(
            "oracle_reconcile_deep: reconciled "
            + ", ".join(
                f"{r.get('todo_id')}:{Path(str(r.get('claim_packet') or '')).name}"
                for r in written
            )
        )
    combined["deep"] = payload
    return combined


def trigger_requeue_stale_ready() -> None:
    _spawn_short_task(
        REVIEW_QUEUE,
        "review_queue_waiting",
        ["--mark-waiting-external-reply"],
        timeout_s=120,
    )
    _spawn_short_task(
        REVIEW_QUEUE,
        "review_queue_requeue",
        ["--requeue-stale-ready"],
        timeout_s=120,
    )


def run_context_refresh_sync() -> bool:
    """Run a bounded targeted context refresh.

    Apple Mail can hang inside osascript. Context refresh is useful, but it is
    not allowed to block supervisor startup or research-loop spawning. Keep the
    synchronous version short; the periodic async trigger can retry later.
    """
    if not CONTEXT_REFRESH.exists():
        supervisor_log("context_refresh: script missing, skipping")
        return False
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_path = SUPERVISOR_LOG_DIR / f"context_refresh_{_now_tag_safe()}.log"
    try:
        with open(log_path, "ab") as logf:
            proc = subprocess.run(
                ["python3", str(CONTEXT_REFRESH), "--write"],
                cwd=str(REPO_ROOT),
                stdout=logf,
                stderr=subprocess.STDOUT,
                timeout=30,
                check=False,
            )
    except subprocess.TimeoutExpired:
        supervisor_log(f"context_refresh: sync timeout after 30s ({log_path.name}); continuing")
        return False
    supervisor_log(f"context_refresh: sync rc={proc.returncode} ({log_path.name})")
    return proc.returncode == 0


def _preflight_rows() -> list[dict]:
    try:
        from outreach_preflight import judge_board  # noqa: PLC0415
    except Exception as exc:
        supervisor_log(f"preflight_repair: import failed: {exc}")
        return []
    try:
        rows = judge_board()
    except Exception as exc:
        supervisor_log(f"preflight_repair: judge_board failed: {exc}")
        return []
    out: list[dict] = []
    for row in rows:
        out.append({
            "todo_id": row.todo_id,
            "slug": row.slug,
            "title": row.title,
            "verdict": row.verdict,
            "missing": list(row.missing or []),
            "score": int(row.score or 0),
        })
    return out


def _preflight_repair_actions(rows: list[dict]) -> dict:
    blocked = [r for r in rows if r.get("verdict") not in {"RUN", "DROP", "HANDOFF"}]
    actionable = [r for r in rows if r.get("verdict") == "RUN"]
    missing_blob = "\n".join(
        "\n".join(str(m) for m in r.get("missing") or []) for r in blocked
    ).lower()
    actions: list[str] = []
    if not rows:
        actions.append("board_refill")
    if not actionable:
        if "valid target-specific profile" in missing_blob or "science_contract" in missing_blob:
            actions.append("profile_judge")
        if "omega fit detail" in missing_blob or "numbered attack plan" in missing_blob or "precise statement" in missing_blob:
            actions.append("board_refill")
        if not actions:
            actions.append("board_refill")
    if blocked:
        actions.append("science_gate")
    return {
        "rows": len(rows),
        "actionable": len(actionable),
        "blocked": len(blocked),
        "actions": sorted(set(actions)),
        "top_blocked": [
            {
                "todo_id": r.get("todo_id"),
                "verdict": r.get("verdict"),
                "score": r.get("score"),
                "missing": (r.get("missing") or [])[:3],
            }
            for r in sorted(blocked, key=lambda x: (-int(x.get("score") or 0), str(x.get("todo_id"))))[:8]
        ],
    }


def run_preflight_repair_controller(state: dict) -> None:
    rows = _preflight_rows()
    plan = _preflight_repair_actions(rows)
    state["last_preflight_repair"] = {
        "checked_at": _now_iso(),
        **plan,
    }
    if plan["actionable"]:
        supervisor_log(f"preflight_repair: {plan['actionable']} actionable target(s), no repair trigger")
        return
    actions = plan.get("actions") or []
    if not actions:
        supervisor_log(
            f"preflight_repair: no actionable target and no inferred repair action; "
            f"blocked={plan['blocked']}"
        )
        return
    last = float(state.get("last_preflight_repair_trigger_ts") or 0.0)
    if _now() - last < PREFLIGHT_REPAIR_COOLDOWN_S:
        supervisor_log(
            "preflight_repair: cooldown active; "
            f"actions={','.join(actions)} blocked={plan['blocked']}"
        )
        return
    supervisor_log(
        "preflight_repair: no actionable target; "
        f"blocked={plan['blocked']} actions={','.join(actions)} "
        f"top={json.dumps(plan['top_blocked'][:3], ensure_ascii=False)}"
    )
    if "science_gate" in actions:
        trigger_science_gate()
    if "profile_judge" in actions:
        trigger_profile_judge()
    if "board_refill" in actions:
        trigger_board_refill()
    state["last_preflight_repair_trigger_ts"] = _now()


def _frontier_pool_snapshot() -> dict:
    rows = _preflight_rows()
    actionable = [r for r in rows if r.get("verdict") == "RUN"]
    profile_needed = [
        r for r in rows
        if r.get("verdict") in {"NEEDS_PROFILE", "NEEDS_BOARD_UPDATE"}
        and any(
            "profile" in str(m).lower() or "science_contract" in str(m).lower()
            for m in (r.get("missing") or [])
        )
    ]
    inbox_ready = 0
    inbox_invalid = 0
    try:
        from outreach_candidate_inbox import list_candidates  # noqa: PLC0415
        profileable_statuses = {
            "needs_profile_judge",
            "operator_requested_review",
            "long_horizon_review",
        }
        for row in list_candidates():
            if row.get("status") in profileable_statuses:
                inbox_ready += 1
            elif row.get("status") == "invalid":
                inbox_invalid += 1
    except Exception as exc:
        supervisor_log(f"frontier_harness: candidate inbox read failed: {exc}")
    return {
        "rows": len(rows),
        "actionable": actionable,
        "profile_needed": profile_needed,
        "inbox_ready": inbox_ready,
        "inbox_invalid": inbox_invalid,
    }


def _top_names(rows: list[dict], n: int = 4) -> str:
    names = [str(r.get("title") or r.get("slug") or r.get("todo_id")) for r in rows[:n]]
    return ", ".join(names) if names else "-"


def run_frontier_harness_controller(state: dict, *, low_water: int = 2) -> None:
    """BEDC-style low-water controller for autonomous math production.

    Priority order:
      1. If RUN targets exist, keep the research loop as the main worker.
      2. If candidate inbox has rows, graduate them to board/profile.
      3. If board targets need profile/science contracts, run profile judge.
      4. If the pool is below low-water, ask ChatGPT/Oracle for new targets.

    Freshness/currentness remains a risk/audit signal. It should not occupy
    the Oracle lane while the harness has no mathematical work in flight.
    """
    snap = _frontier_pool_snapshot()
    actionable = snap["actionable"]
    state["last_frontier_harness"] = {
        "checked_at": _now_iso(),
        "actionable_count": len(actionable),
        "actionable_names": [r.get("title") for r in actionable[:8]],
        "profile_needed_count": len(snap["profile_needed"]),
        "inbox_ready": snap["inbox_ready"],
        "inbox_invalid": snap["inbox_invalid"],
        "oracle_idle": oracle_idle(),
    }
    if len(actionable) >= low_water:
        supervisor_log(
            "frontier_harness: research pool ready; "
            f"{len(actionable)} RUN target(s): {_top_names(actionable)}"
        )
        if oracle_has_capacity() and not _script_running("outreach_board_refill.py"):
            last = float(state.get("last_frontier_refill_ts") or 0.0)
            if _now() - last >= 1800:
                supervisor_log(
                    "frontier_harness: spare Oracle lane available; running background board refill"
                )
                trigger_board_refill()
                state["last_frontier_refill_ts"] = _now()
        return
    if actionable:
        supervisor_log(
            "frontier_harness: research loop has RUN target(s), but pool is below low-water; "
            f"{len(actionable)}<{low_water}: {_top_names(actionable)}"
        )
        if snap["profile_needed"]:
            last = float(state.get("last_frontier_harness_trigger_ts") or 0.0)
            if _now() - last >= FRONTIER_HARNESS_COOLDOWN_S:
                supervisor_log(
                    "frontier_harness: also repairing profile/science contracts for "
                    + _top_names(snap["profile_needed"])
                )
                trigger_profile_judge()
                state["last_frontier_harness_trigger_ts"] = _now()
        if oracle_has_capacity() and not _script_running("outreach_board_refill.py"):
            supervisor_log("frontier_harness: spare Oracle capacity available; topping up candidate inbox")
            trigger_board_refill()
            state["last_frontier_harness_trigger_ts"] = _now()
        return

    last = float(state.get("last_frontier_harness_trigger_ts") or 0.0)
    if _now() - last < FRONTIER_HARNESS_COOLDOWN_S:
        supervisor_log(
            "frontier_harness: pool empty but cooldown active; "
            f"inbox_ready={snap['inbox_ready']} profile_needed={len(snap['profile_needed'])}"
        )
        return

    if snap["inbox_ready"] > 0:
        supervisor_log(
            f"frontier_harness: graduating {snap['inbox_ready']} candidate inbox row(s) via Codex"
        )
        trigger_profile_judge()
        state["last_frontier_harness_trigger_ts"] = _now()
        return

    if snap["profile_needed"]:
        supervisor_log(
            "frontier_harness: repairing board profile/science contracts for "
            + _top_names(snap["profile_needed"])
        )
        trigger_profile_judge()
        state["last_frontier_harness_trigger_ts"] = _now()
        return

    if _script_running("outreach_board_refill.py"):
        supervisor_log("frontier_harness: board_refill already active; waiting for candidates")
        return

    supervisor_log(
        f"frontier_harness: RUN pool below low-water ({len(actionable)}<{low_water}); "
        "asking Oracle/ChatGPT for new high-impact open-problem targets"
    )
    trigger_board_refill()
    state["last_frontier_harness_trigger_ts"] = _now()


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
            "context_refresh_hours",
            "x_openproblem_watch_hours",
            "profile_judge_hours",
            "science_gate_hours",
            "freshness_judge_hours",
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
        for slot in ("inner_research", "inner_task", "inner_writeback"):
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
    parser.add_argument("--context-refresh-hours", type=float, default=DEFAULT_CONTEXT_REFRESH_HOURS,
                        help="cooldown for targeted issue/mail context refresh")
    parser.add_argument("--x-openproblem-watch-hours", type=float, default=DEFAULT_X_OPENPROBLEM_WATCH_HOURS,
                        help="cooldown for budget-limited X open-problem signal collection")
    parser.add_argument("--profile-judge-hours", type=float, default=DEFAULT_PROFILE_JUDGE_HOURS,
                        help="cooldown for candidate inbox profile/deep judge graduation")
    parser.add_argument("--science-gate-hours", type=float, default=DEFAULT_SCIENCE_GATE_HOURS,
                        help="cooldown for writing science_gate.json ledgers")
    parser.add_argument("--freshness-judge-hours", type=float, default=DEFAULT_FRESHNESS_JUDGE_HOURS,
                        help="cooldown for targeted freshness/currentness judge")
    parser.add_argument("--no-freshness-judge", action="store_true",
                        help="disable opportunistic freshness/currentness judge; freshness remains a risk flag")
    parser.add_argument("--frontier-low-water", type=int, default=2,
                        help="minimum RUN research targets before Oracle board refill is triggered")
    parser.add_argument("--lock-stale-hours", type=float, default=DEFAULT_LOCK_STALE_HOURS)
    parser.add_argument("--inner-restart-backoff", type=int, default=DEFAULT_INNER_RESTART_BACKOFF_S)
    parser.add_argument("--auto-commit", action="store_true",
                        help="opt in to committing/pushing OUTREACH_LOG.md and RESEARCH_BOARD.md snapshots")
    parser.add_argument("--no-pi-review", action="store_true",
                        help="skip periodic Claude PI supervision")
    parser.add_argument("--no-inner", action="store_true",
                        help="do not spawn either inner daemon (research_loop + task_runner); only run short-task triggers")
    parser.add_argument("--no-research-loop", action="store_true",
                        help="skip the research_loop inner (drains RESEARCH_BOARD T-NN entries)")
    parser.add_argument("--no-task-runner", action="store_true",
                        help="skip the task_runner inner (drains outreach_state/task_queue/*.json)")
    parser.add_argument("--no-writeback-loop", action="store_true",
                        help="skip the writeback_loop inner (drains writeback_pending tasks; killo-golden skill)")
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
        f"auto_commit={'on' if args.auto_commit else 'off'} "
        f"inner={'off' if args.no_inner else 'on'} "
        f"server_spawn={'off' if args.no_server_spawn else 'on'})"
    )

    supervisor_state: dict = {
        "inner_research": None,
        "inner_task": None,
        "inner_writeback": None,
        "pi_review_hours": args.pi_review_hours,
        "arxiv_watch_hours": args.arxiv_watch_hours,
        "lit_staleness_hours": args.lit_staleness_hours,
        "inbox_watcher_hours": args.inbox_watch_hours,
        "board_refill_hours": args.board_refill_hours,
        "context_refresh_hours": args.context_refresh_hours,
        "x_openproblem_watch_hours": args.x_openproblem_watch_hours,
        "profile_judge_hours": args.profile_judge_hours,
        "science_gate_hours": args.science_gate_hours,
        "freshness_judge_hours": args.freshness_judge_hours,
    }

    last_pi_ts = 0.0
    last_inbox_ts = 0.0
    last_arxiv_ts = 0.0
    last_lit_ts = 0.0
    last_refill_ts = 0.0
    last_context_refresh_ts = 0.0
    last_x_watch_ts = 0.0
    last_profile_judge_ts = 0.0
    last_science_gate_ts = 0.0
    last_freshness_judge_ts = 0.0
    last_tab_alert_ts = 0.0
    last_research_exit_ts = 0.0
    last_task_exit_ts = 0.0
    last_writeback_exit_ts = 0.0

    try:
        while not STOP_FILE.exists():
            tick_started = _now()

            if not args.no_server_spawn:
                ensure_server()

            run_oracle_reconcile_sync(include_deep=False)

            cleanup_stale_lock(args.lock_stale_hours)
            cleaned = stale_research_cleanup()
            if cleaned:
                supervisor_log(f"cleaned {cleaned} stale research claims")
            task_claims, task_states = stale_task_cleanup()
            if task_claims or task_states:
                supervisor_log(
                    f"cleaned stale task state: claims={task_claims} "
                    f"in_progress_rows={task_states}"
                )

            if args.once and not args.no_inner:
                supervisor_log("once mode: skipping persistent inner daemons; short tasks only")
            if not args.no_inner and not args.once:
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
                # writeback_loop slot
                if not args.no_writeback_loop:
                    proc = supervisor_state.get("inner_writeback")
                    if proc is None or proc.poll() is not None:
                        if proc is not None:
                            rc = proc.poll()
                            since = _now() - last_writeback_exit_ts
                            if since < args.inner_restart_backoff:
                                pass
                            else:
                                supervisor_log(f"writeback_loop exited rc={rc}; respawning")
                                supervisor_state["inner_writeback"] = spawn_writeback_loop()
                                last_writeback_exit_ts = _now()
                        else:
                            supervisor_state["inner_writeback"] = spawn_writeback_loop()

            since_context_h = (_now() - last_context_refresh_ts) / 3600.0
            if args.once or since_context_h >= supervisor_state["context_refresh_hours"]:
                run_context_refresh_sync()
                trigger_requeue_stale_ready()
                last_context_refresh_ts = _now()

            since_inbox_h = (_now() - last_inbox_ts) / 3600.0
            if args.once or since_inbox_h >= supervisor_state["inbox_watcher_hours"]:
                trigger_inbox_watcher()
                last_inbox_ts = _now()

            since_arxiv_h = (_now() - last_arxiv_ts) / 3600.0
            if args.once or since_arxiv_h >= supervisor_state["arxiv_watch_hours"]:
                trigger_arxiv_watch()
                last_arxiv_ts = _now()

            since_x_h = (_now() - last_x_watch_ts) / 3600.0
            if args.once or since_x_h >= supervisor_state["x_openproblem_watch_hours"]:
                trigger_x_openproblem_watch()
                last_x_watch_ts = _now()

            since_profile_h = (_now() - last_profile_judge_ts) / 3600.0
            if args.once or since_profile_h >= supervisor_state["profile_judge_hours"]:
                trigger_profile_judge()
                last_profile_judge_ts = _now()

            since_science_h = (_now() - last_science_gate_ts) / 3600.0
            if args.once or since_science_h >= supervisor_state["science_gate_hours"]:
                trigger_science_gate()
                trigger_impact_gate()
                last_science_gate_ts = _now()

            since_freshness_h = (_now() - last_freshness_judge_ts) / 3600.0
            if (
                not args.no_freshness_judge
                and (args.once or since_freshness_h >= supervisor_state["freshness_judge_hours"])
            ):
                trigger_freshness_judge()
                last_freshness_judge_ts = _now()

            run_frontier_harness_controller(
                supervisor_state,
                low_water=max(0, int(args.frontier_low_water)),
            )
            run_preflight_repair_controller(supervisor_state)

            since_lit_h = (_now() - last_lit_ts) / 3600.0
            if args.once or since_lit_h >= supervisor_state["lit_staleness_hours"]:
                trigger_lit_staleness()
                last_lit_ts = _now()

            since_refill_h = (_now() - last_refill_ts) / 3600.0
            if args.once or since_refill_h >= supervisor_state["board_refill_hours"]:
                if oracle_has_capacity():
                    trigger_board_refill()
                    last_refill_ts = _now()
                else:
                    supervisor_log("board_refill: deferred because Oracle has no spare browser capacity")

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

            if args.auto_commit:
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
                            elif action == "run_profile_judge":
                                last_profile_judge_ts = _now()
                            elif action == "run_science_gate":
                                last_science_gate_ts = _now()
                            elif action == "run_freshness_judge":
                                last_freshness_judge_ts = _now()

            if args.once:
                break

            elapsed = _now() - tick_started
            time.sleep(max(5.0, args.poll_interval - elapsed))

    except KeyboardInterrupt:
        supervisor_log("supervisor interrupted")
    finally:
        for slot in ("inner_research", "inner_task", "inner_writeback"):
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
