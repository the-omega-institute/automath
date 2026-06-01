#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Cross-platform supervisor for the paper publication pipeline.

This is the outer loop that keeps `oracle_pipeline.py` alive across paper
splits, journal-fit cycles, referee revisions, and final back-flow. The
pattern is adapted from:

  * tools/bedc-deep/supervisor.py (the-omega-institute/newmath@bedc-claim-packet-pipeline)
  * tools/community-outreach/outreach_supervisor.py (origin/openproblem-target)

with two notable departures:

  1. Windows compatibility is a hard requirement. POSIX-only primitives
     (os.killpg, signal.SIGTERM, start_new_session, osascript) are
     replaced with cross-platform equivalents (proc.terminate/kill,
     CREATE_NEW_PROCESS_GROUP on Windows, structured logs instead of
     desktop notifications).

  2. The "inner loop" is `oracle_pipeline.py` itself. Each tick the
     supervisor checks whether oracle_pipeline has a paper to advance,
     spawns it, and when it exits picks the next paper. Crashes get a
     backoff before respawn.

Responsibilities:

  1. Server health: ensure oracle_server.py is running on :8765 (the
     ChatGPT Pro browser bridge). Auto-respawn if dead.
  2. Inner loop manager: spawn oracle_pipeline.py for the highest-priority
     paper not yet at DONE; restart on crash with backoff.
  3. Tab health alert: log a warning when oracle_server reports
     queue_waiting_for_browser_agent for longer than 5 minutes (means
     ChatGPT tabs are not ACTIVE).
  4. Auto-commit: detect changes in papers/publication/**/*.tex,
     PIPELINE.md, and pipeline_state/*.json; commit and push to the
     supervisor branch.
  5. Soft halt: stop file (.pipeline_supervisor.stop) and SIGINT both
     drain the inner cleanly.

Stop the supervisor by creating tools/chatgpt-oracle/.pipeline_supervisor.stop
or sending Ctrl+C. On exit the inner is terminated cleanly.

Usage examples:

    # Run forever, drive whichever paper is next:
    python tools/chatgpt-oracle/pipeline_supervisor.py

    # One tick (good for cron or smoke tests):
    python tools/chatgpt-oracle/pipeline_supervisor.py --once

    # Drive a specific paper only:
    python tools/chatgpt-oracle/pipeline_supervisor.py --paper papers/publication/2026_xxx
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
from typing import Any

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")
except (AttributeError, OSError):
    pass

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent

ORACLE_SERVER_URL = "http://localhost:8765"
ORACLE_SERVER_SCRIPT = SCRIPT_DIR / "oracle_server.py"
ORACLE_PIPELINE_SCRIPT = SCRIPT_DIR / "oracle_pipeline.py"
PIPELINE_STATE_DIR = SCRIPT_DIR / "pipeline_state"

PUBLICATION_DIR = REPO_ROOT / "papers" / "publication"
SUPERVISOR_LOG_DIR = SCRIPT_DIR / "supervisor_logs"
STOP_FILE = SCRIPT_DIR / ".pipeline_supervisor.stop"
PID_FILE = SCRIPT_DIR / ".pipeline_supervisor.pid"
SERVER_RESTART_FILE = SCRIPT_DIR / ".server.restart"
INNER_RESTART_FILE = SCRIPT_DIR / ".inner.restart"
SUPERVISOR_BRANCH_DEFAULT = "dev-automation-integration"

DEFAULT_POLL_INTERVAL_S = 120
DEFAULT_INNER_RESTART_BACKOFF_S = 30
DEFAULT_AUTO_COMMIT_COOLDOWN_S = 600
TAB_STUCK_THRESHOLD_S = 300
TAB_ALERT_DEBOUNCE_S = 600
# Agent has held one task this long without progress → almost certainly
# the browser tab died or got navigated away. Server's hard cleanup is
# at TASK_TIMEOUT (4h); we want to surface much earlier.
AGENT_STUCK_THRESHOLD_S = 30 * 60        # 30 minutes
# Any queued task waiting this long even with at least one busy agent →
# real backlog (e.g. agent is processing a different task forever).
# Independent of TAB_STUCK_THRESHOLD_S which only fires on zero-agent state.
QUEUE_AGED_THRESHOLD_S = 60 * 60         # 1 hour
SERVER_BOOT_GRACE_S = 4

# Log surfacer: each tick scans tracked log files (inner.log,
# oracle_server.log, pi_review log) for high-signal lines and echoes
# them to supervisor.log so the operator's monitor catches them without
# tailing each child log directly. Tracks per-file byte offsets so each
# line is reported at most once per supervisor run.
INNER_LOG_PATH = SCRIPT_DIR / "supervisor_logs" / "inner.log"
ORACLE_SERVER_LOG_PATH = SCRIPT_DIR / "supervisor_logs" / "oracle_server.log"
SURFACED_LOGS = [
    ("inner", INNER_LOG_PATH),
    ("server", ORACLE_SERVER_LOG_PATH),
]
INNER_LOG_ALERT_PATTERNS = re.compile(
    r"\[(ERROR|CRITICAL)\]"
    r"|Claude (CLI )?unavailable"
    r"|out of extra usage"
    r"|Codex stderr:"
    r"|Stage [A-D] (blocked|failed)"
    r"|FAILED — Stage"
    r"|max .* rounds exhausted"
    r"|compile failed"
    r"|push failed"
    r"|aborted"
    r"|UnicodeEncodeError"
    r"|UnicodeDecodeError"
    r"|Traceback \(most recent"
    r"|charmap\.cp1252"
    r"|404 Not Found"
    r"|500 Internal"
    r"|Connection refused"
    r"|Address already in use",
    re.IGNORECASE,
)
INNER_LOG_MAX_LINES_PER_TICK = 20

# Aggressive remediation thresholds: after this many seconds, supervisor
# itself cancels a stuck real task without waiting for PI's 6h cycle.
# Below this we still log info: but don't act.
REAL_TASK_AUTO_CANCEL_S = 2 * 3600       # 2 hours

# Refill is a fallback producer: triggered only when the existing backlog
# is fully DONE. Default cooldown is intentionally long (7 days) — the
# operator's priority is finishing the existing splits, not generating new
# ones.
DEFAULT_REFILL_COOLDOWN_HOURS = 24 * 7
REFILL_SCRIPT = SCRIPT_DIR / "paper_refill.py"
REFILL_QUEUE_PATH = REPO_ROOT / "papers" / "publication" / "_refill_queue.json"

# PI review (joint codex + claude judgment layer) — periodic sanity check, not
# a critical-path gate. Default cooldown is long enough that codex/claude
# tokens remain a small fraction of total pipeline cost.
DEFAULT_PI_REVIEW_HOURS = 6
PI_REVIEW_SCRIPT = SCRIPT_DIR / "pi_review.py"
PI_REVIEW_LOG = SCRIPT_DIR / "supervisor_logs" / "pi_review.log"

IS_WINDOWS = sys.platform == "win32"


# ---------------------------------------------------------------------------
# logging / time helpers
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
    try:
        with open(SUPERVISOR_LOG_DIR / "supervisor.log", "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except OSError as exc:
        print(f"[{_now_iso()}] WARN: failed to append supervisor log: {exc}", flush=True)


def desktop_notify(title: str, body: str) -> None:
    """Best-effort cross-platform notification.

    macOS: osascript. Windows: log only (toast notifications need extra
    deps). Linux: log only. Always also writes to supervisor.log so an
    operator can scrape state. Prefix is `WARN:` so existing monitor
    grep patterns (case-insensitive `warn:`) catch it.
    """
    supervisor_log(f"WARN: {title} — {body}")
    if sys.platform == "darwin":
        safe_title = title.replace('"', '\\"')
        safe_body = body.replace('"', '\\"')
        script = f'display notification "{safe_body}" with title "{safe_title}"'
        try:
            subprocess.run(
                ["osascript", "-e", script],
                timeout=5, check=False,
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            )
        except Exception:
            pass


# ---------------------------------------------------------------------------
# subprocess helpers — Windows compatible
# ---------------------------------------------------------------------------


def command_failure_summary(proc: subprocess.CompletedProcess,
                            *, max_chars: int = 500) -> str:
    output = " ".join(
        ((proc.stderr or "") + " " + (proc.stdout or "")).split()
    )
    if len(output) > max_chars:
        output = output[: max_chars - 3].rstrip() + "..."
    return f"rc={proc.returncode}" + (f"; {output}" if output else "")


def _detached_popen_kwargs() -> dict:
    """Return Popen kwargs that detach the child from this process group.

    On POSIX we want start_new_session so SIGINT to the supervisor does
    not kill the child immediately; supervisor explicitly calls
    proc.terminate() / proc.kill() instead.

    On Windows we use CREATE_NEW_PROCESS_GROUP so we can send Ctrl-Break
    if needed and still call proc.terminate().
    """
    if IS_WINDOWS:
        flags = 0
        flags |= getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0)
        return {"creationflags": flags}
    return {"start_new_session": True}


def _terminate(proc: subprocess.Popen, *, grace_seconds: int = 30) -> None:
    """Terminate a child process portably.

    SIGTERM on POSIX, TerminateProcess on Windows; escalate to kill if
    the child does not exit within grace_seconds.
    """
    if proc.poll() is not None:
        return
    try:
        proc.terminate()
        supervisor_log(f"sent terminate to inner pid={proc.pid}")
    except (ProcessLookupError, OSError) as exc:
        supervisor_log(f"terminate failed pid={proc.pid}: {exc}")
        return
    try:
        proc.wait(timeout=grace_seconds)
    except subprocess.TimeoutExpired:
        try:
            proc.kill()
            supervisor_log(f"escalated to kill on inner pid={proc.pid}")
        except (ProcessLookupError, OSError):
            pass


def _python() -> str:
    return sys.executable or ("python" if IS_WINDOWS else "python3")


def _subprocess_env() -> dict[str, str]:
    env = os.environ.copy()
    env.setdefault("PYTHONIOENCODING", "utf-8")
    env.setdefault("PYTHONUTF8", "1")
    env.setdefault("ORACLE_MAX_AGENTS", "5")
    return env


def process_alive(pid: int | None) -> bool:
    if not pid:
        return False
    if IS_WINDOWS:
        proc = subprocess.run(
            [
                "powershell",
                "-NoProfile",
                "-Command",
                f"Get-Process -Id {pid} -ErrorAction SilentlyContinue | Select-Object -First 1",
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=5,
            check=False,
        )
        return proc.returncode == 0 and bool((proc.stdout or "").strip())
    try:
        os.kill(pid, 0)
    except OSError:
        return False
    return True


def read_pid_record(path: Path | None = None) -> dict[str, Any]:
    if path is None:
        path = PID_FILE
    try:
        raw = path.read_text(encoding="utf-8").strip()
    except OSError:
        return {"pid": None, "started_ts": None, "script": ""}
    if not raw:
        return {"pid": None, "started_ts": None, "script": ""}
    if raw.startswith("{"):
        try:
            data = json.loads(raw)
        except json.JSONDecodeError:
            return {"pid": None, "started_ts": None, "script": ""}
        try:
            pid = int(data.get("pid") or 0)
        except (TypeError, ValueError):
            pid = 0
        try:
            started_ts = float(data["started_ts"]) if data.get("started_ts") is not None else None
        except (TypeError, ValueError):
            started_ts = None
        return {
            "pid": pid if pid > 0 else None,
            "started_ts": started_ts,
            "script": str(data.get("script") or ""),
        }
    try:
        pid = int(raw)
    except ValueError:
        pid = 0
    return {"pid": pid if pid > 0 else None, "started_ts": None, "script": ""}


def write_pid_record(started_ts: float, path: Path | None = None) -> None:
    if path is None:
        path = PID_FILE
    path.write_text(
        json.dumps(
            {
                "pid": os.getpid(),
                "started_ts": started_ts,
                "script": str(Path(__file__).name),
            },
            ensure_ascii=True,
            sort_keys=True,
        ) + "\n",
        encoding="utf-8",
    )


def claim_supervisor_singleton(started_ts: float) -> bool:
    record = read_pid_record()
    existing_pid = record.get("pid")
    script_name = str(record.get("script") or "")
    same_supervisor_script = not script_name or script_name == Path(__file__).name
    if (
        existing_pid
        and existing_pid != os.getpid()
        and same_supervisor_script
        and process_alive(existing_pid)
    ):
        supervisor_log(
            f"supervisor already running pid={existing_pid}; exiting without starting duplicate"
        )
        return False
    try:
        write_pid_record(started_ts)
    except OSError as exc:
        supervisor_log(f"WARN: failed to write supervisor pid file: {exc}")
    return True


def cleanup_supervisor_pid() -> None:
    record = read_pid_record()
    if record.get("pid") == os.getpid():
        try:
            PID_FILE.unlink()
        except OSError:
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
    return server_status(timeout).get("port") == 8765


def oracle_work_in_flight(status: dict[str, Any] | None = None) -> bool:
    """Return True when restarting inner would orphan active Oracle work."""
    s = status if status is not None else server_status()
    try:
        queue_length = int(s.get("queue_length") or 0)
    except (TypeError, ValueError):
        queue_length = 0
    try:
        agents_busy = int(s.get("agents_busy") or 0)
    except (TypeError, ValueError):
        agents_busy = 0
    queued_tasks = s.get("queued_tasks") or []
    queued = s.get("queued") or []
    return queue_length > 0 or agents_busy > 0 or bool(queued_tasks) or bool(queued)


def ensure_server() -> subprocess.Popen | None:
    """Spawn oracle_server.py if dead. Returns the Popen handle, or None on failure / already-up.

    Note: when the server was started outside of this supervisor (e.g. the
    operator launched it manually), we cannot kill it via Popen. P1's
    .server.restart relies on supervisor having spawned the server itself —
    if the operator started the server externally and wants to restart it,
    they should kill that process first, then drop the .server.restart
    flag (or just let supervisor.ensure_server respawn).
    """
    if server_alive():
        return None
    if not ORACLE_SERVER_SCRIPT.exists():
        supervisor_log(
            f"oracle_server: {ORACLE_SERVER_SCRIPT.name} missing — cannot auto-spawn"
        )
        return None
    supervisor_log("server not responding; spawning oracle_server.py")
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    server_log = open(SUPERVISOR_LOG_DIR / "oracle_server.log", "ab")
    server_log.write(f"\n=== server spawn at {_now_iso()} ===\n".encode())
    server_log.flush()
    try:
        proc = subprocess.Popen(
            [_python(), str(ORACLE_SERVER_SCRIPT)],
            cwd=str(REPO_ROOT),
            stdout=server_log,
            stderr=subprocess.STDOUT,
            env=_subprocess_env(),
            **_detached_popen_kwargs(),
        )
    except Exception as exc:
        supervisor_log(f"oracle_server spawn failed: {exc}")
        return None
    time.sleep(SERVER_BOOT_GRACE_S)
    if not server_alive():
        supervisor_log("server still not responding after spawn; check manually")
        return None
    supervisor_log(f"server spawned pid={proc.pid}")
    return proc


def server_source_sha() -> str:
    """Read /status.source_sha (running server's source hash)."""
    return server_status().get("source_sha", "") or ""


def disk_source_sha(path: Path) -> str:
    import hashlib
    try:
        return hashlib.sha1(path.read_bytes()).hexdigest()[:12]
    except OSError:
        return ""


def maybe_log_supervisor_drift(*, running_sha: str,
                               last_alert_ts: float) -> float:
    disk_sha = disk_source_sha(Path(__file__))
    if (
        running_sha
        and disk_sha
        and running_sha != disk_sha
        and _now() - last_alert_ts > 1800
    ):
        supervisor_log(
            f"DRIFT: pipeline_supervisor.py on disk (sha={disk_sha}) differs "
            f"from running supervisor (sha={running_sha}); restart supervisor "
            "to apply."
        )
        return _now()
    return last_alert_ts


def queue_stuck_too_long(threshold_seconds: int) -> bool:
    s = server_status()
    if s.get("diagnosis") != "queue_waiting_for_browser_agent":
        return False
    queued = s.get("queued_tasks") or []
    return any((t.get("age_seconds") or 0) > threshold_seconds for t in queued)


def stuck_agents(threshold_seconds: int) -> list[dict]:
    """Return agents that have held a single task longer than threshold."""
    s = server_status()
    out: list[dict] = []
    for aid, info in (s.get("agents") or {}).items():
        elapsed = info.get("elapsed") or 0
        if elapsed > threshold_seconds:
            out.append({
                "agent_id": aid,
                "task_id": info.get("task_id", "?"),
                "elapsed": elapsed,
            })
    return out


def aged_queued_tasks(threshold_seconds: int) -> list[dict]:
    """Return queued tasks waiting longer than threshold (regardless of diagnosis)."""
    s = server_status()
    out: list[dict] = []
    for t in s.get("queued_tasks") or []:
        age = t.get("age_seconds") or 0
        if age > threshold_seconds:
            out.append({
                "task_id": t.get("task_id", "?"),
                "age_seconds": age,
                "conversation_id": t.get("conversation_id", ""),
            })
    return out


def cancel_task(task_id: str, reason: str = "supervisor_auto") -> bool:
    """POST /cancel for a task_id. Used by supervisor self-heal + PI callbacks."""
    try:
        req = urllib.request.Request(
            f"{ORACLE_SERVER_URL}/cancel",
            data=json.dumps({"task_id": task_id, "reason": reason}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        urllib.request.urlopen(req, timeout=10)
        return True
    except Exception as exc:
        supervisor_log(f"cancel_task({task_id}) failed: {exc}")
        return False


def auto_heal_disposable_stuck(threshold_seconds: int = 300) -> int:
    """Cancel disposable tasks (smoke/test/retry) stuck on an agent > N seconds.

    Called every tick. Self-healing — does not require operator or PI
    judgment because disposable tasks have no operational value.
    """
    healed = 0
    for stuck in stuck_agents(threshold_seconds):
        tid = stuck.get("task_id", "")
        if tid.startswith(("smoke", "test_", "retry_")):
            if cancel_task(tid, reason="auto_heal_disposable_stuck"):
                supervisor_log(
                    f"auto-action: cancelled disposable {tid} stuck on "
                    f"{stuck['agent_id']} for {stuck['elapsed']}s"
                )
                healed += 1
    return healed


_log_offsets: dict[str, int] = {}


def surface_log_alerts() -> int:
    """Scan each tracked log file's tail since last call.

    Echoes high-signal lines to supervisor.log so the operator's
    monitor catches them. Tracks per-file byte offsets so each line is
    reported at most once. Watches both inner.log (paper pipeline) and
    oracle_server.log (bridge service); the latter caught the recent
    Unicode crash that the inner-only surfacer had missed.
    """
    total_surfaced = 0
    for tag, path in SURFACED_LOGS:
        if not path.exists():
            continue
        try:
            size = path.stat().st_size
        except OSError:
            continue
        if tag not in _log_offsets:
            _log_offsets[tag] = size
            continue
        offset = _log_offsets.get(tag, 0)
        if size < offset:  # rotated / truncated
            offset = 0
        if size == offset:
            continue
        per_file = 0
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as fh:
                fh.seek(offset)
                for line in fh:
                    if per_file < INNER_LOG_MAX_LINES_PER_TICK:
                        if INNER_LOG_ALERT_PATTERNS.search(line):
                            cleaned = line.rstrip("\r\n")
                            if len(cleaned) > 320:
                                cleaned = cleaned[:317] + "..."
                            supervisor_log(f"{tag}: {cleaned}")
                            per_file += 1
                _log_offsets[tag] = fh.tell()
        except OSError as exc:
            supervisor_log(f"{path.name} surface scan failed: {exc}")
        total_surfaced += per_file
    return total_surfaced


# Backward-compat shim: pi_review and tests may still reach for the
# old name.
surface_inner_log_alerts = surface_log_alerts


def auto_cancel_long_stuck_real_tasks(threshold_seconds: int = REAL_TASK_AUTO_CANCEL_S) -> int:
    """Cancel real review tasks stuck on a single agent >threshold.

    Disposable tasks are handled separately by auto_heal_disposable_stuck.
    This is an aggressive last-resort remediation: a 2h+ stuck task on
    an agent almost always means the browser tab died silently. Cancelling
    frees the agent slot so other queued work can dispatch immediately,
    instead of waiting for the 4h server-side TASK_TIMEOUT.

    Cancelled real tasks reappear in the inner pool's normal flow because
    Stage B / C re-emit when their oracle wait times out internally.
    """
    cancelled = 0
    for stuck in stuck_agents(threshold_seconds):
        tid = stuck.get("task_id", "")
        if tid.startswith(("smoke", "test_", "retry_")):
            continue  # disposable handled elsewhere
        if cancel_task(tid, reason=f"auto_cancel_long_stuck_{stuck['elapsed']}s"):
            supervisor_log(
                f"auto-action: cancelled real task {tid[:50]} stuck on "
                f"{stuck['agent_id']} for {stuck['elapsed']}s — agent slot freed"
            )
            cancelled += 1
    return cancelled


# ---------------------------------------------------------------------------
# paper selection
# ---------------------------------------------------------------------------


_DONE_STAGE_RE = re.compile(r"(DONE|P7|D-DONE|publication_ready|submitted)", re.IGNORECASE)


def _read_pipeline_state(paper_dir: Path) -> dict[str, Any]:
    state_file = PIPELINE_STATE_DIR / f"{paper_dir.name}.json"
    if state_file.exists():
        try:
            return json.loads(state_file.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            return {}
    return {}


def _is_done(paper_dir: Path) -> bool:
    state = _read_pipeline_state(paper_dir)
    if state.get("current_stage") in {"DONE", "D-DONE"}:
        return True
    if str(state.get("status", "")).lower() in {"done", "publication_ready", "submitted"}:
        return True
    pipeline_md = paper_dir / "PIPELINE.md"
    if pipeline_md.exists():
        try:
            head = pipeline_md.read_text(encoding="utf-8", errors="ignore")[:4096]
        except OSError:
            head = ""
        if _DONE_STAGE_RE.search(head):
            return True
    return False


def _has_main_tex(paper_dir: Path) -> bool:
    return (paper_dir / "main.tex").exists()


def _paper_priority_key(paper_dir: Path) -> tuple[int, float, str]:
    """Sort key: prefer in-progress, then most-recently-touched, then name."""
    state = _read_pipeline_state(paper_dir)
    in_progress = 0 if state.get("current_stage") in {"A", "B", "C", "D"} else 1
    state_path = PIPELINE_STATE_DIR / f"{paper_dir.name}.json"
    mtime = state_path.stat().st_mtime if state_path.exists() else 0.0
    return (in_progress, -mtime, paper_dir.name)


_last_discovery_summary: dict[str, Any] = {}


def _recoverable_stage_a_block_from_status(status: str) -> bool:
    s = status.lower()
    if "a-blocked" not in s and "stage a blocked" not in s:
        return False
    hard_markers = (
        "overlap deferred",
        "needs_human_resolution",
        "human_decision",
        "overlap needs",
        "overlap with earlier submitted",
        "earlier submitted/current",
        "prior submitted sibling",
        "submitted sibling feedback",
        "canonical route before advancing",
        "wait for prior",
        "duplicate of canonical",
        "parked",
        "oracle escalation park",
        "legacy archive",
    )
    if any(marker in s for marker in hard_markers):
        return False
    recoverable_markers = (
        "a2 fake extension",
        "fake extension",
        "manual theorem-deepening",
        "max stage a rounds exhausted",
        "max stage a theoremization rounds exhausted",
        "final audit real block",
        "final audit unclear failure",
        "final audit failed",
        "pre-restart stale-round path",
        "manual-review before any rerun",
        "manual-review",
        "codex ceiling",
    )
    if any(marker in s for marker in recoverable_markers):
        return True
    return "a-blocked" in s or "stage a blocked" in s


def _paper_name_from_skipped_status(line: str) -> str:
    stripped = line.strip()
    if not stripped:
        return ""
    if stripped.startswith("`"):
        end = stripped.find("`", 1)
        return stripped[1:end] if end > 1 else ""
    return stripped.split(":", 1)[0].strip()


def recoverable_stage_a_blocked_papers(summary: dict[str, Any]) -> list[str]:
    papers: list[str] = []
    for line in summary.get("skipped_status", []) or []:
        text = str(line)
        if _recoverable_stage_a_block_from_status(text):
            name = _paper_name_from_skipped_status(text)
            if name:
                papers.append(name)
    return sorted(set(papers))


def watchdog_wake_recoverable_stage_a_blocks(summary: dict[str, Any]) -> int:
    """Wake inner scheduling when Codex-ceiling Stage A blocks are found.

    This does not cancel or kill running work.  It drops the same soft restart
    signal operators already use so the next safe supervisor tick re-runs
    discovery with the updated recoverable-block gate.
    """
    papers = recoverable_stage_a_blocked_papers(summary)
    if not papers:
        return 0
    try:
        INNER_RESTART_FILE.write_text(
            "recoverable Stage A block watchdog\n"
            + "\n".join(papers)
            + "\n",
            encoding="utf-8",
        )
        supervisor_log(
            f"watchdog: recoverable Stage A block(s) need Oracle escalation: "
            f"{', '.join(papers[:5])}"
            + (" ..." if len(papers) > 5 else "")
        )
    except OSError as exc:
        supervisor_log(f"WARN: failed to write {INNER_RESTART_FILE.name}: {exc}")
    return len(papers)


def format_discovery_summary(summary: dict[str, Any]) -> str:
    return (
        f"diagnosis={summary.get('diagnosis', 'unknown')}; "
        f"candidates={summary.get('candidate_count', 0)}; "
        f"runnable={summary.get('runnable_count', 0)}; "
        f"status_skipped={summary.get('skipped_status_count', 0)}; "
        f"done_skipped={summary.get('skipped_done_count', 0)}; "
        "unregistered_skipped="
        f"{summary.get('skipped_unregistered_count', 0)}; "
        "assignment_skipped="
        f"{summary.get('skipped_assignment_count', 0)}"
    )


def _pipeline_discovery_summary(only: list[str] | None = None) -> dict[str, Any]:
    code = (
        "import json, sys; "
        f"sys.path.insert(0, {str(SCRIPT_DIR)!r}); "
        "import oracle_pipeline; "
        f"paper_dirs = {only!r}; "
        "summary = oracle_pipeline.discover_paper_summary("
        "paper_dirs, respect_assignment=False, log=False); "
        "print(json.dumps(summary, ensure_ascii=True))"
    )
    proc = subprocess.run(
        [_python(), "-c", code],
        cwd=str(REPO_ROOT),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=30,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(command_failure_summary(proc))
    return json.loads(proc.stdout)


def discover_runnable_papers(only: list[str] | None = None) -> list[Path]:
    global _last_discovery_summary
    try:
        summary = _pipeline_discovery_summary(only)
        _last_discovery_summary = summary
        candidates = [Path(p) for p in summary.get("papers", [])]
        candidates = [p for p in candidates if _has_main_tex(p) and not _is_done(p)]
        candidates.sort(key=_paper_priority_key)
        return candidates
    except Exception as exc:
        _last_discovery_summary = {}
        supervisor_log(f"WARN: pipeline discovery summary failed; using fallback scan: {exc}")

    if not PUBLICATION_DIR.exists():
        return []
    candidates = []
    for child in sorted(PUBLICATION_DIR.iterdir()):
        if not child.is_dir():
            continue
        if child.name.startswith(".") or child.name.startswith("_"):
            continue
        if only and child.name not in only and str(child) not in only:
            continue
        if not _has_main_tex(child):
            continue
        if _is_done(child):
            continue
        candidates.append(child)
    candidates.sort(key=_paper_priority_key)
    return candidates


# ---------------------------------------------------------------------------
# inner loop manager (oracle_pipeline.py for one paper at a time)
# ---------------------------------------------------------------------------


def spawn_inner_pool(parallel: int, *, target_journal: str = "",
                     paper_filter: list[str] | None = None,
                     extra_args: list[str] | None = None) -> subprocess.Popen | None:
    """Spawn a single long-running oracle_pipeline.py with internal pool.

    oracle_pipeline.py's `run_rolling` already implements the
    "codex parallel + oracle queues" pattern: papers run concurrently in
    a ThreadPoolExecutor; while one worker is waiting on an Oracle browser
    response (I/O-bound), other workers continue Codex/Claude compute work
    (CPU-bound). Pool oversubscribes by MAX_ORACLE_WAIT_OVERSUBSCRIPTION
    so blocked workers do not idle the pool. The supervisor therefore
    spawns ONE inner with --all --parallel N --continuous and lets the
    inner own paper scheduling.

    paper_filter, when set, restricts the pool to those paper directories
    (passed as repeated --paper flags). Empty filter → --all.
    """
    if not ORACLE_PIPELINE_SCRIPT.exists():
        supervisor_log(f"oracle_pipeline.py missing at {ORACLE_PIPELINE_SCRIPT}")
        return None
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_handle = open(SUPERVISOR_LOG_DIR / "inner.log", "ab")
    mode = (f"--paper x{len(paper_filter)}" if paper_filter else "--all")
    log_handle.write(
        f"\n=== inner pool spawn at {_now_iso()} {mode} parallel={parallel} ===\n".encode()
    )
    log_handle.flush()
    cmd = [
        _python(),
        str(ORACLE_PIPELINE_SCRIPT),
        "--parallel", str(parallel),
        "--continuous",
    ]
    if paper_filter:
        for p in paper_filter:
            cmd.extend(["--paper", p])
    else:
        cmd.append("--all")
    if target_journal:
        cmd.extend(["--target-journal", target_journal])
    if extra_args:
        cmd.extend(extra_args)
    if not paper_filter and "--no-assign" not in cmd:
        cmd.append("--no-assign")
    try:
        proc = subprocess.Popen(
            cmd,
            cwd=str(REPO_ROOT),
            stdout=log_handle,
            stderr=subprocess.STDOUT,
            env=_subprocess_env(),
            **_detached_popen_kwargs(),
        )
    except Exception as exc:
        supervisor_log(f"inner pool spawn failed: {exc}")
        return None
    supervisor_log(
        f"inner pool spawned pid={proc.pid} parallel={parallel} mode={mode}"
    )
    return proc


# ---------------------------------------------------------------------------
# backlog refill (fallback producer)
# ---------------------------------------------------------------------------


def refill_last_run_ts() -> float:
    """Read the last-run timestamp from the refill queue (0.0 if absent)."""
    if not REFILL_QUEUE_PATH.exists():
        return 0.0
    try:
        data = json.loads(REFILL_QUEUE_PATH.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return 0.0
    raw = str(data.get("updated_at") or "")
    if not raw:
        return 0.0
    try:
        # ISO-8601, possibly trailing Z
        if raw.endswith("Z"):
            raw = raw[:-1] + "+00:00"
        return datetime.fromisoformat(raw).timestamp()
    except ValueError:
        return 0.0


def pi_review_last_run_ts() -> float:
    """Read the last PI review timestamp from the log file. 0.0 if never run."""
    if not PI_REVIEW_LOG.exists():
        return 0.0
    try:
        text = PI_REVIEW_LOG.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return 0.0
    last = ""
    for line in reversed(text.splitlines()):
        line = line.strip()
        if line.startswith("[") and "]" in line:
            last = line[1:line.index("]")]
            break
    if not last:
        return 0.0
    try:
        if last.endswith("Z"):
            last = last[:-1] + "+00:00"
        return datetime.fromisoformat(last).timestamp()
    except ValueError:
        return 0.0


def trigger_pi_review(*, codex_timeout: int = 900, claude_timeout: int = 600) -> bool:
    """Spawn pi_review.py in the background. Returns True if launched."""
    if not PI_REVIEW_SCRIPT.exists():
        supervisor_log(f"pi_review skipped: {PI_REVIEW_SCRIPT.name} missing")
        return False
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_path = SUPERVISOR_LOG_DIR / f"pi_review_{_now_tag_safe()}.log"
    cmd = [
        _python(),
        str(PI_REVIEW_SCRIPT),
        "--codex-timeout", str(codex_timeout),
        "--claude-timeout", str(claude_timeout),
    ]
    try:
        with open(log_path, "ab") as logf:
            subprocess.Popen(
                cmd,
                cwd=str(REPO_ROOT),
                stdout=logf,
                stderr=subprocess.STDOUT,
                env=_subprocess_env(),
                **_detached_popen_kwargs(),
            )
    except Exception as exc:
        supervisor_log(f"pi_review spawn failed: {exc}")
        return False
    supervisor_log("pi_review spawned (codex + claude joint health check)")
    return True


def trigger_refill(project_url: str, *, limit: int = 5,
                   timeout: int = 1800, model: str = "chatgpt-5.4-pro") -> bool:
    """Spawn paper_refill.py in the background. Returns True if launched."""
    if not REFILL_SCRIPT.exists():
        supervisor_log(f"refill skipped: {REFILL_SCRIPT.name} missing")
        return False
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_path = SUPERVISOR_LOG_DIR / f"refill_{_now_tag_safe()}.log"
    cmd = [
        _python(),
        str(REFILL_SCRIPT),
        "--limit", str(limit),
        "--timeout", str(timeout),
        "--model", model,
    ]
    if project_url:
        cmd.extend(["--project-url", project_url])
    try:
        with open(log_path, "ab") as logf:
            subprocess.Popen(
                cmd,
                cwd=str(REPO_ROOT),
                stdout=logf,
                stderr=subprocess.STDOUT,
                env=_subprocess_env(),
                **_detached_popen_kwargs(),
            )
    except Exception as exc:
        supervisor_log(f"refill spawn failed: {exc}")
        return False
    supervisor_log(
        f"refill spawned (limit={limit} timeout={timeout}s) — backlog drained, "
        f"candidates will land in {REFILL_QUEUE_PATH.name}"
    )
    return True


def refill_disabled_message() -> str:
    return "refill local-context mode available; --refill-project-url not set"


def maybe_refill_drained_backlog(args: Any) -> None:
    cooldown_s = max(0.0, args.refill_cooldown_hours * 3600.0)
    since_refill_s = _now() - refill_last_run_ts()
    if since_refill_s >= cooldown_s:
        if not args.refill_project_url:
            supervisor_log(refill_disabled_message())
        trigger_refill(
            args.refill_project_url,
            limit=args.refill_limit,
            timeout=args.refill_timeout,
        )
    else:
        remaining_h = (cooldown_s - since_refill_s) / 3600.0
        supervisor_log(f"refill cooldown not met ({remaining_h:.1f}h remaining)")


def default_auto_commit_paths() -> list[str]:
    return [
        "papers/publication",
        "tools/chatgpt-oracle/pipeline_state",
        "tools/chatgpt-oracle/oracle_pipeline.py",
        "tools/chatgpt-oracle/oracle_server.py",
        "tools/chatgpt-oracle/chatgpt_oracle_windows.user.js",
        "tools/chatgpt-oracle/chatgpt_oracle_macos.user.js",
        "tools/chatgpt-oracle/pipeline_supervisor.py",
        "tools/chatgpt-oracle/pipeline_health.py",
        "tools/chatgpt-oracle/tests/test_pipeline_supervisor.py",
        "tools/chatgpt-oracle/tests/test_pipeline_health.py",
        "tools/chatgpt-oracle/split_overlap_harness.py",
        "tools/chatgpt-oracle/tests/test_split_overlap_harness.py",
        "tools/chatgpt-oracle/SPLIT_SAFETY.md",
    ]


AUTO_COMMIT_DENY_PATTERNS = (
    ".tmp/",
    ".tmp\\",
    "/.tmp",
    "\\.tmp",
    ".tmp.",
    "_env_index",
    "envs_",
    "all_labels.tmp",
    "theorem_envs_fresh",
    "theorem_inventory_env",
    "theorem_inventory_live_envs",
    "theorem_envs_fresh_readable.txt",
    ".make_inventory.py",
    "write_inventory.py",
)


def auto_commit_allowed_file(path: str) -> bool:
    normalized = path.replace("\\", "/")
    lowered = normalized.lower()
    if "/__pycache__/" in lowered or lowered.endswith(".pyc"):
        return False
    return not any(pattern.lower() in lowered for pattern in AUTO_COMMIT_DENY_PATTERNS)


# ---------------------------------------------------------------------------
# auto-commit
# ---------------------------------------------------------------------------


def _git(args: list[str], capture: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=str(REPO_ROOT),
        capture_output=capture,
        text=True,
    )


def current_branch() -> str:
    res = _git(["rev-parse", "--abbrev-ref", "HEAD"])
    return (res.stdout or "").strip()


def commit_and_push_if_changed(allowed_branch: str, paths: list[str]) -> bool:
    branch = current_branch()
    if not branch:
        supervisor_log("auto-commit skipped: cannot resolve git branch")
        return False
    if branch != allowed_branch:
        supervisor_log(
            f"auto-commit skipped: on branch {branch!r}, refusing to push to {allowed_branch}"
        )
        return False

    diff = _git(["status", "--porcelain", "--", *paths])
    if not diff.stdout.strip():
        return False
    files: list[str] = []
    for line in diff.stdout.splitlines():
        parts = line.strip().split(None, 1)
        if len(parts) == 2:
            path = parts[1]
            if auto_commit_allowed_file(path):
                files.append(path)
            else:
                supervisor_log(f"auto-commit skip generated scratch: {path}")
    if not files:
        return False

    supervisor_log(f"auto-commit: {len(files)} changed file(s) — staging")
    _git(["add", "--", *files], capture=False)
    msg = f"pipeline supervisor: paper batch {_now_iso()}"
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
# signal / stop
# ---------------------------------------------------------------------------


def _install_signal_handlers() -> None:
    def _handler(signum, frame):
        try:
            STOP_FILE.write_text(f"signal {signum} at {_now_iso()}\n", encoding="utf-8")
        except OSError:
            pass

    sigterm = getattr(signal, "SIGTERM", None)
    handlers = [signal.SIGINT]
    if sigterm is not None and sigterm != signal.SIGINT:
        handlers.append(sigterm)
    if IS_WINDOWS:
        sigbreak = getattr(signal, "SIGBREAK", None)
        if sigbreak is not None:
            handlers.append(sigbreak)
    for sig in handlers:
        try:
            signal.signal(sig, _handler)
        except (OSError, ValueError):
            pass


# ---------------------------------------------------------------------------
# main loop
# ---------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(description="Paper pipeline supervisor (Windows-compatible)")
    parser.add_argument("--paper", action="append", default=[],
                        help="Restrict the inner pool to specific paper directories "
                             "(may repeat). Without this, the inner pool runs --all.")
    parser.add_argument("--parallel", type=int, default=0,
                        help="Inner pool parallelism. 0 means oracle_pipeline auto-detects "
                             "from CPU cores (typically 2-6). Codex/Claude run "
                             "concurrently; oracle waits do not idle the pool.")
    parser.add_argument("--target-journal", default="",
                        help="Pass-through to oracle_pipeline --target-journal")
    parser.add_argument("--inner-extra", action="append", default=[],
                        help="Extra args appended to each oracle_pipeline invocation "
                             "(may repeat). Example: --inner-extra --no-claude")
    parser.add_argument("--branch", default=SUPERVISOR_BRANCH_DEFAULT,
                        help=f"Only auto-commit on this branch (default {SUPERVISOR_BRANCH_DEFAULT})")
    parser.add_argument("--poll-interval", type=int, default=DEFAULT_POLL_INTERVAL_S,
                        help="Seconds between supervisor ticks while inner is running")
    parser.add_argument("--inner-restart-backoff", type=int, default=DEFAULT_INNER_RESTART_BACKOFF_S,
                        help="Seconds to back off after inner crash before respawn")
    parser.add_argument("--auto-commit-cooldown", type=int, default=DEFAULT_AUTO_COMMIT_COOLDOWN_S)
    parser.add_argument("--no-server-spawn", action="store_true",
                        help="Do not auto-spawn oracle_server.py")
    parser.add_argument("--no-auto-commit", action="store_true",
                        help="Disable git commit + push")
    parser.add_argument("--no-inner", action="store_true",
                        help="Skip spawning oracle_pipeline; tick-only (server health, "
                             "auto-commit, tab-stuck monitoring still run)")
    parser.add_argument("--refill-project-url", default="",
                        help="ChatGPT Project URL with main paper attached. "
                             "When set, supervisor triggers paper_refill.py "
                             "ONLY if (a) all existing papers are DONE and "
                             "(b) cooldown is satisfied. Refill is fallback, "
                             "not periodic — finishing existing splits comes first.")
    parser.add_argument("--refill-cooldown-hours", type=float,
                        default=DEFAULT_REFILL_COOLDOWN_HOURS,
                        help=f"Hours between refill runs (default {DEFAULT_REFILL_COOLDOWN_HOURS}h = 7d)")
    parser.add_argument("--refill-limit", type=int, default=5,
                        help="Max candidates per refill run")
    parser.add_argument("--refill-timeout", type=int, default=1800,
                        help="Oracle wait budget for refill (seconds)")
    parser.add_argument("--pi-review-hours", type=float, default=DEFAULT_PI_REVIEW_HOURS,
                        help=f"Hours between PI joint reviews (default {DEFAULT_PI_REVIEW_HOURS}h). "
                             "0 disables. PI review = codex + claude jointly assess "
                             "pipeline health and write to .pi_inbox.md.")
    parser.add_argument("--no-pi-review", action="store_true",
                        help="Disable PI joint review entirely.")
    parser.add_argument("--once", action="store_true",
                        help="Run a single tick (advance one paper, or just check) then exit")
    args = parser.parse_args()

    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    PIPELINE_STATE_DIR.mkdir(parents=True, exist_ok=True)
    _install_signal_handlers()

    supervisor_started_ts = _now()
    if not claim_supervisor_singleton(supervisor_started_ts):
        return 1

    if STOP_FILE.exists():
        supervisor_log(f"clearing stale STOP_FILE {STOP_FILE}")
        try:
            STOP_FILE.unlink()
        except OSError:
            pass

    supervisor_log(
        f"supervisor starting "
        f"(branch={args.branch} poll={args.poll_interval}s "
        f"server_spawn={'off' if args.no_server_spawn else 'on'} "
        f"auto_commit={'off' if args.no_auto_commit else 'on'} "
        f"inner={'off' if args.no_inner else 'on'} "
        f"platform={sys.platform})"
    )

    last_commit_ts = 0.0
    last_tab_alert_ts = 0.0
    supervisor_running_sha = disk_source_sha(Path(__file__))
    last_drift_alert_ts = 0.0
    last_supervisor_drift_alert_ts = 0.0
    last_pi_review_ts = pi_review_last_run_ts()
    server_proc: subprocess.Popen | None = None
    inner: subprocess.Popen | None = None

    auto_commit_paths = default_auto_commit_paths()

    paper_filter: list[str] = []
    if args.paper:
        for entry in args.paper:
            # Accept either the short name or an absolute path; oracle_pipeline.py
            # accepts both forms via its --paper flag.
            paper_filter.append(entry)

    try:
        while not STOP_FILE.exists():
            tick_started = _now()

            # P1: handle .server.restart signal — kill server so ensure_server
            # respawns it on this same tick.
            if SERVER_RESTART_FILE.exists():
                supervisor_log(f"server restart signal seen ({SERVER_RESTART_FILE.name})")
                if server_proc is not None and server_proc.poll() is None:
                    _terminate(server_proc, grace_seconds=15)
                    server_proc = None
                else:
                    supervisor_log(
                        "server was not started by this supervisor (or already exited); "
                        "ensure_server will (re)spawn on this tick"
                    )
                try:
                    SERVER_RESTART_FILE.unlink()
                except OSError:
                    pass

            if not args.no_server_spawn:
                # If our tracked proc died on its own, drop the handle so
                # ensure_server can respawn cleanly.
                if server_proc is not None and server_proc.poll() is not None:
                    rc = server_proc.poll()
                    supervisor_log(f"oracle_server exited rc={rc} on its own; will respawn")
                    server_proc = None
                spawned = ensure_server()
                if spawned is not None:
                    server_proc = spawned

            # P2: source-version drift between disk and running server.
            if server_alive():
                running_sha = server_source_sha()
                disk_sha = disk_source_sha(ORACLE_SERVER_SCRIPT)
                if running_sha and disk_sha and running_sha != disk_sha:
                    if _now() - last_drift_alert_ts > 1800:  # warn at most every 30 min
                        supervisor_log(
                            f"DRIFT: oracle_server.py on disk (sha={disk_sha}) differs from "
                            f"running server (sha={running_sha}). "
                            f"`touch {SERVER_RESTART_FILE.name}` to apply."
                        )
                        last_drift_alert_ts = _now()

            last_supervisor_drift_alert_ts = maybe_log_supervisor_drift(
                running_sha=supervisor_running_sha,
                last_alert_ts=last_supervisor_drift_alert_ts,
            )

            # P1: handle .inner.restart signal — terminate the current inner
            # so the next tick picks the next runnable paper with new code.
            if INNER_RESTART_FILE.exists():
                if oracle_work_in_flight():
                    supervisor_log(
                        f"inner restart signal deferred ({INNER_RESTART_FILE.name}); "
                        "Oracle work is still in flight"
                    )
                else:
                    supervisor_log(f"inner restart signal seen ({INNER_RESTART_FILE.name})")
                    if inner is not None and inner.poll() is None:
                        _terminate(inner, grace_seconds=20)
                    inner = None
                    current_paper = None
                    try:
                        INNER_RESTART_FILE.unlink()
                    except OSError:
                        pass

            if not args.no_inner:
                if inner is None or inner.poll() is not None:
                    if inner is not None and inner.poll() is not None:
                        rc = inner.poll()
                        supervisor_log(
                            f"inner pool exited rc={rc}; "
                            f"backoff {args.inner_restart_backoff}s before respawn"
                        )
                        time.sleep(args.inner_restart_backoff)
                        inner = None

                    # Decide whether there is anything to run before spawning
                    # the long-running pool. oracle_pipeline.py --all will
                    # exit immediately if no runnable papers remain, which
                    # gives us a natural signal to consider refill.
                    runnable = discover_runnable_papers(
                        paper_filter if paper_filter else None
                    )
                    if not runnable:
                        if paper_filter:
                            supervisor_log(
                                f"no runnable paper(s) match filter {paper_filter!r}; will retry next tick"
                            )
                        else:
                            detail = (
                                format_discovery_summary(_last_discovery_summary)
                                if _last_discovery_summary
                                else "fallback_scan_no_candidates"
                            )
                            supervisor_log(f"no runnable papers ({detail})")
                            watchdog_wake_recoverable_stage_a_blocks(
                                _last_discovery_summary
                            )
                            maybe_refill_drained_backlog(args)
                    else:
                        inner = spawn_inner_pool(
                            args.parallel,
                            target_journal=args.target_journal,
                            paper_filter=paper_filter or None,
                            extra_args=args.inner_extra,
                        )

            # Surface high-signal lines from inner.log + oracle_server.log so
            # supervisor's monitor sees Stage failures, Claude/codex outages,
            # compile errors, server unicode crashes etc without tailing
            # each child log directly.
            try:
                surface_log_alerts()
            except Exception as exc:
                supervisor_log(f"log surface error: {exc}")

            # Self-heal: cancel disposable tasks stuck on agents (no
            # operator value, no PI judgment needed).
            try:
                auto_heal_disposable_stuck(threshold_seconds=300)
            except Exception as exc:
                supervisor_log(f"auto-heal error: {exc}")

            # Real-task remediation tiers:
            #   30 min: log INFO only (PI will inspect)
            #   2 hour: supervisor auto-cancels (frees agent slot;
            #           Stage B/C will re-emit if needed)
            try:
                auto_cancel_long_stuck_real_tasks()
            except Exception as exc:
                supervisor_log(f"auto-cancel error: {exc}")
            real_stuck = [
                a for a in stuck_agents(AGENT_STUCK_THRESHOLD_S)
                if not str(a.get("task_id", "")).startswith(("smoke", "test_", "retry_"))
                and (a.get("elapsed") or 0) < REAL_TASK_AUTO_CANCEL_S
            ]
            if real_stuck:
                supervisor_log(
                    f"info: {len(real_stuck)} real task(s) stuck on agent "
                    f">{AGENT_STUCK_THRESHOLD_S//60}min — PI will inspect"
                )

            # User-side stuck conditions: PIPELINE CANNOT FIX without
            # operator action. These DO ping monitor.
            user_attention_needed = False
            user_attention_msg = ""
            if queue_stuck_too_long(TAB_STUCK_THRESHOLD_S):
                user_attention_needed = True
                user_attention_msg = (
                    "ALERT: queue waiting >5min for any browser agent. "
                    "Open https://chatgpt.com/?oracle=1 and click ACTIVATE."
                )
            else:
                aged = aged_queued_tasks(QUEUE_AGED_THRESHOLD_S)
                if aged:
                    joined = "; ".join(
                        f"{q['task_id'][:40]}@{q['age_seconds']}s"
                        for q in aged[:3]
                    )
                    user_attention_needed = True
                    user_attention_msg = (
                        f"ALERT: {len(aged)} real task(s) queued "
                        f">{QUEUE_AGED_THRESHOLD_S//60}min: {joined}. "
                        "Browser tabs likely insufficient or stuck."
                    )

            if user_attention_needed and _now() - last_tab_alert_ts > TAB_ALERT_DEBOUNCE_S:
                desktop_notify("pipeline supervisor: operator action needed",
                               user_attention_msg)
                last_tab_alert_ts = _now()

            if not args.no_auto_commit:
                if _now() - last_commit_ts >= args.auto_commit_cooldown:
                    try:
                        commit_and_push_if_changed(args.branch, auto_commit_paths)
                    except Exception as exc:
                        supervisor_log(f"auto-commit error: {exc}")
                    last_commit_ts = _now()

            if not args.no_pi_review and args.pi_review_hours > 0:
                cooldown_s = args.pi_review_hours * 3600.0
                since_pi_s = _now() - last_pi_review_ts
                if since_pi_s >= cooldown_s:
                    if trigger_pi_review():
                        last_pi_review_ts = _now()

            if args.once:
                break

            elapsed = _now() - tick_started
            time.sleep(max(5.0, args.poll_interval - elapsed))

    except KeyboardInterrupt:
        supervisor_log("supervisor interrupted")
    finally:
        if inner is not None and inner.poll() is None:
            _terminate(inner)
        # Leave server_proc alone on supervisor exit — operators may want the
        # bridge to keep running while they tinker with the supervisor itself.
        # If they want a full shutdown they can `taskkill` / `kill` the server.
        if STOP_FILE.exists():
            try:
                STOP_FILE.unlink()
            except OSError:
                pass
        cleanup_supervisor_pid()
        supervisor_log("supervisor exiting")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
