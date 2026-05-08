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

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent

ORACLE_SERVER_URL = "http://localhost:8765"
ORACLE_SERVER_SCRIPT = SCRIPT_DIR / "oracle_server.py"
ORACLE_PIPELINE_SCRIPT = SCRIPT_DIR / "oracle_pipeline.py"
PIPELINE_STATE_DIR = SCRIPT_DIR / "pipeline_state"

PUBLICATION_DIR = REPO_ROOT / "papers" / "publication"
SUPERVISOR_LOG_DIR = SCRIPT_DIR / "supervisor_logs"
STOP_FILE = SCRIPT_DIR / ".pipeline_supervisor.stop"
SERVER_RESTART_FILE = SCRIPT_DIR / ".server.restart"
INNER_RESTART_FILE = SCRIPT_DIR / ".inner.restart"
SUPERVISOR_BRANCH_DEFAULT = "dev-automation-integration"

DEFAULT_POLL_INTERVAL_S = 120
DEFAULT_INNER_RESTART_BACKOFF_S = 30
DEFAULT_AUTO_COMMIT_COOLDOWN_S = 600
TAB_STUCK_THRESHOLD_S = 300
TAB_ALERT_DEBOUNCE_S = 600
SERVER_BOOT_GRACE_S = 4

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
    operator can scrape state.
    """
    supervisor_log(f"NOTIFY: {title} — {body}")
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


def queue_stuck_too_long(threshold_seconds: int) -> bool:
    s = server_status()
    if s.get("diagnosis") != "queue_waiting_for_browser_agent":
        return False
    queued = s.get("queued_tasks") or []
    return any((t.get("age_seconds") or 0) > threshold_seconds for t in queued)


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


def discover_runnable_papers(only: list[str] | None = None) -> list[Path]:
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


def spawn_inner_for_paper(paper_dir: Path, *, target_journal: str = "",
                          extra_args: list[str] | None = None) -> subprocess.Popen | None:
    if not ORACLE_PIPELINE_SCRIPT.exists():
        supervisor_log(f"oracle_pipeline.py missing at {ORACLE_PIPELINE_SCRIPT}")
        return None
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_handle = open(SUPERVISOR_LOG_DIR / "inner.log", "ab")
    log_handle.write(
        f"\n=== inner spawn at {_now_iso()} paper={paper_dir.name} ===\n".encode()
    )
    log_handle.flush()
    cmd = [
        _python(),
        str(ORACLE_PIPELINE_SCRIPT),
        "--paper", str(paper_dir),
    ]
    if target_journal:
        cmd.extend(["--target-journal", target_journal])
    if extra_args:
        cmd.extend(extra_args)
    try:
        proc = subprocess.Popen(
            cmd,
            cwd=str(REPO_ROOT),
            stdout=log_handle,
            stderr=subprocess.STDOUT,
            **_detached_popen_kwargs(),
        )
    except Exception as exc:
        supervisor_log(f"inner spawn failed for {paper_dir.name}: {exc}")
        return None
    supervisor_log(f"inner spawned pid={proc.pid} paper={paper_dir.name}")
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
    if not project_url:
        supervisor_log("refill skipped: --refill-project-url not set")
        return False
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_path = SUPERVISOR_LOG_DIR / f"refill_{_now_tag_safe()}.log"
    cmd = [
        _python(),
        str(REFILL_SCRIPT),
        "--project-url", project_url,
        "--limit", str(limit),
        "--timeout", str(timeout),
        "--model", model,
    ]
    try:
        with open(log_path, "ab") as logf:
            subprocess.Popen(
                cmd,
                cwd=str(REPO_ROOT),
                stdout=logf,
                stderr=subprocess.STDOUT,
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
            files.append(parts[1])
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
                        help="Restrict to specific paper directory name (may repeat). "
                             "Without this, supervisor picks runnable papers automatically.")
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

    if STOP_FILE.exists():
        supervisor_log(f"clearing stale STOP_FILE {STOP_FILE}")
        try:
            STOP_FILE.unlink()
        except OSError:
            pass

    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    PIPELINE_STATE_DIR.mkdir(parents=True, exist_ok=True)
    _install_signal_handlers()

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
    last_drift_alert_ts = 0.0
    last_pi_review_ts = pi_review_last_run_ts()
    server_proc: subprocess.Popen | None = None
    inner: subprocess.Popen | None = None
    current_paper: Path | None = None

    auto_commit_paths = [
        "papers/publication",
        "tools/chatgpt-oracle/pipeline_state",
    ]

    only_papers: list[str] | None = None
    if args.paper:
        only_papers = []
        for entry in args.paper:
            p = Path(entry)
            only_papers.append(p.name if p.is_absolute() or "/" in entry or "\\" in entry else entry)

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

            # P1: handle .inner.restart signal — terminate the current inner
            # so the next tick picks the next runnable paper with new code.
            if INNER_RESTART_FILE.exists():
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
                            f"inner exited rc={rc} (paper={current_paper.name if current_paper else '-'}); "
                            f"backoff {args.inner_restart_backoff}s before next paper"
                        )
                        time.sleep(args.inner_restart_backoff)
                        inner = None
                        current_paper = None

                    runnable = discover_runnable_papers(only_papers)
                    if not runnable:
                        if only_papers is not None:
                            supervisor_log(
                                f"no runnable paper(s) match filter {only_papers!r}; will retry next tick"
                            )
                        else:
                            supervisor_log("no runnable papers (all DONE or none with main.tex)")
                            # Backlog drained → maybe trigger fallback refill.
                            if args.refill_project_url:
                                cooldown_s = max(0.0, args.refill_cooldown_hours * 3600.0)
                                since_refill_s = _now() - refill_last_run_ts()
                                if since_refill_s >= cooldown_s:
                                    trigger_refill(
                                        args.refill_project_url,
                                        limit=args.refill_limit,
                                        timeout=args.refill_timeout,
                                    )
                                else:
                                    remaining_h = (cooldown_s - since_refill_s) / 3600.0
                                    supervisor_log(
                                        f"refill cooldown not met ({remaining_h:.1f}h remaining)"
                                    )
                    else:
                        target = runnable[0]
                        current_paper = target
                        inner = spawn_inner_for_paper(
                            target,
                            target_journal=args.target_journal,
                            extra_args=args.inner_extra,
                        )

            if queue_stuck_too_long(TAB_STUCK_THRESHOLD_S):
                if _now() - last_tab_alert_ts > TAB_ALERT_DEBOUNCE_S:
                    desktop_notify(
                        "pipeline supervisor: tab stuck",
                        "ChatGPT oracle tab stuck >5min. Open https://chatgpt.com/?oracle=1 and click ACTIVATE.",
                    )
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
        supervisor_log("supervisor exiting")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
