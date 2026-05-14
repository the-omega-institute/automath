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
    SOLVED / HANDOFF markers; Pending User Approval is rechecked by the
    science gate so incomplete or stale review marks can re-enter repair
  - skips targets that already have a recent (< 24h) summary (cooldown)

Stale claims (default > 4h since marker mtime, no live process) are reaped
by cleanup_stale_claims(); the supervisor calls this every tick.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import fcntl
import hashlib
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
RESEARCH_LOOP_LOCK = STATE_DIR / "research_loop.lock"
CODEX_TRANSPORT_STATE = STATE_DIR / "codex_transport.json"
ORACLE_BRIDGE_STATE = STATE_DIR / "oracle_bridge.json"
RESEARCH_BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"
DRAFTS_DIR = SCRIPT_DIR / "drafts"
TARGETS_DIR = SCRIPT_DIR / "targets"
DISPATCH_WORKTREE = SCRIPT_DIR / "dispatch_worktree.py"
ORACLE_RECONCILE = SCRIPT_DIR / "outreach_oracle_reconcile.py"
LOCAL_REPAIR = SCRIPT_DIR / "outreach_local_repair.py"

DEFAULT_PARALLEL = 2
DEFAULT_POLL_INTERVAL = 120
DEFAULT_CLAIM_STALE_HOURS = 4
DEFAULT_TARGET_TIMEOUT_S = 7200  # 2h hard cap per target
DEFAULT_ORACLE_REFILL_RESERVE = int(os.environ.get("OUTREACH_ORACLE_REFILL_RESERVE", "1") or "1")
SUMMARY_COOLDOWN_HOURS = 2
TRANSPORT_FAILURE_BACKOFF_MINUTES = int(os.environ.get("OUTREACH_TRANSPORT_BACKOFF_MINUTES", "5") or "5")
DEFAULT_ORACLE_TURN_TIMEOUT_S = 7200
CODEX_TRANSPORT_BACKOFF_MINUTES = int(
    os.environ.get("OUTREACH_CODEX_TRANSPORT_BACKOFF_MINUTES", str(TRANSPORT_FAILURE_BACKOFF_MINUTES)) or "5"
)

# Regex matchers for board status filtering. Case-insensitive substring tests.
SKIP_STATUS_PATTERNS = [
    "CLOSED",
    "DISCARDED",
    "OVERTAKEN",
    "SOLVED",
    "HANDOFF",
    "not outreach",
]

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_preflight import ACTIONABLE_VERDICTS, judge  # noqa: E402
from outreach_science_gate import CLOSE_TARGET, WRITEBACK_READY, evaluate as science_gate_evaluate  # noqa: E402
from outreach_impact_gate import (  # noqa: E402
    IMPACT_PLAN_READY,
    CLOSE_OR_ARCHIVE as IMPACT_CLOSE_OR_ARCHIVE,
    evaluate as impact_gate_evaluate,
    write_ledger as write_impact_ledger,
)
from outreach_profile import load_profile  # noqa: E402


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------


def _now() -> float:
    return time.time()


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _iso_from_epoch(epoch: float) -> str:
    return datetime.fromtimestamp(epoch, timezone.utc).isoformat(timespec="seconds")


def _now_tag_safe() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def loop_log(msg: str) -> None:
    RESEARCH_LOOP_LOG_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {msg}"
    print(line, flush=True)
    with open(RESEARCH_LOOP_LOG_DIR / "research_loop.log", "a", encoding="utf-8") as f:
        f.write(line + "\n")


def _impact_allows_operator_review(impact_gate) -> bool:
    """Only operator-surface real results or explicit archive decisions.

    Science gate says whether a local mathematical packet is internally
    coherent.  Impact gate says whether it is worth interrupting the operator
    as an external-facing result.  Bounded verifier/audit packets may satisfy
    the former while still being too low-value for this project's current
    research lane.
    """
    status = str(getattr(impact_gate, "status", "") or "")
    return status in {IMPACT_PLAN_READY, IMPACT_CLOSE_OR_ARCHIVE}


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


def _cooldown_applies(todo_id: str, slug: str, cooldown_hours: float) -> bool:
    """Avoid re-notifying terminal/user-review targets, not active research.

    The old loop treated any recent summary as a hard cooldown. That made the
    harness passive: a target could remain NEEDS_EVIDENCE but be skipped for a
    day. Here cooldown only applies when science_gate already says the target
    is terminal or ready for operator review. Active deep-reason targets should
    keep iterating until a gate closes, writes back, or the board status changes.
    """
    if not _has_recent_summary(slug, cooldown_hours):
        return False
    todos = _parse_board_safe()
    todo = todos.get(todo_id)
    if todo is None:
        return True
    try:
        gate = science_gate_evaluate(todo)
    except Exception:
        return False
    return gate.status in {WRITEBACK_READY, CLOSE_TARGET}


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


def _live_worker_for_target(todo_id: str, slug: str) -> bool:
    """Detect orphan/in-flight workers for the same target.

    A supervisor restart can orphan a dispatch_worktree process while its
    Oracle call is still pending.  The claim marker may be stale or already
    cleaned, but starting a second local_repair/oracle cycle for the same
    target corrupts the target-local workup handoff.  Match by todo_id first
    because it is present in worker command lines; keep a slug fallback for
    older/manual invocations.
    """
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
    todo_markers = (
        f"dispatch_worktree.py --supervise --supervise-id {todo_id}",
        f"dispatch_worktree.py --supervise-id {todo_id}",
        f"outreach_local_repair.py --todo-id {todo_id}",
    )
    for line in (proc.stdout or "").splitlines():
        if any(marker in line for marker in todo_markers):
            return True
        if slug and f" {slug} " in f" {line} ":
            return True
    return False


def _live_dispatch_for_slug(slug: str) -> bool:
    """Backward-compatible stale-claim helper for older marker files."""
    try:
        todos = _parse_board_safe()
    except Exception:
        todos = {}
    for todo_id, todo in todos.items():
        try:
            if todo.slug() == slug and _live_worker_for_target(todo_id, slug):
                return True
        except Exception:
            continue
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
        if mtime > cutoff and (_pid_alive(pid) or _live_dispatch_for_slug(d.name)):
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
        "--no-arxiv-stage0",
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


def _oracle_batch_turns(todo_id: str) -> int:
    """One browser-bound Oracle turn per local harness cycle.

    Scientific stopping is not a turn-count decision.  We deliberately return
    to the outer loop after every Oracle answer so Codex can replay/check the
    locally testable part before the next follow-up is generated in the same
    ChatGPT conversation.
    """
    return 1


def _spawn_oracle_deep(todo_id: str, timeout_s: int) -> tuple[int, str]:
    """Run dispatch_worktree.py --supervise --oracle-deep for one target.

    This is the default fallback when deterministic science_gate says the next
    action is deep_reason. The turn count here is only a per-batch watchdog:
    scientific stopping is decided after each batch by science_gate, not by this
    integer.
    """
    if not DISPATCH_WORKTREE.exists():
        return 127, ""
    RESEARCH_LOOP_LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_path = RESEARCH_LOOP_LOG_DIR / f"oracle_deep_{todo_id}_{_now_tag_safe()}.log"
    per_turn_timeout = min(DEFAULT_ORACLE_TURN_TIMEOUT_S, max(600, timeout_s))
    batch_turns = _oracle_batch_turns(todo_id)
    cmd = [
        "python3", str(DISPATCH_WORKTREE),
        "--supervise",
        "--supervise-id", todo_id,
        "--oracle-deep",
        "--codex-driver",
        "--oracle-max-turns", str(batch_turns),
        "--oracle-timeout", str(per_turn_timeout),
    ]
    env = os.environ.copy()
    env["OUTREACH_ALLOW_PRE_ORACLE_WORKUP_REUSE"] = "1"
    hard_timeout = max(timeout_s, batch_turns * per_turn_timeout + 300)
    with open(log_path, "ab") as logf:
        proc = subprocess.Popen(
            cmd,
            cwd=str(REPO_ROOT),
            env=env,
            stdout=logf,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        try:
            rc = proc.wait(timeout=hard_timeout)
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


def _missing_requires_local_repair(missing: list[str]) -> bool:
    """True when science_gate is blocked by repository-local evidence.

    In this state the next owner is Codex/local execution, not Oracle.  Oracle
    can propose mathematics, but only the local harness can honestly create,
    run, or reject replay scripts and verifier artifacts.
    """
    text = "\n".join(str(x).lower() for x in missing or [])
    needles = (
        "referenced local artifact missing",
        "local runnable replay artifact",
        "local runnable reproducer",
        "lacks a local runnable reproducer",
        "replay/formal verification",
        "verifier_command",
        "checker_command",
        "reproduction_command",
        "enumerator_command",
        "script_path",
    )
    return any(needle in text for needle in needles)


def _spawn_local_repair(todo_id: str, timeout_s: int) -> tuple[int, str]:
    """Run Codex local follow-up/replay for one target.

    This is used both for hard missing-artifact repair and for the ordinary
    Oracle→Codex loop: Oracle proposes or proves; Codex tries to replay the
    locally testable part and writes the next exact handoff.
    """
    if not LOCAL_REPAIR.exists():
        return 127, ""
    RESEARCH_LOOP_LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_path = RESEARCH_LOOP_LOG_DIR / f"local_repair_{todo_id}_{_now_tag_safe()}.log"
    try:
        default_repair_timeout = int(os.environ.get("OUTREACH_LOCAL_WORKUP_TIMEOUT", "900") or "900")
    except ValueError:
        default_repair_timeout = 900
    repair_timeout = max(600, min(timeout_s, default_repair_timeout))
    cmd = [
        "python3",
        str(LOCAL_REPAIR),
        "--todo-id",
        todo_id,
        "--timeout",
        str(repair_timeout),
        "--json",
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
            rc = proc.wait(timeout=repair_timeout + 300)
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


def _run_codex_workup_before_oracle(todo_id: str, slug: str, timeout_s: int) -> tuple[int, str]:
    """Always let Codex inspect/process the target before an Oracle batch.

    The Oracle prompt should be built from a local workup, not just from board
    metadata.  This pass may create verifier scripts, replay simple checks, or
    simply write codex_workup.md with the exact proof obligation Oracle should
    attack next.
    """
    loop_log(f"{todo_id}: refreshing Codex local workup before Oracle")
    started = _now()
    rc, log_path = _spawn_local_repair(todo_id, timeout_s)
    loop_log(f"{todo_id}: pre-Oracle Codex workup rc={rc} ({log_path})")
    if rc != 0:
        _note_local_repair_backoff(slug, reason=f"pre-oracle codex workup rc={rc}", log_path=log_path)
        return rc, log_path
    fresh_ok, fresh_reason = _pre_oracle_workup_fresh_after(slug, started)
    if not fresh_ok:
        _note_local_repair_backoff(
            slug,
            reason=f"pre-oracle codex workup stale/unusable after current run: {fresh_reason}",
            log_path=log_path,
        )
        loop_log(f"{todo_id}: pre-Oracle Codex workup stale/unusable after current run ({fresh_reason})")
        return 2, log_path
    return rc, log_path


def _extract_next_oracle_question_from_workup(text: str) -> str:
    if not text:
        return ""
    match = re.search(r"(?ims)^##\s+Next\s+Oracle\s+question\s*$\s*(.*?)(?=^##\s+|\Z)", text)
    if not match:
        return ""
    return match.group(1).strip()


def _extract_workup_section(text: str, heading: str) -> str:
    if not text:
        return ""
    pattern = re.compile(
        r"(?ims)^##\s+"
        + re.escape(heading).replace(r"\ ", r"\s+")
        + r"\s*$"
        + r"(.*?)"
        + r"(?=^##\s+|\Z)"
    )
    match = pattern.search(text)
    return match.group(1).strip() if match else ""


def _read_next_oracle_question(slug: str) -> str:
    """Return the exact Codex-selected next Oracle question, if present."""
    target_dir = TARGETS_DIR / slug
    direct = target_dir / "next_oracle_question.md"
    workup = target_dir / "codex_workup.md"
    workup_text = ""
    workup_question = ""
    try:
        workup_text = workup.read_text(encoding="utf-8", errors="replace")
        workup_question = _extract_next_oracle_question_from_workup(workup_text)
    except OSError:
        pass
    try:
        if direct.exists():
            text = direct.read_text(encoding="utf-8", errors="replace").strip()
            if text:
                try:
                    if workup_question and workup.stat().st_mtime > direct.stat().st_mtime + 300:
                        return workup_question
                except OSError:
                    pass
                return text
    except OSError:
        pass
    return workup_question


def _is_concrete_next_oracle_question(question: str) -> bool:
    """Reject generic continuation prompts before they reach Oracle."""
    q = (question or "").strip()
    if len(q) < 120:
        return False
    lowered = question.lower()
    if len(question) < 80:
        return False
    generic_markers = (
        "continue research",
        "继续研究",
        "do the next step",
        "lower the progress metric",
        "provide metadata",
        "review the board",
        "look into this problem",
        "make progress",
        "find something useful",
    )
    if any(marker in lowered for marker in generic_markers):
        return False
    concrete_markers = (
        "prove",
        "disprove",
        "certificate",
        "construction",
        "counterexample",
        "verifier",
        "exact",
        "bound",
        "obstruction",
        "cnf",
        "lrat",
        "drat",
        "graph",
        "lemma",
        "theorem",
        "compute",
        "enumerate",
        "check",
    )
    return any(marker in lowered for marker in concrete_markers)


def _local_grounding_tokens(text: str) -> set[str]:
    body = text or ""
    lowered = body.lower()
    tokens: set[str] = set()
    patterns = (
        r"tools/community-outreach/targets/[A-Za-z0-9_.\-/]+",
        r"\b[A-Za-z0-9_.\-/]*(?:results\.json|verify[A-Za-z0-9_.-]*\.py|check[A-Za-z0-9_.-]*\.py|oracle_claim_packet_[A-Za-z0-9_.-]*\.md)\b",
        r"\b[A-Za-z0-9_.\-/]+\.(?:json|py|cnf|drat|lrat|rup|g6|graph6|edge|vtx|sage|m)\b",
        r"\b(?:sha-?256|hash)\s*[:= ]\s*[a-f0-9]{6,64}\b",
        r"\bcase[- ]?\d+\b",
        r"\b(?:n|k|m)\s*=\s*\d+\b",
        r"\b(?:\d+)\s+(?:vertices|edges|clauses|variables)\b",
    )
    for pattern in patterns:
        for match in re.findall(pattern, body, flags=re.IGNORECASE):
            token = match if isinstance(match, str) else " ".join(match)
            token = re.sub(r"\s+", " ", token.strip().lower())
            if len(token) >= 4:
                tokens.add(token)
    for phrase in (
        "no local replay",
        "found no",
        "not present",
        "first failed check",
        "missing certificate",
        "missing lemma",
        "missing proof",
        "failed at the first local check",
        "exit 0",
        "exited 0",
        "unsat",
        "sat",
    ):
        if phrase in lowered:
            tokens.add(phrase)
    return tokens


def _question_is_grounded_in_local_work(question: str, workup: str, slug: str) -> bool:
    q = (question or "").lower()
    if not q.strip():
        return False
    local_body = _extract_workup_section(workup, "Local evidence checked")
    commands_body = _extract_workup_section(workup, "Commands run")
    attempt_body = _extract_workup_section(workup, "Codex attempt before Oracle")
    artifact_body = _extract_workup_section(workup, "Verifier/artifact status")
    obligations_body = _extract_workup_section(workup, "Proof obligations still open")
    evidence = "\n".join([local_body, commands_body, attempt_body, artifact_body, obligations_body])
    tokens = _local_grounding_tokens(evidence)
    return any(token and token in q for token in tokens)


def _workup_has_local_execution_trace(text: str) -> tuple[bool, str]:
    """Require evidence that Codex actually processed the target before Oracle.

    A standalone `next_oracle_question.md` is not enough: it can be produced by
    prompt decoration without any local replay/check.  The workup must expose
    what was inspected, what command/check was run or why none was possible,
    what artifact state was observed, and what proof obligations remain.
    """
    stripped = (text or "").strip()
    if len(stripped) < 500:
        return False, "codex_workup.md too short to show local processing"
    lowered = stripped.lower()
    required_sections = (
        "## local evidence checked",
        "## commands run",
        "## codex attempt before oracle",
        "## verifier/artifact status",
        "## proof obligations still open",
        "## next oracle question",
    )
    missing_sections = [section for section in required_sections if section not in lowered]
    if missing_sections:
        return False, "codex_workup.md missing sections: " + ", ".join(missing_sections)
    local_body = _extract_workup_section(stripped, "Local evidence checked")
    commands_body = _extract_workup_section(stripped, "Commands run")
    attempt_body = _extract_workup_section(stripped, "Codex attempt before Oracle")
    artifact_body = _extract_workup_section(stripped, "Verifier/artifact status")
    if len(local_body) < 80:
        return False, "Local evidence checked section too thin to prove target inspection"
    if len(commands_body) < 80:
        return False, "Commands run section too thin to prove local execution"
    if len(attempt_body) < 120:
        return False, "Codex attempt before Oracle section too thin to prove an actual local/proof attempt"
    if len(artifact_body) < 80:
        return False, "Verifier/artifact status section too thin to prove artifact review"
    command_markers = (
        "```",
        "$ ",
        "python3 ",
        "python ",
        "rg ",
        "find ",
        "git status",
        "sed -n",
        "cat ",
        "ls ",
        "date ",
        "lean ",
        "lake ",
        "sage ",
        "magma ",
        "gap ",
        "node ",
        "npm ",
        "pytest",
        "curl ",
        "unzip ",
        "sha256sum",
    )
    commands_lower = commands_body.lower()
    if not any(marker in commands_lower for marker in command_markers):
        return False, "Commands run section lacks concrete shell/tool commands"
    inspection_markers = (
        "inspected",
        "searched",
        "found",
        "confirmed",
        "checked",
        "ran",
        "replayed",
        "no oracle claim",
        "missing",
        "absent",
    )
    local_artifact_text = f"{local_body}\n{artifact_body}".lower()
    if not any(marker in local_artifact_text for marker in inspection_markers):
        return False, "local evidence/artifact sections do not describe an actual inspection result"
    if not _text_has_codex_attempt(attempt_body):
        return False, "Codex attempt before Oracle lacks a real attempt/action/outcome on the current mathematical gap"
    trace_markers = (
        "command",
        "ran",
        "checked",
        "verified",
        "passed",
        "failed",
        "missing",
        "not run",
        "no local",
        "no oracle claim",
        "results.json",
        "verifier",
        "artifact",
        "python",
    )
    if not any(marker in lowered for marker in trace_markers):
        return False, "codex_workup.md lacks local command/check/artifact trace"
    return True, ""


def _text_has_codex_attempt(text: str) -> bool:
    body = (text or "").strip()
    if len(body) < 120:
        return False
    lowered = body.lower()
    action_markers = (
        "attempted",
        "tried",
        "ran",
        "computed",
        "checked",
        "replayed",
        "verified",
        "constructed",
        "enumerated",
        "proved",
        "reduced",
        "tested",
        "split",
        "derived",
        "bounded",
        "failed",
        "blocked",
        "no local replay",
    )
    outcome_markers = (
        "result",
        "outcome",
        "therefore",
        "because",
        "confirmed",
        "refuted",
        "mismatch",
        "counterexample",
        "obstruction",
        "blocker",
        "missing",
        "not present",
        "timeout",
        "unsat",
        "sat",
        "pass",
        "fail",
        "cannot",
        "needs oracle",
    )
    math_or_artifact_markers = (
        "proof",
        "lemma",
        "theorem",
        "bound",
        "certificate",
        "construction",
        "verifier",
        "script",
        "results.json",
        "oracle_claim_packet",
        "cnf",
        "drat",
        "lrat",
        "graph",
        "hash",
        "sha",
        "case",
        "finite",
        "recurrence",
    )
    return (
        any(marker in lowered for marker in action_markers)
        and any(marker in lowered for marker in outcome_markers)
        and any(marker in lowered for marker in math_or_artifact_markers)
    )


def _local_repair_last_has_codex_command_trace(slug: str) -> tuple[bool, str]:
    """Require machine-observed Codex commands before an Oracle turn."""
    path = TARGETS_DIR / slug / "local_repair_last.json"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError:
        return False, "missing local_repair_last.json"
    except json.JSONDecodeError as exc:
        return False, f"invalid local_repair_last.json: {exc}"
    if not payload.get("ok"):
        return False, "last local repair did not pass"
    postcheck = payload.get("postcheck") if isinstance(payload, dict) else None
    if not isinstance(postcheck, dict):
        return False, "last local repair missing postcheck"
    trace = postcheck.get("codex_command_trace")
    if not isinstance(trace, dict):
        return False, "last local repair missing Codex command trace"
    if not trace.get("ok"):
        return False, str(trace.get("reason") or "Codex command trace not ok")
    if int(trace.get("target_command_count") or 0) <= 0:
        return False, "Codex command trace has no target-local commands"
    stdout_log = str(payload.get("stdout_log") or "")
    if not stdout_log:
        return False, "last local repair missing stdout_log"
    stdout_path = REPO_ROOT / stdout_log
    if not stdout_path.exists():
        return False, f"last local repair stdout_log is missing: {stdout_log}"
    if _parse_iso_time(str(payload.get("finished_at") or "")) is None:
        return False, "last local repair missing valid finished_at"
    substantive = postcheck.get("substantive_local_work")
    if not isinstance(substantive, dict):
        return False, "last local repair missing substantive local-work check"
    if not substantive.get("ok"):
        diagnostics = substantive.get("diagnostics")
        if isinstance(diagnostics, list) and diagnostics:
            return False, "substantive local-work check failed: " + "; ".join(str(item) for item in diagnostics[:4])
        return False, "substantive local-work check failed"
    if not substantive.get("report_declares_pre_oracle_processing"):
        return False, "local repair report does not declare the pre-Oracle mathematical action"
    math_action_count = int(
        substantive.get("mathematical_action_command_count")
        or trace.get("mathematical_action_command_count")
        or 0
    )
    if math_action_count <= 0:
        return False, "Codex command trace has no target-local mathematical action before Oracle"
    return True, ""


def _parse_iso_time(value: str) -> float | None:
    text = (value or "").strip()
    if not text:
        return None
    try:
        return datetime.fromisoformat(text.replace("Z", "+00:00")).timestamp()
    except ValueError:
        return None


def _last_local_repair_window(slug: str) -> tuple[float | None, float | None, str]:
    path = TARGETS_DIR / slug / "local_repair_last.json"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError:
        return None, None, "missing local_repair_last.json"
    except json.JSONDecodeError as exc:
        return None, None, f"invalid local_repair_last.json: {exc}"
    started = _parse_iso_time(str(payload.get("started_at") or ""))
    if started is None:
        return None, None, "last local repair missing valid started_at"
    finished = _parse_iso_time(str(payload.get("finished_at") or ""))
    if finished is None:
        return None, None, "last local repair missing valid finished_at"
    return started, finished, ""


def _last_local_repair_finished_at(slug: str) -> tuple[float | None, str]:
    _started, finished, reason = _last_local_repair_window(slug)
    if finished is None:
        return None, reason
    return finished, ""


def _pre_oracle_workup_status(slug: str) -> tuple[bool, str]:
    """Ensure Codex left both a concrete question and a real local workup."""
    target_dir = TARGETS_DIR / slug
    question = _read_next_oracle_question(slug)
    if not _is_concrete_next_oracle_question(question):
        return False, "missing concrete next_oracle_question"
    workup_path = target_dir / "codex_workup.md"
    try:
        workup = workup_path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return False, "missing codex_workup.md"
    ok, reason = _workup_has_local_execution_trace(workup)
    if not ok:
        return False, reason
    if not _question_is_grounded_in_local_work(question, workup, slug):
        return False, (
            "next_oracle_question is not grounded in this local workup; "
            "it must reuse a target-local path/artifact, command result, hash, "
            "finite case label, or explicit local failure"
        )
    trace_ok, trace_reason = _local_repair_last_has_codex_command_trace(slug)
    if not trace_ok:
        return False, trace_reason
    return True, ""


def _pre_oracle_workup_fresh_after(slug: str, started_at: float) -> tuple[bool, str]:
    """Ensure the accepted workup was written by this local-repair pass.

    A target can have a good old `codex_workup.md`.  That is useful context, but
    it must not let the harness skip the current Codex pass after a new Oracle
    packet, verifier change, or board edit.  The accepted handoff should be at
    least as fresh as the local-repair invocation that just returned.
    """
    ok, reason = _pre_oracle_workup_status(slug)
    if not ok:
        return ok, reason
    target_dir = TARGETS_DIR / slug
    required = (
        "codex_workup.md",
        "next_oracle_question.md",
        "local_repair_report.md",
    )
    stale: list[str] = []
    threshold = max(0.0, started_at - 2.0)
    for name in required:
        path = target_dir / name
        try:
            mtime = path.stat().st_mtime
        except OSError:
            return False, f"missing {name}"
        if mtime < threshold:
            stale.append(name)
    if stale:
        return False, "stale local repair handoff: " + ", ".join(stale)
    return True, ""


def _is_transport_stub_response(text: str) -> bool:
    stripped = (text or "").strip()
    if not stripped:
        return True
    lowered = stripped.lower()
    markers = (
        "error: task cancelled by server",
        "error (re-extract):",
        "error: empty response",
        "empty response (timeout or extraction failure)",
        "no assistant output after",
        "re-extract: nothing meaningful",
        "re-extract: empty response",
        "server unreachable",
    )
    if any(lowered.startswith(marker) for marker in markers):
        return True
    return len(stripped) < 80 and "cancelled" in lowered and "server" in lowered


def _claim_packet_oracle_response(text: str) -> str:
    marker = "## Oracle Response"
    idx = text.find(marker)
    if idx < 0:
        return text
    return text[idx + len(marker) :].strip()


def _latest_substantive_claim_packet(target_dir: Path) -> Path | None:
    packets = sorted(
        target_dir.glob("oracle_claim_packet_*.md"),
        key=lambda p: p.stat().st_mtime if p.exists() else 0,
        reverse=True,
    )
    for packet in packets:
        try:
            text = packet.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if not _is_transport_stub_response(_claim_packet_oracle_response(text)):
            return packet
    return None


def _pre_oracle_workup_recent(slug: str, *, max_age_seconds: int) -> tuple[bool, str]:
    """Accept a fresh Codex handoff without rerunning local repair.

    Oracle still never receives a raw board card: this reuses only a handoff
    that already passed the same machine-observed Codex command trace gate and
    is newer than the latest substantive Oracle claim packet.
    """
    ok, reason = _pre_oracle_workup_status(slug)
    if not ok:
        return ok, reason
    target_dir = TARGETS_DIR / slug
    required = (
        "codex_workup.md",
        "next_oracle_question.md",
        "local_repair_report.md",
    )
    oldest_mtime = time.time()
    oldest_age = 0.0
    for name in required:
        path = target_dir / name
        try:
            stat = path.stat()
        except OSError:
            return False, f"missing {name}"
        oldest_mtime = min(oldest_mtime, stat.st_mtime)
        oldest_age = max(oldest_age, time.time() - stat.st_mtime)
    if oldest_age > max_age_seconds:
        return False, f"Codex handoff older than reuse window ({oldest_age:.0f}s > {max_age_seconds}s)"
    repair_started, repair_finished, repair_reason = _last_local_repair_window(slug)
    if repair_started is None or repair_finished is None:
        return False, repair_reason
    if oldest_mtime < repair_started - 2.0:
        return False, "Codex handoff files are older than last local repair start"
    latest_claim = _latest_substantive_claim_packet(target_dir)
    if latest_claim is not None and oldest_mtime < latest_claim.stat().st_mtime:
        return (
            False,
            "Codex handoff is older than latest substantive Oracle claim "
            f"({latest_claim.name}); Codex must locally replay/process that claim before the next Oracle turn",
        )
    if latest_claim is not None and repair_finished < latest_claim.stat().st_mtime:
        return (
            False,
            "last local repair completed before latest substantive Oracle claim "
            f"({latest_claim.name}); Codex must locally replay/process that claim before the next Oracle turn",
        )
    return True, ""


def _has_pre_oracle_workup(slug: str) -> bool:
    """Ensure the pre-Oracle Codex pass processed the target, not just metadata."""
    ok, _reason = _pre_oracle_workup_status(slug)
    return ok


def _path_contains_codex_transport_failure(log_path: str) -> bool:
    if not log_path:
        return False
    try:
        text = Path(log_path).read_text(encoding="utf-8", errors="replace").lower()
    except OSError:
        return False
    markers = (
        "failed to initialize in-process app-server client",
        "operation not permitted",
        "codex cli not found",
        "could not update path",
    )
    return any(marker in text for marker in markers)


def _note_global_codex_transport_backoff(*, reason: str, log_path: str = "") -> None:
    backoff_s = max(0, CODEX_TRANSPORT_BACKOFF_MINUTES) * 60
    backoff_until = _now() + backoff_s
    payload = {
        "ok": False,
        "transport_backoff": True,
        "reason": reason,
        "stderr_log": log_path,
        "recorded_at": _now_iso(),
        "backoff_until_epoch": backoff_until,
        "backoff_until": _iso_from_epoch(backoff_until),
        "backoff_minutes": CODEX_TRANSPORT_BACKOFF_MINUTES,
    }
    try:
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        CODEX_TRANSPORT_STATE.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    except OSError as exc:
        loop_log(f"failed to write global Codex transport backoff marker: {exc}")


def _global_codex_transport_backoff_applies() -> bool:
    try:
        state = json.loads(CODEX_TRANSPORT_STATE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    try:
        until = float(state.get("backoff_until_epoch") or 0.0)
    except (TypeError, ValueError):
        until = 0.0
    return _now() < until


def _path_contains_oracle_bridge_not_ready(log_path: str) -> bool:
    if not log_path:
        return False
    try:
        text = Path(log_path).read_text(encoding="utf-8", errors="replace").lower()
    except OSError:
        return False
    markers = (
        "bridge not ready",
        "bridge_not_ready",
        "no compatible outreach oracle tab",
        "queue_waiting_for_compatible_agent",
        "queue_waiting_for_project_agent",
    )
    return any(marker in text for marker in markers)


def _note_global_oracle_bridge_backoff(*, reason: str, log_path: str = "") -> None:
    backoff_s = max(0, TRANSPORT_FAILURE_BACKOFF_MINUTES) * 60
    backoff_until = _now() + backoff_s
    payload = {
        "ok": False,
        "bridge_backoff": True,
        "reason": reason,
        "stderr_log": log_path,
        "recorded_at": _now_iso(),
        "backoff_until_epoch": backoff_until,
        "backoff_until": _iso_from_epoch(backoff_until),
        "backoff_minutes": TRANSPORT_FAILURE_BACKOFF_MINUTES,
    }
    try:
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        ORACLE_BRIDGE_STATE.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    except OSError as exc:
        loop_log(f"failed to write global Oracle bridge backoff marker: {exc}")


def _global_oracle_bridge_backoff_applies() -> bool:
    try:
        state = json.loads(ORACLE_BRIDGE_STATE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    try:
        until = float(state.get("backoff_until_epoch") or 0.0)
    except (TypeError, ValueError):
        until = 0.0
    return _now() < until


def _read_local_repair_report(slug: str) -> dict:
    path = TARGETS_DIR / slug / "local_repair_last.json"
    try:
        report = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return report if isinstance(report, dict) else {}


def _local_repair_failure_kind(slug: str) -> str:
    report = _read_local_repair_report(slug)
    if report.get("ok") is True:
        return ""
    kind = str(report.get("failure_kind") or "")
    if kind:
        return kind
    if report.get("incomplete_handoff") is True:
        return "incomplete_handoff"
    if report.get("incomplete_handoff_watchdog", {}).get("triggered") is True:
        return "incomplete_handoff"
    if report.get("transport_failure") is True:
        return "codex_transport"
    return ""


def _local_repair_backoff_label(slug: str) -> str:
    kind = _local_repair_failure_kind(slug)
    if kind == "incomplete_handoff":
        return "Codex incomplete handoff"
    if kind == "codex_transport":
        return "Codex local-repair transport failure"
    return "Codex local-repair failure"


def _note_local_repair_backoff(slug: str, *, reason: str, log_path: str = "") -> None:
    target_dir = TARGETS_DIR / slug
    target_dir.mkdir(parents=True, exist_ok=True)
    path = target_dir / "local_repair_last.json"
    existing = _read_local_repair_report(slug)
    failure_kind = str(existing.get("failure_kind") or "")
    incomplete_handoff = bool(
        existing.get("incomplete_handoff") is True
        or existing.get("incomplete_handoff_watchdog", {}).get("triggered") is True
    )
    transport_failure = bool(existing.get("transport_failure") is True)
    if not failure_kind and incomplete_handoff:
        failure_kind = "incomplete_handoff"
    if not failure_kind and transport_failure:
        failure_kind = "codex_transport"
    if not failure_kind and _path_contains_codex_transport_failure(log_path):
        failure_kind = "codex_transport"
        transport_failure = True
    backoff_s = max(0, TRANSPORT_FAILURE_BACKOFF_MINUTES) * 60
    backoff_until = _now() + backoff_s
    payload = dict(existing) if existing else {}
    payload.update({
        "ok": False,
        "reason": reason,
        "stderr_log": log_path,
        "recorded_at": _now_iso(),
        "backoff_until_epoch": backoff_until,
        "backoff_until": datetime.fromtimestamp(backoff_until, timezone.utc).isoformat(timespec="seconds"),
        "backoff_minutes": TRANSPORT_FAILURE_BACKOFF_MINUTES,
    })
    if failure_kind:
        payload["failure_kind"] = failure_kind
    payload["incomplete_handoff"] = incomplete_handoff
    payload["transport_failure"] = transport_failure and failure_kind == "codex_transport"
    try:
        path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    except OSError as exc:
        loop_log(f"{slug}: failed to write local repair backoff marker: {exc}")
    if failure_kind == "codex_transport":
        _note_global_codex_transport_backoff(reason=reason, log_path=log_path)


def _reconcile_oracle_deep(todo_id: str) -> dict:
    """Consume any late/saved Oracle deep output for this target.

    The browser bridge can complete after dispatch_worktree timed out or after
    a retry/re-extract. Reconcile here immediately after each Oracle batch so
    the next science-gate decision sees the actual ChatGPT output plus any
    materialized FILE blocks.
    """
    if not ORACLE_RECONCILE.exists():
        return {}
    try:
        proc = subprocess.run(
            [
                "python3",
                str(ORACLE_RECONCILE),
                "--deep",
                "--todo-id",
                todo_id,
                "--json",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )
    except Exception as exc:  # noqa: BLE001
        loop_log(f"{todo_id}: oracle deep reconcile failed: {exc}")
        return {}
    if proc.returncode != 0:
        loop_log(f"{todo_id}: oracle deep reconcile rc={proc.returncode} {(proc.stderr or proc.stdout)[:300]}")
        return {}
    try:
        payload = json.loads(proc.stdout or "{}")
    except json.JSONDecodeError:
        loop_log(f"{todo_id}: oracle deep reconcile invalid json {(proc.stdout or '')[:300]}")
        return {}
    written = payload.get("written") or []
    if written:
        loop_log(
            f"{todo_id}: oracle deep reconcile wrote "
            + ", ".join(str(r.get("claim_packet") or r.get("source") or "?") for r in written)
        )
    return payload


def _reconcile_wrote_payload(payload: dict) -> bool:
    written = payload.get("written") if isinstance(payload, dict) else None
    return isinstance(written, list) and bool(written)


def _log_contains_transport_skip(log_path: str) -> bool:
    if not log_path:
        return False
    try:
        text = Path(log_path).read_text(encoding="utf-8", errors="replace")
    except OSError:
        return False
    lowered = text.lower()
    markers = (
        "[oracle-deep] server down",
        "[oracle] server down",
        "[oracle-deep] bridge not ready",
        "bridge_not_ready",
        "oracle-deep skipped",
        "stage=oracle_deep_skipped",
        "server unreachable",
        "failed to initialize in-process app-server client",
        "operation not permitted",
    )
    return any(marker in lowered for marker in markers)


def _note_transport_backoff(slug: str, *, reason: str, log_path: str = "") -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    path = STATE_DIR / f"{slug}.json"
    try:
        state = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        state = {}
    runs = state.setdefault("oracle_deep_runs", [])
    if not isinstance(runs, list):
        runs = []
        state["oracle_deep_runs"] = runs
    runs.append({
        "final_verdict": "FAILED",
        "transport_backoff": True,
        "reason": reason,
        "log_path": log_path,
        "recorded_at": _now_iso(),
        "turns": [{"error": reason, "response_chars": 0}],
    })
    path.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _oracle_deep_produced_payload(rc: int, log_path: str, reconcile_payload: dict) -> bool:
    if _reconcile_wrote_payload(reconcile_payload):
        return True
    if rc != 0:
        return False
    return not _log_contains_transport_skip(log_path)


def _run_local_followup_after_oracle(todo_id: str, rc: int, log_path: str, timeout_s: int) -> tuple[int, str]:
    local_rc, local_log = _spawn_local_repair(todo_id, timeout_s)
    loop_log(f"{todo_id}: Codex local follow-up after Oracle rc={local_rc} ({local_log})")
    if local_rc != 0 and rc == 0:
        return local_rc, local_log
    return rc, log_path


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
        "**Science gate pending** — review below only after the science gate reports WRITEBACK_READY or CLOSE_TARGET.",
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
        "3. If science_gate=WRITEBACK_READY → review the draft/note and approve or request edits.",
        "4. If science_gate=NEEDS_EVIDENCE → keep deepening or re-scope; do not ship.",
        "5. If science_gate=CLOSE_TARGET → review the closure rationale and archive/update the board.",
        "",
        "**Reminder**: this loop never sends anything; user approval is the gate.",
    ]
    p.write_text("\n".join(body_lines) + "\n", encoding="utf-8")
    return p


def _append_science_gate_summary(p: Path, gate: dict) -> None:
    try:
        with open(p, "a", encoding="utf-8") as f:
            f.write("\n## Science gate\n\n")
            f.write(f"- Status: `{gate.get('status', '')}`\n")
            f.write(f"- Next action: `{gate.get('next_action', '')}`\n")
            f.write(f"- Failure kind: `{gate.get('failure_kind', '')}`\n")
            f.write(f"- Retry budget: `{gate.get('retry_budget', 0)}`\n")
            f.write(f"- Closure status: `{gate.get('closure_status', '') or '-'}`\n")
            f.write(f"- Verification status: `{gate.get('verification_status', '') or '-'}`\n")
            f.write(f"- Outreach status: `{gate.get('outreach_status', '') or '-'}`\n")
            f.write(f"- Contribution type: `{gate.get('contribution_type', '') or '-'}`\n")
            f.write(f"- Terminal artifact: `{gate.get('terminal_artifact', '') or '-'}`\n")
            if gate.get("evidence_paths"):
                f.write("- Evidence paths:\n")
                for path in gate.get("evidence_paths") or []:
                    f.write(f"  - `{path}`\n")
            if gate.get("missing"):
                f.write("- Missing:\n")
                for item in gate.get("missing") or []:
                    f.write(f"  - {item}\n")
            if gate.get("reasons"):
                f.write("- Reasons:\n")
                for item in gate.get("reasons") or []:
                    f.write(f"  - {item}\n")
    except OSError as exc:
        loop_log(f"science gate summary append failed for {p}: {exc}")


def _append_impact_gate_summary(p: Path, gate: dict) -> None:
    try:
        with open(p, "a", encoding="utf-8") as f:
            f.write("\n## Outreach impact gate\n\n")
            f.write(f"- Status: `{gate.get('status', '')}`\n")
            f.write(f"- Primary channel: `{gate.get('primary_channel', '') or '-'}`\n")
            f.write(f"- Channels: `{', '.join(gate.get('channels') or []) or '-'}`\n")
            f.write(f"- Impact score: `{gate.get('impact_score', 0)}`\n")
            f.write(f"- Audience: `{gate.get('audience', '') or '-'}`\n")
            if gate.get("draft_paths"):
                f.write("- Draft/artifact paths:\n")
                for path in gate.get("draft_paths") or []:
                    f.write(f"  - `{path}`\n")
            if gate.get("required_before_send"):
                f.write("- Required before send/post:\n")
                for item in gate.get("required_before_send") or []:
                    f.write(f"  - {item}\n")
    except OSError as exc:
        loop_log(f"impact gate summary append failed for {p}: {exc}")


def _has_real_artifacts(slug: str) -> bool:
    """A T-NN target only earns 'Pending User Approval' once concrete
    artifacts exist on disk under targets/<slug>/. Avoids false-marking
    entries whose dispatch_worktree.supervisor_profile is empty (rc=0
    no-op) — those should stay Backlog.
    """
    target_dir = TARGETS_DIR / slug
    if not target_dir.exists():
        return False
    for name in (
        "research.md",
        "submission_draft.md",
        "submission_draft_final.md",
    ):
        p = target_dir / name
        try:
            if p.exists() and p.stat().st_size > 0:
                return True
        except OSError:
            continue
    # Any *_results.json or _results.md counts too (per gitignore patterns)
    for f in target_dir.glob("*_results.*"):
        try:
            if f.is_file() and f.stat().st_size > 0:
                return True
        except OSError:
            continue
    return False


def _artifact_digest(slug: str) -> str:
    """Digest the current target artifacts used for no-progress detection."""
    target_dir = TARGETS_DIR / slug
    h = hashlib.sha256()
    if not target_dir.exists():
        return ""
    for path in sorted(target_dir.glob("*")):
        if not path.is_file():
            continue
        if path.name in {
            "science_gate.json",
            "outreach_impact_gate.json",
            "local_repair_last.json",
        }:
            continue
        try:
            stat = path.stat()
            h.update(path.name.encode("utf-8"))
            h.update(str(stat.st_size).encode("ascii"))
            h.update(path.read_bytes()[:200000])
        except OSError:
            continue
    return h.hexdigest()


def _state_path(slug: str) -> Path:
    return STATE_DIR / f"{slug}.research_loop.json"


def _read_loop_state(slug: str) -> dict:
    try:
        return json.loads(_state_path(slug).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def _write_loop_state(slug: str, state: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    _state_path(slug).write_text(
        json.dumps(state, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def _no_progress_patience(slug: str) -> int:
    profile, _ = load_profile(slug)
    contract = profile.science_contract if profile is not None else None
    try:
        n = int(getattr(contract, "no_progress_patience_turns", 2) or 2)
    except (TypeError, ValueError):
        n = 2
    return max(1, n)


def _record_progress_after_batch(slug: str, gate_status: str) -> dict:
    digest = _artifact_digest(slug)
    state = _read_loop_state(slug)
    previous = str(state.get("artifact_digest") or "")
    no_progress = int(state.get("no_progress_batches") or 0)
    if digest and digest == previous and gate_status not in {WRITEBACK_READY, CLOSE_TARGET}:
        no_progress += 1
    else:
        no_progress = 0
    state.update({
        "updated_at": _now_iso(),
        "artifact_digest": digest,
        "last_gate_status": gate_status,
        "no_progress_batches": no_progress,
        "no_progress_patience": _no_progress_patience(slug),
    })
    _write_loop_state(slug, state)
    return state


def _latest_oracle_transport_failure(slug: str) -> bool:
    path = STATE_DIR / f"{slug}.json"
    try:
        state = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    runs = state.get("oracle_deep_runs") or []
    if not isinstance(runs, list) or not runs:
        return False
    latest = runs[-1]
    if not isinstance(latest, dict):
        return False
    if str(latest.get("final_verdict") or "").upper() != "FAILED":
        return False
    turns = latest.get("turns") or []
    if not isinstance(turns, list) or not turns:
        return True
    for turn in turns:
        if not isinstance(turn, dict):
            continue
        err = str(turn.get("error") or "").lower()
        chars = int(turn.get("response_chars") or 0)
        if chars > 500:
            return False
        if any(marker in err for marker in ("empty response", "timeout", "extraction", "transport", "cancel")):
            return True
    return False


def _transport_backoff_applies(slug: str) -> bool:
    if not _latest_oracle_transport_failure(slug):
        return False
    path = STATE_DIR / f"{slug}.json"
    try:
        age = _now() - path.stat().st_mtime
    except OSError:
        return False
    return age < max(0, TRANSPORT_FAILURE_BACKOFF_MINUTES) * 60


def _local_repair_transport_failure(slug: str) -> bool:
    report = _read_local_repair_report(slug)
    if report.get("ok") is True:
        return False
    if _local_repair_failure_kind(slug) == "incomplete_handoff":
        return False
    if report.get("transport_failure") is True:
        return True
    stderr_log = str(report.get("stderr_log") or "")
    if not stderr_log:
        return False
    return _path_contains_codex_transport_failure(stderr_log)


def _local_repair_backoff_applies(slug: str) -> bool:
    path = TARGETS_DIR / slug / "local_repair_last.json"
    try:
        report = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    if report.get("ok") is True:
        return False
    try:
        until = float(report.get("backoff_until_epoch") or 0.0)
    except (TypeError, ValueError):
        until = 0.0
    if until > _now():
        return True
    if not _local_repair_transport_failure(slug):
        return False
    try:
        age = _now() - path.stat().st_mtime
    except OSError:
        return False
    return age < max(0, TRANSPORT_FAILURE_BACKOFF_MINUTES) * 60


def process_one(todo_id: str, slug: str, *, timeout_s: int) -> dict:
    """Claim → dispatch → write summary → mark board (only if real work
    happened) → release."""
    started = _now()
    if _live_worker_for_target(todo_id, slug):
        loop_log(f"{todo_id}: live worker already active for {slug}; skipping duplicate claim")
        return {"todo_id": todo_id, "slug": slug, "skipped": "live_worker_active"}
    if not claim(slug):
        return {"todo_id": todo_id, "slug": slug, "skipped": "already_claimed"}
    try:
        todos = _parse_board_safe()
        science_gate = science_gate_evaluate(todos[todo_id]) if todo_id in todos else None
        if science_gate is not None and science_gate.status in {WRITEBACK_READY, CLOSE_TARGET}:
            rc = 0
            log_path = f"science_gate_precheck:{science_gate.status}"
            summary_path = _write_summary(todo_id, slug, rc, log_path)
            _append_science_gate_summary(summary_path, science_gate.to_dict())
            impact_gate = None
            if todo_id in todos:
                try:
                    impact_gate = impact_gate_evaluate(todos[todo_id])
                    write_impact_ledger(impact_gate)
                    _append_impact_gate_summary(summary_path, impact_gate.to_dict())
                except Exception as exc:
                    loop_log(f"{todo_id}: impact_gate failed: {exc}")
            progress_state = _record_progress_after_batch(slug, science_gate.status)
            marked = False
            if impact_gate is not None and _impact_allows_operator_review(impact_gate):
                loop_log(
                    f"{todo_id}: science_gate={science_gate.status}; "
                    f"impact_gate={impact_gate.status}; routing to operator review"
                )
            else:
                impact_status = getattr(impact_gate, "status", "unknown") if impact_gate is not None else "unknown"
                loop_log(
                    f"{todo_id}: science_gate={science_gate.status} but impact_gate={impact_status}; "
                    "not surfacing as ready because this is not yet a real publishable math result"
                )
            if (
                _has_real_artifacts(slug)
                and impact_gate is not None
                and _impact_allows_operator_review(impact_gate)
            ):
                marked = mark_pending_user_approval(
                    todo_id,
                    note=f"rc={rc} · science_gate={science_gate.status} · impact_gate={impact_gate.status}",
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
                "science_gate": science_gate.to_dict(),
                "impact_gate": impact_gate.to_dict() if impact_gate is not None else {},
                "progress_state": progress_state,
            }
        loop_log(f"claimed {todo_id} ({slug}); dispatching --supervise")
        rc, log_path = _spawn_supervise(todo_id, timeout_s)
        loop_log(f"{todo_id}: dispatch_worktree --supervise rc={rc} ({log_path})")
        # Late ChatGPT results often arrive via retry/re-extract after the
        # previous subprocess already timed out. Consume them before deciding
        # whether this target needs another Oracle turn.
        _reconcile_oracle_deep(todo_id)
        todos = _parse_board_safe()
        science_gate = None
        if todo_id in todos:
            science_gate = science_gate_evaluate(todos[todo_id])
        if (
            rc == 0
            and science_gate is not None
            and science_gate.next_action == "deep_reason"
        ):
            gate_missing = list(science_gate.to_dict().get("missing") or [])
            if _missing_requires_local_repair(gate_missing):
                loop_log(
                    f"{todo_id}: science_gate needs local replay/verifier repair; "
                    "dispatching Codex local_repair before any further Oracle turn"
                )
                repair_started = _now()
                rc, log_path = _spawn_local_repair(todo_id, timeout_s)
                loop_log(f"{todo_id}: outreach_local_repair rc={rc} ({log_path})")
                todos = _parse_board_safe()
                if todo_id in todos:
                    science_gate = science_gate_evaluate(todos[todo_id])
                    gate_missing = list(science_gate.to_dict().get("missing") or [])
                if (
                    rc == 0
                    and science_gate is not None
                    and science_gate.next_action == "deep_reason"
                    and not _missing_requires_local_repair(gate_missing)
                ):
                    loop_log(
                        f"{todo_id}: local repair cleared replay/verifier blockers; "
                        "checking Codex-selected next Oracle task before proof/closure"
                    )
                    workup_ok, workup_reason = _pre_oracle_workup_fresh_after(slug, repair_started)
                    if not workup_ok:
                        rc, log_path = 2, log_path
                        _note_local_repair_backoff(
                            slug,
                            reason=(
                                "local repair cleared replay/verifier blockers but did not produce "
                                f"a usable pre-Oracle Codex workup: {workup_reason}"
                            ),
                            log_path=log_path,
                        )
                        loop_log(
                            f"{todo_id}: local repair did not leave a usable pre-Oracle Codex workup "
                            f"({workup_reason}); not asking Oracle from a generic prompt"
                        )
                    else:
                        rc, log_path = _spawn_oracle_deep(todo_id, timeout_s)
                        loop_log(f"{todo_id}: dispatch_worktree --oracle-deep rc={rc} ({log_path})")
                        reconcile_payload = _reconcile_oracle_deep(todo_id)
                        if _oracle_deep_produced_payload(rc, log_path, reconcile_payload):
                            rc, log_path = _run_local_followup_after_oracle(todo_id, rc, log_path, timeout_s)
                        else:
                            if _path_contains_oracle_bridge_not_ready(log_path):
                                _note_global_oracle_bridge_backoff(
                                    reason=f"oracle bridge not ready for {todo_id}",
                                    log_path=log_path,
                                )
                            _note_transport_backoff(
                                slug,
                                reason=f"oracle-deep transport/no-payload rc={rc}",
                                log_path=log_path,
                            )
                            loop_log(
                                f"{todo_id}: oracle-deep produced no usable payload; "
                                f"backing off {TRANSPORT_FAILURE_BACKOFF_MINUTES}min instead of local repair"
                            )
            else:
                reuse_ok, reuse_reason = _pre_oracle_workup_recent(
                    slug,
                    max_age_seconds=max(900, int(timeout_s)),
                )
                if reuse_ok:
                    loop_log(
                        f"{todo_id}: reusing fresh Codex local workup for oracle-deep; "
                        "not rerunning local repair"
                    )
                    workup_rc, workup_log = 0, log_path
                    workup_ok, workup_reason = True, ""
                else:
                    loop_log(
                        f"{todo_id}: science_gate.next_action=deep_reason"
                        f"{' after local supervisor produced no artifact' if not _has_real_artifacts(slug) else ''}; "
                        f"running Codex workup before oracle-deep ({reuse_reason})"
                    )
                    workup_rc, workup_log = _run_codex_workup_before_oracle(todo_id, slug, timeout_s)
                    if workup_rc != 0:
                        rc, log_path = workup_rc, workup_log
                        loop_log(
                            f"{todo_id}: pre-Oracle Codex workup failed; "
                            "not asking Oracle from an unprocessed board card"
                        )
                    else:
                        workup_ok, workup_reason = _pre_oracle_workup_status(slug)
                if workup_rc == 0 and not workup_ok:
                    rc, log_path = 2, workup_log
                    _note_local_repair_backoff(
                        slug,
                        reason=f"pre-oracle codex workup unusable: {workup_reason}",
                        log_path=workup_log,
                    )
                    loop_log(
                        f"{todo_id}: pre-Oracle Codex workup unusable ({workup_reason}); "
                        "not asking Oracle from a generic/unprocessed prompt"
                    )
                elif workup_rc == 0:
                    rc, log_path = _spawn_oracle_deep(todo_id, timeout_s)
                    loop_log(f"{todo_id}: dispatch_worktree --oracle-deep rc={rc} ({log_path})")
                    reconcile_payload = _reconcile_oracle_deep(todo_id)
                    if _oracle_deep_produced_payload(rc, log_path, reconcile_payload):
                        rc, log_path = _run_local_followup_after_oracle(todo_id, rc, log_path, timeout_s)
                    else:
                        if _path_contains_oracle_bridge_not_ready(log_path):
                            _note_global_oracle_bridge_backoff(
                                reason=f"oracle bridge not ready for {todo_id}",
                                log_path=log_path,
                            )
                        _note_transport_backoff(
                            slug,
                            reason=f"oracle-deep transport/no-payload rc={rc}",
                            log_path=log_path,
                        )
                        loop_log(
                            f"{todo_id}: oracle-deep produced no usable payload; "
                            f"backing off {TRANSPORT_FAILURE_BACKOFF_MINUTES}min instead of local repair"
                        )
            todos = _parse_board_safe()
            if todo_id in todos:
                science_gate = science_gate_evaluate(todos[todo_id])
        summary_path = _write_summary(todo_id, slug, rc, log_path)
        if science_gate is not None:
            _append_science_gate_summary(summary_path, science_gate.to_dict())
        impact_gate = None
        if todo_id in todos:
            try:
                impact_gate = impact_gate_evaluate(todos[todo_id])
                write_impact_ledger(impact_gate)
                _append_impact_gate_summary(summary_path, impact_gate.to_dict())
            except Exception as exc:
                loop_log(f"{todo_id}: impact_gate failed: {exc}")
        progress_state = _record_progress_after_batch(
            slug,
            science_gate.status if science_gate is not None else "unknown",
        )
        # Only mark Pending User Approval when concrete artifacts landed and
        # impact_gate agrees this is worth operator/public review.  Empty
        # supervisor_profiles and low-value bounded/audit packets must not
        # interrupt the user as "ready" mathematical contributions.
        marked = False
        gate_status = science_gate.status if science_gate is not None else ""
        impact_ready = impact_gate is not None and _impact_allows_operator_review(impact_gate)
        if _has_real_artifacts(slug) and gate_status in {WRITEBACK_READY, CLOSE_TARGET} and impact_ready:
            marked = mark_pending_user_approval(
                todo_id,
                note=f"rc={rc} · science_gate={gate_status} · impact_gate={impact_gate.status}",
            )
        elif gate_status in {WRITEBACK_READY, CLOSE_TARGET} and not impact_ready:
            impact_status = getattr(impact_gate, "status", "unknown") if impact_gate is not None else "unknown"
            loop_log(
                f"{todo_id}: science_gate={gate_status} but impact_gate={impact_status}; "
                "continuing/deprioritizing instead of marking Pending User Approval"
            )
        else:
            loop_log(
                f"{todo_id}: not marking — "
                f"{'no artifacts under targets/' + slug + '/' if rc == 0 and not _has_real_artifacts(slug) else f'rc={rc}'} "
                f"science_gate={gate_status or 'unknown'} "
                f"no_progress_batches={progress_state.get('no_progress_batches')}/"
                f"{progress_state.get('no_progress_patience')}"
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
            "science_gate": science_gate.to_dict() if science_gate is not None else {},
            "impact_gate": impact_gate.to_dict() if impact_gate is not None else {},
            "progress_state": progress_state,
        }
    finally:
        release(slug)


# ---------------------------------------------------------------------------
# selection policy
# ---------------------------------------------------------------------------


def _is_problemsilike_target(todo) -> bool:
    return bool(re.search(r"https?://(?:www\.)?problemsilike\.com/\d+", getattr(todo, "source", "") or "", re.I))


def _problemsilike_problem_id(todo) -> int:
    m = re.search(r"problemsilike\.com/(\d+)", getattr(todo, "source", "") or "", re.I)
    if not m:
        return 10**9
    try:
        return int(m.group(1))
    except ValueError:
        return 10**9


def _target_has_completed_initial_harness_cycle(slug: str) -> bool:
    """Best-effort local marker for source -> Oracle -> local replay completion.

    This intentionally checks only local bytes.  A target counts as having had
    a first full cycle only after it has local workup/replay artifacts, a next
    Oracle question, and an Oracle claim packet in the target directory.
    """
    target_dir = TARGETS_DIR / slug
    required = (
        target_dir / "research.md",
        target_dir / "results.json",
        target_dir / "next_oracle_question.md",
        target_dir / "local_repair_last.json",
    )
    if not all(p.exists() and p.stat().st_size > 0 for p in required):
        return False
    return any(p.is_file() and p.stat().st_size > 0 for p in target_dir.glob("oracle_claim_packet*.md"))


def _selection_priority(item) -> tuple[int, int, int, str]:
    """Sort key for research target selection.

    Problems I Like is a curated high-impact source and is currently hot.  OPEN
    entries should be consumed before lower-yield frontier churn, especially
    before repeatedly revisiting targets that have already produced only
    NEEDS_EVIDENCE artifacts.  Science and impact gates still decide readiness;
    this only chooses the next internal math-lane target.
    """
    _, t = item
    topic = getattr(t, "topic_score", None) or 0
    fit = getattr(t, "fit_score", None) or 0
    if _is_problemsilike_target(t) and not _is_skipped(getattr(t, "status", "") or ""):
        problem_id = _problemsilike_problem_id(t)
        slug = t.slug()
        if not _target_has_completed_initial_harness_cycle(slug):
            return (0, problem_id, -(topic + fit), t.todo_id)
        return (1, problem_id, -(topic + fit), t.todo_id)
    return (2, 10**9, -(topic + fit), t.todo_id)


def select_next_target(skip_slugs: set[str] | None = None) -> Optional[tuple[str, str]]:
    """Return (todo_id, slug) of the next actionable target, or None."""
    skip_slugs = skip_slugs or set()
    if _global_oracle_bridge_backoff_applies():
        return None
    todos = _parse_board_safe()
    if not todos:
        return None
    for tid, todo in sorted(todos.items(), key=_selection_priority):
        status = getattr(todo, "status", "") or ""
        if _is_skipped(status):
            continue
        preflight = judge(todo)
        if preflight.verdict not in ACTIONABLE_VERDICTS:
            loop_log(
                f"{tid}: preflight skip verdict={preflight.verdict} "
                f"missing={'; '.join(preflight.missing) or '-'}"
            )
            continue
        try:
            gate = science_gate_evaluate(todo)
            if gate.next_action in {"deep_reason", "profile_judge"}:
                # These are runnable repair/deepening states.  Do not let a
                # stale impact-gate ledger or prior archive wording mask the
                # science gate; the loop should keep improving evidence until
                # science_gate itself reaches an operator terminal action.
                pass
            elif gate.status == WRITEBACK_READY:
                impact = impact_gate_evaluate(todo)
                write_impact_ledger(impact)
                if _impact_allows_operator_review(impact):
                    loop_log(
                        f"{tid}: science_gate=WRITEBACK_READY; "
                        f"impact primary={impact.primary_channel} channels={','.join(impact.channels) or '-'}; "
                        "waiting for operator review"
                    )
                else:
                    loop_log(
                        f"{tid}: science_gate=WRITEBACK_READY but impact_gate={impact.status}; "
                        "not treating bounded/audit output as a real result"
                    )
                continue
            elif gate.status == CLOSE_TARGET:
                impact = impact_gate_evaluate(todo)
                write_impact_ledger(impact)
                if _impact_allows_operator_review(impact):
                    loop_log(f"{tid}: science_gate=CLOSE_TARGET; waiting for operator archive review")
                else:
                    loop_log(
                        f"{tid}: science_gate=CLOSE_TARGET but impact_gate={impact.status}; "
                        "not surfacing low-value closure as ready"
                    )
                continue
            else:
                terminal_next_actions = {
                    "operator_review",
                    "operator_archive_review",
                    "skip",
                    "hold",
                }
                if gate.next_action in terminal_next_actions:
                    loop_log(
                        f"{tid}: science_gate={gate.status} next_action={gate.next_action}; "
                        "waiting for operator/gate transition"
                    )
                    continue
        except Exception as exc:
            loop_log(f"{tid}: gate precheck failed, continuing selection cautiously: {exc}")
        slug = todo.slug()
        if slug in skip_slugs:
            continue
        if _claim_marker(slug).exists():
            continue
        if _cooldown_applies(tid, slug, SUMMARY_COOLDOWN_HOURS):
            continue
        if _transport_backoff_applies(slug):
            loop_log(
                f"{tid}: recent Oracle transport/extraction failure; "
                f"backing off {TRANSPORT_FAILURE_BACKOFF_MINUTES}min and trying another target"
            )
            continue
        if _local_repair_backoff_applies(slug):
            loop_log(
                f"{tid}: recent {_local_repair_backoff_label(slug)}; "
                f"backing off {TRANSPORT_FAILURE_BACKOFF_MINUTES}min and trying another target"
            )
            continue
        return tid, slug
    return None


def _blocked_snapshot(limit: int = 8) -> list[dict]:
    todos = _parse_board_safe()
    rows: list[dict] = []
    for tid, todo in todos.items():
        if _global_codex_transport_backoff_applies() or _global_oracle_bridge_backoff_applies():
            return []
        status = getattr(todo, "status", "") or ""
        if _is_skipped(status):
            continue
        try:
            preflight = judge(todo)
        except Exception as exc:  # noqa: BLE001
            rows.append({
                "todo_id": tid,
                "slug": todo.slug(),
                "verdict": "ERROR",
                "score": 0,
                "missing": [str(exc)[:160]],
            })
            continue
        if preflight.verdict in ACTIONABLE_VERDICTS:
            continue
        rows.append({
            "todo_id": tid,
            "slug": preflight.slug,
            "title": preflight.title,
            "verdict": preflight.verdict,
            "score": preflight.score,
            "missing": list(preflight.missing or [])[:4],
            "risks": list(preflight.risk_flags or [])[:4],
        })
    rows.sort(key=lambda r: (-int(r.get("score") or 0), str(r.get("todo_id") or "")))
    return rows[:limit]


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


def _visible_active_rows(active: dict[concurrent.futures.Future, tuple[str, str]]) -> list[dict]:
    """Return active rows for status, hiding targets already gate-terminal.

    A worker can be finishing stale local repair or summary work after another
    harness component has moved the target to WRITEBACK_READY/CLOSE_TARGET.
    Status consumers should not read that as "still researching this target";
    otherwise the watchdog/operator view keeps reporting a solved local loop
    as active work and blocks attention from the next target.
    """
    todos = _parse_board_safe()
    rows: list[dict] = []
    for tid, slug in active.values():
        todo = todos.get(tid)
        if todo is not None:
            try:
                gate = science_gate_evaluate(todo)
                if gate.status in {WRITEBACK_READY, CLOSE_TARGET}:
                    continue
            except Exception:
                pass
        rows.append({"todo_id": tid, "slug": slug})
    return rows


def _install_signal_handlers(stop_flag: dict) -> None:
    def _handler(signum, frame):
        stop_flag["stop"] = True

    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            signal.signal(sig, _handler)
        except (OSError, ValueError):
            pass


def _acquire_loop_lock():
    """Acquire a process-level singleton lock for loop mode.

    Supervisor restarts can leave an old research_loop orphaned while spawning
    a new one. Without a lock, both loops race the same board and can dispatch
    unrelated targets. The lock is advisory and automatically releases on
    process exit.
    """
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    fd = os.open(str(RESEARCH_LOOP_LOCK), os.O_CREAT | os.O_RDWR, 0o644)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        os.close(fd)
        return None
    os.ftruncate(fd, 0)
    os.write(fd, f"pid={os.getpid()}\nstarted_at={_now_iso()}\n".encode("utf-8"))
    return fd


def _collect_finished(
    active: dict[concurrent.futures.Future, tuple[str, str]],
    *,
    block: bool = False,
    poll_interval: int = DEFAULT_POLL_INTERVAL,
) -> list[dict]:
    if not active:
        return []
    done: set[concurrent.futures.Future] = set()
    if block:
        done, _ = concurrent.futures.wait(
            active.keys(),
            timeout=poll_interval,
            return_when=concurrent.futures.FIRST_COMPLETED,
        )
    else:
        done = {f for f in active if f.done()}
    results: list[dict] = []
    for future in done:
        todo_id, slug = active.pop(future)
        try:
            result = future.result()
        except Exception as exc:  # noqa: BLE001
            result = {"todo_id": todo_id, "slug": slug, "error": str(exc)}
            loop_log(f"{todo_id}: worker exception: {exc}")
        loop_log(f"{todo_id} result: {result}")
        _write_status({
            "last_completed": _now_iso(),
            "result": result,
            "active": _visible_active_rows(active),
        })
        results.append(result)
    return results


def _run_parallel_loop(args: argparse.Namespace, stop_flag: dict) -> int:
    max_workers = max(1, int(args.parallel or 1))
    oracle_refill_reserve = max(0, int(getattr(args, "oracle_refill_reserve", DEFAULT_ORACLE_REFILL_RESERVE) or 0))
    research_workers = max(1, max_workers - oracle_refill_reserve)
    if research_workers != max_workers:
        loop_log(
            f"parallel={max_workers} with oracle_refill_reserve={oracle_refill_reserve}; "
            f"research workers={research_workers}"
        )
    active: dict[concurrent.futures.Future, tuple[str, str]] = {}
    iteration = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=research_workers) as executor:
        while not stop_flag["stop"]:
            iteration += 1
            cleanup_stale_claims()
            _collect_finished(active)

            started_any = False
            codex_transport_paused = False
            oracle_bridge_paused = False
            while not stop_flag["stop"] and len(active) < research_workers:
                if _global_codex_transport_backoff_applies():
                    codex_transport_paused = True
                    break
                if _global_oracle_bridge_backoff_applies():
                    oracle_bridge_paused = True
                    break
                skip_slugs = {slug for _, slug in active.values()}
                if args.todo_id:
                    if active:
                        break
                    todos = _parse_board_safe()
                    todo = todos.get(args.todo_id)
                    if todo is None:
                        loop_log(f"--todo-id {args.todo_id} not found on board, exiting")
                        return 1
                    slug = todo.slug()
                    if _is_skipped(getattr(todo, "status", "") or ""):
                        loop_log(f"{args.todo_id} status indicates skip; exiting")
                        return 1
                    preflight = judge(todo)
                    if preflight.verdict not in ACTIONABLE_VERDICTS:
                        loop_log(
                            f"{args.todo_id} preflight blocks run: "
                            f"verdict={preflight.verdict} "
                            f"missing={'; '.join(preflight.missing) or '-'} "
                            f"reasons={'; '.join(preflight.reasons) or '-'}"
                        )
                        return 1
                    picked: Optional[tuple[str, str]] = (args.todo_id, slug)
                else:
                    picked = select_next_target(skip_slugs=skip_slugs)

                if picked is None:
                    break

                todo_id, slug = picked
                loop_log(f"iter={iteration} picked {todo_id} ({slug})")
                future = executor.submit(process_one, todo_id, slug, timeout_s=args.target_timeout_s)
                active[future] = (todo_id, slug)
                started_any = True

                if args.once:
                    break
                if args.todo_id:
                    break

            _write_status({
                "iter": iteration,
                "last_poll": _now_iso(),
                "active": _visible_active_rows(active),
                "blocked_top": _blocked_snapshot(),
                "parallel": max_workers,
                "research_workers": research_workers,
                "oracle_refill_reserve": oracle_refill_reserve,
                "codex_transport_paused": codex_transport_paused,
                "oracle_bridge_paused": oracle_bridge_paused,
            })

            if args.once:
                if active:
                    _collect_finished(active, block=True, poll_interval=args.target_timeout_s)
                return 0

            if not active and not started_any:
                if codex_transport_paused:
                    loop_log(
                        f"Codex local-repair transport backoff active; "
                        f"pausing target selection for {CODEX_TRANSPORT_BACKOFF_MINUTES}min"
                    )
                elif oracle_bridge_paused:
                    loop_log(
                        f"Oracle bridge backoff active; "
                        f"pausing target selection for {TRANSPORT_FAILURE_BACKOFF_MINUTES}min"
                    )
                else:
                    loop_log(f"no actionable target this poll (iter={iteration})")
                time.sleep(args.poll_interval)
                continue

            if active:
                _collect_finished(active, block=True, poll_interval=args.poll_interval)

        if active:
            loop_log(f"research_loop stop requested; waiting for {len(active)} active worker(s) to finish current subprocess")
            concurrent.futures.wait(active.keys())
            _collect_finished(active)
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--loop", action="store_true",
                   help="run continuously, polling for next actionable target")
    p.add_argument("--once", action="store_true",
                   help="select one actionable target, run it, exit")
    p.add_argument("--todo-id", default="",
                   help="explicit T-NN to run (forces selection); use with --once")
    p.add_argument("--parallel", type=int, default=DEFAULT_PARALLEL,
                   help=f"max concurrent targets (default {DEFAULT_PARALLEL})")
    p.add_argument("--oracle-refill-reserve", type=int, default=DEFAULT_ORACLE_REFILL_RESERVE,
                   help="reserve this many Oracle browser lanes for board refill / recovery tasks")
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

    loop_lock_fd = None
    if args.loop and not args.todo_id:
        loop_lock_fd = _acquire_loop_lock()
        if loop_lock_fd is None:
            loop_log("another research_loop instance already holds the singleton lock; exiting")
            return 0

    stop_flag: dict = {"stop": False}
    _install_signal_handlers(stop_flag)

    loop_log(
        f"research_loop starting "
        f"(loop={args.loop} once={args.once} todo_id={args.todo_id or 'auto'} "
        f"parallel={args.parallel} oracle_refill_reserve={args.oracle_refill_reserve} "
        f"timeout={args.target_timeout_s}s)"
    )

    if args.parallel > 1:
        return _run_parallel_loop(args, stop_flag)

    iteration = 0
    while not stop_flag["stop"]:
        iteration += 1

        cleanup_stale_claims()

        # Pick target.
        if _global_oracle_bridge_backoff_applies():
            loop_log(
                f"Oracle bridge backoff active; "
                f"pausing target selection for {TRANSPORT_FAILURE_BACKOFF_MINUTES}min"
            )
            _write_status({
                "iter": iteration,
                "last_poll": _now_iso(),
                "picked": None,
                "oracle_bridge_paused": True,
            })
            if args.once:
                return 0
            time.sleep(args.poll_interval)
            continue
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
            preflight = judge(todo)
            if preflight.verdict not in ACTIONABLE_VERDICTS:
                loop_log(
                    f"{args.todo_id} preflight blocks run: "
                    f"verdict={preflight.verdict} "
                    f"missing={'; '.join(preflight.missing) or '-'} "
                    f"reasons={'; '.join(preflight.reasons) or '-'}"
                )
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
