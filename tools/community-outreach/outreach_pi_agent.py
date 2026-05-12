#!/usr/bin/env python3
"""Outreach pipeline PI agent — bounded operator action plan from a Claude consultation.

Mirrors tools/bedc-deep/pi_agent.py for the community-outreach domain. The
supervisor calls this; the PI agent receives a snapshot of the live pipeline
(OUTREACH_LOG, per-target state, Apple Mail Sent/Drafts, drafts/ folder,
RESEARCH_BOARD active rows, recent commits, supervisor tail), asks Claude for
an action plan, and applies the autonomous subset directly. Risky moves land
in .outreach_human_inbox.md.

Hard boundaries enforced both in the prompt AND here:
- never edits drafts/ files
- never sends external messages (Mail / X / forum)
- never edits OUTREACH_LOG.md or RESEARCH_BOARD.md content beyond the single
  canonical mark_target_stale path
- never edits lean4/ or papers/

State written:
  outreach_state/pi_journal.jsonl       one line per cycle
  outreach_state/concern_counts.json    persisted concern counter
  .outreach_human_inbox.md              actionable suggestions for the operator
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_DIR = SCRIPT_DIR / "outreach_state"
PROMPT_PATH = SCRIPT_DIR / "prompts" / "outreach_pi_agent.txt"
OPERATOR_MEMORY_PATH = SCRIPT_DIR / "OPERATOR_MEMORY.md"
SUPERVISOR_LOG_DIR = STATE_DIR / "supervisor_logs"
SUPERVISOR_LOG = SUPERVISOR_LOG_DIR / "supervisor.log"
PI_JOURNAL = STATE_DIR / "pi_journal.jsonl"
CONCERN_COUNTS_PATH = STATE_DIR / "concern_counts.json"
HUMAN_INBOX = SCRIPT_DIR / ".outreach_human_inbox.md"
OUTREACH_LOG = SCRIPT_DIR / "OUTREACH_LOG.md"
RESEARCH_BOARD = SCRIPT_DIR / "RESEARCH_BOARD.md"
DRAFTS_DIR = SCRIPT_DIR / "drafts"
TARGETS_DIR = SCRIPT_DIR / "targets"

ORACLE_SERVER_URL = "http://localhost:8766"
CLAUDE_PATH = shutil.which("claude") or "/opt/homebrew/bin/claude"

ESCALATE_AFTER_REPEATS = 2
PI_TIMEOUT_S = 1200

ALLOWED_AUTONOMOUS = {
    "run_arxiv_watch",
    "run_lit_staleness",
    "run_inbox_watcher",
    "run_profile_judge",
    "mark_target_stale",
    "adjust_cooldown",
    "restart_inner",
    # 2026-05-09: bounded task-state mutations so PI can self-iterate on dead
    # tasks without the operator having to step in for every retry exhaustion.
    "revive_task",        # rejected → pending + retries=0 (with optional context tweaks)
    "reroute_task",       # flip context.use_oracle to escape a stuck deep-reason path
}
ALLOWED_INBOX = {
    "send_drafted_email",
    "post_to_x",
    "post_to_forum",
    "follow_up_target",
    "add_target",
    "cancel_target",
    "change_priority",
    "prompt_repair",
    "endorser_search",
    "other",
}


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _safe(text: str) -> str:
    return (text or "").replace("{", "{{").replace("}", "}}")


def _read_tail(path: Path, n: int = 30) -> str:
    if not path.exists():
        return "(file not present)"
    try:
        return "\n".join(path.read_text(encoding="utf-8").splitlines()[-n:])
    except OSError:
        return "(could not read)"


def _server_status() -> dict:
    try:
        with urllib.request.urlopen(f"{ORACLE_SERVER_URL}/status", timeout=3) as r:
            return json.loads(r.read().decode("utf-8"), strict=False)
    except Exception as exc:
        return {"_error": str(exc)}


# ---------------------------------------------------------------------------
# snapshot collectors
# ---------------------------------------------------------------------------


_OUTREACH_ROW_RE = re.compile(r"^\|([^|]+)\|([^|]+)\|([^|]+)\|([^|]+)\|([^|]+)\|([^|]+)\|\s*$")


def _parse_outreach_log() -> dict:
    if not OUTREACH_LOG.exists():
        return {"active": [], "completed_count": 0, "pending_review_count": 0}
    text = OUTREACH_LOG.read_text(encoding="utf-8")
    sections: dict[str, list[str]] = {}
    current = None
    for line in text.splitlines():
        if line.startswith("## "):
            current = line[3:].strip()
            sections[current] = []
        elif current is not None:
            sections[current].append(line)

    def _rows(lines: list[str]) -> list[dict]:
        out: list[dict] = []
        for ln in lines:
            m = _OUTREACH_ROW_RE.match(ln)
            if not m:
                continue
            cells = [c.strip() for c in m.groups()]
            if cells[0].lower() in ("target", "---") or set(cells[0]) <= {"-", " "}:
                continue
            out.append({
                "target": cells[0],
                "channel": cells[1],
                "status": cells[2],
                "backflow": cells[3],
                "best_score": cells[4],
                "last_update": cells[5],
            })
        return out

    return {
        "active": _rows(sections.get("Active Targets", [])),
        "completed_count": len(_rows(sections.get("Completed", []))),
        "pending_review_count": len(_rows(sections.get("Pending Claude Review", []))),
    }


def _state_summary(limit: int = 40) -> dict:
    if not STATE_DIR.exists():
        return {"rows": [], "histogram": {}}
    rows: list[dict] = []
    histogram: dict[str, int] = {}
    for f in sorted(STATE_DIR.glob("*.json"))[:limit]:
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        status = d.get("status") or d.get("stage") or "unknown"
        histogram[status] = histogram.get(status, 0) + 1
        rows.append({
            "file": f.name,
            "status": status,
            "score": d.get("best_score") or d.get("score"),
            "stage": d.get("stage"),
            "last_update": d.get("last_update") or d.get("updated_at"),
        })
    return {"rows": rows, "histogram": histogram}


def _drafts_listing() -> list[dict]:
    if not DRAFTS_DIR.exists():
        return []
    out: list[dict] = []
    cutoff_days = 60
    now = datetime.now(timezone.utc).timestamp()
    for p in DRAFTS_DIR.iterdir():
        if not p.is_file():
            continue
        try:
            mtime = p.stat().st_mtime
        except OSError:
            continue
        age_days = (now - mtime) / 86400.0
        if age_days > cutoff_days:
            continue
        out.append({
            "name": p.name,
            "size_bytes": p.stat().st_size,
            "age_days": round(age_days, 1),
        })
    return sorted(out, key=lambda r: r["age_days"])


def _mail_recent(folder: str, limit: int = 30) -> list[dict]:
    """List last N messages from Mail.app folder ('sent mailbox' or 'drafts mailbox')."""
    if sys.platform != "darwin":
        return []
    script = f'''
tell application "Mail"
    set msgs to messages of {folder}
    set out to {{}}
    set ctr to 0
    repeat with msg in msgs
        if ctr >= {limit} then exit repeat
        try
            set s to subject of msg
            set toAddrs to address of (to recipients of msg)
            set d to date sent of msg
            set end of out to (s & "\\t" & (toAddrs as string) & "\\t" & (d as string))
        end try
        set ctr to ctr + 1
    end repeat
    return out
end tell
'''
    try:
        proc = subprocess.run(
            ["osascript", "-e", script],
            capture_output=True,
            text=True,
            timeout=15,
        )
    except Exception:
        return []
    if proc.returncode != 0:
        return []
    rows: list[dict] = []
    for chunk in (proc.stdout or "").split(", "):
        chunk = chunk.strip()
        if not chunk or "\t" not in chunk:
            continue
        parts = chunk.split("\t")
        if len(parts) < 3:
            continue
        rows.append({"subject": parts[0][:140], "to": parts[1][:140], "date": parts[2][:80]})
    return rows


def _research_board_summary() -> dict:
    if not RESEARCH_BOARD.exists():
        return {"counts": {}}
    text = RESEARCH_BOARD.read_text(encoding="utf-8")
    counts: dict[str, int] = {}
    for status in ("Backlog", "In Research", "Draft Ready", "Pending User Approval", "Submitted"):
        counts[status] = text.count(f"Status | **{status}") + text.count(f"Status | {status}")
    return {"counts": counts}


def _preflight_summary() -> dict:
    """Summarize deterministic board gates for the PI snapshot.

    Keep this local/offline. The PI should see why the research loop is idle
    before it proposes restarts or generic discovery work.
    """
    try:
        from outreach_preflight import judge_board  # noqa: PLC0415
    except Exception as exc:
        return {"error": f"import failed: {exc}"}
    try:
        rows = judge_board()
    except Exception as exc:
        return {"error": f"judge_board failed: {exc}"}

    histogram: dict[str, int] = {}
    actionable: list[dict] = []
    blocked: list[dict] = []
    for row in rows:
        histogram[row.verdict] = histogram.get(row.verdict, 0) + 1
        item = {
            "todo_id": row.todo_id,
            "slug": row.slug,
            "title": row.title,
            "score": row.score,
            "verdict": row.verdict,
            "missing": row.missing[:6],
            "risk_flags": row.risk_flags[:4],
            "display_kind": row.display.kind,
            "display_artifact": row.display.artifact,
        }
        if row.verdict == "RUN":
            actionable.append(item)
        elif len(blocked) < 12:
            blocked.append(item)
    return {
        "histogram": histogram,
        "actionable": actionable[:8],
        "top_blocked": blocked,
    }


def _review_queue_summary() -> dict:
    """Read-only operator/recovery queue for PI review."""
    try:
        from outreach_review_queue import build_queue  # noqa: PLC0415
    except Exception as exc:
        return {"error": f"import failed: {exc}"}
    try:
        q = build_queue()
    except Exception as exc:
        return {"error": f"build_queue failed: {exc}"}
    return {
        "ready_for_operator": q.get("ready_for_operator", [])[:8],
        "blocked_tasks": q.get("blocked_tasks", [])[:8],
        "stale_in_progress": q.get("stale_in_progress", [])[:8],
        "profile_candidates": q.get("profile_candidates", [])[:8],
        "candidate_inbox": q.get("candidate_inbox", {}),
        "freshness_judges": q.get("freshness_judges", {}),
        "board_histogram": q.get("board_histogram", {}),
        "external_send_policy": q.get("external_send_policy"),
    }


def _recent_commits(n: int = 6) -> list[str]:
    try:
        out = subprocess.run(
            ["git", "log", "--oneline", f"-{n}"],
            cwd=str(SCRIPT_DIR),
            capture_output=True,
            text=True,
            timeout=5,
        ).stdout
    except Exception:
        return []
    return [ln for ln in out.splitlines() if ln.strip()]


def _stop_age_seconds(path: Path) -> float | None:
    if not path.exists():
        return None
    try:
        return (datetime.now(timezone.utc).timestamp() - path.stat().st_mtime)
    except OSError:
        return None


def collect_snapshot() -> dict:
    return {
        "ts": _now_iso(),
        "outreach_log": _parse_outreach_log(),
        "target_states": _state_summary(),
        "research_board": _research_board_summary(),
        "drafts": _drafts_listing(),
        "mail_sent_recent": _mail_recent("sent mailbox", limit=20),
        "mail_drafts_recent": _mail_recent("drafts mailbox", limit=20),
        "oracle_server": _server_status(),
        "preflight": _preflight_summary(),
        "review_queue": _review_queue_summary(),
        "recent_commits": _recent_commits(),
        "supervisor_tail": _read_tail(SUPERVISOR_LOG, n=30),
    }


# ---------------------------------------------------------------------------
# claude exec
# ---------------------------------------------------------------------------
# Single source of truth lives in outreach_claude_exec (zero-dep). Re-exported
# below so existing `from outreach_pi_agent import claude_exec` callers keep
# working without taking on this module's import-time risk surface.

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_claude_exec import claude_exec as _claude_exec  # noqa: E402


def claude_exec(prompt: str, *, timeout: int = PI_TIMEOUT_S, log_tag: str = "pi_review") -> tuple[bool, str, int]:
    return _claude_exec(
        prompt,
        timeout=timeout,
        log_tag=log_tag,
        log_dir=SUPERVISOR_LOG_DIR,
        repo_root=REPO_ROOT,
    )


def _extract_json_object(text: str) -> dict | None:
    text = (text or "").strip()
    if not text:
        return None
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, flags=re.DOTALL)
    if fence:
        candidate = fence.group(1)
    else:
        first = text.find("{")
        last = text.rfind("}")
        if first == -1 or last == -1 or last <= first:
            return None
        candidate = text[first : last + 1]
    try:
        return json.loads(candidate)
    except json.JSONDecodeError:
        return None


# ---------------------------------------------------------------------------
# concern dedup + escalation
# ---------------------------------------------------------------------------


def _hash_concern(s: str) -> str:
    canon = re.sub(r"\s+", " ", s.strip().lower())[:300]
    return hashlib.sha256(canon.encode("utf-8")).hexdigest()[:16]


def _load_concern_counts() -> dict:
    if not CONCERN_COUNTS_PATH.exists():
        return {}
    try:
        return json.loads(CONCERN_COUNTS_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def _save_concern_counts(counts: dict) -> None:
    CONCERN_COUNTS_PATH.parent.mkdir(parents=True, exist_ok=True)
    CONCERN_COUNTS_PATH.write_text(
        json.dumps(counts, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )


def bump_concerns(concerns: list[str]) -> list[dict]:
    counts = _load_concern_counts()
    escalated: list[dict] = []
    seen: set[str] = set()
    for concern in concerns:
        if not concern or not concern.strip():
            continue
        key = _hash_concern(concern)
        if key in seen:
            continue
        seen.add(key)
        entry = counts.get(key, {
            "text": concern.strip(),
            "count": 0,
            "first_seen": _now_iso(),
            "last_seen": _now_iso(),
            "escalated": False,
        })
        entry["count"] = entry.get("count", 0) + 1
        entry["text"] = concern.strip()
        entry["last_seen"] = _now_iso()
        if entry["count"] >= ESCALATE_AFTER_REPEATS and not entry.get("escalated"):
            entry["escalated"] = True
            entry["escalated_at"] = _now_iso()
            escalated.append({"hash": key, **entry})
        counts[key] = entry
    _save_concern_counts(counts)
    return escalated


# ---------------------------------------------------------------------------
# action executors (autonomous whitelist)
# ---------------------------------------------------------------------------


def _spawn_arxiv_watch() -> None:
    arxiv_watch = SCRIPT_DIR / "arxiv_watch.py"
    if not arxiv_watch.exists():
        return
    subprocess.Popen(
        ["python3", str(arxiv_watch)],
        cwd=str(REPO_ROOT),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )


def _spawn_lit_staleness(target_id: str) -> None:
    lit = SCRIPT_DIR / "lit_staleness.py"
    if not lit.exists():
        return
    args = ["python3", str(lit)]
    if target_id and target_id != "ALL":
        args.extend(["--target", target_id])
    subprocess.Popen(
        args,
        cwd=str(REPO_ROOT),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )


def _spawn_inbox_watcher(days: int = 14) -> None:
    watcher = SCRIPT_DIR / "outreach_inbox_watcher.py"
    if not watcher.exists():
        return
    subprocess.Popen(
        ["python3", str(watcher), "--days", str(int(days))],
        cwd=str(REPO_ROOT),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )


def _spawn_profile_judge() -> None:
    judge = SCRIPT_DIR / "outreach_profile_judge.py"
    if not judge.exists():
        return
    subprocess.Popen(
        ["python3", str(judge), "--generate-board-batch-with-codex", "--top", "1", "--min-score", "15"],
        cwd=str(REPO_ROOT),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )
    subprocess.Popen(
        ["python3", str(judge), "--graduate-inbox-with-codex", "--top", "1"],
        cwd=str(REPO_ROOT),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )


def _mark_target_stale(target_id: str, reason: str) -> bool:
    """Append a 'stale' note to the OUTREACH_LOG row matching target_id.

    Conservative: only mutates rows where the first cell substring-matches
    target_id; appends ' — stale (pi: <reason>)' to the status cell.
    Returns True iff a row was modified.
    """
    if not OUTREACH_LOG.exists() or not target_id:
        return False
    text = OUTREACH_LOG.read_text(encoding="utf-8")
    new_lines: list[str] = []
    changed = False
    safe_reason = reason.replace("|", "/").strip()[:120]
    suffix = f" — stale (pi {datetime.now().strftime('%Y-%m-%d')}: {safe_reason})"
    for line in text.splitlines():
        m = _OUTREACH_ROW_RE.match(line)
        if m and target_id.lower() in m.group(1).lower() and "stale (pi" not in m.group(3):
            cells = [m.group(i) for i in range(1, 7)]
            cells[2] = cells[2].rstrip() + suffix
            new_lines.append("| " + " | ".join(c.strip() for c in cells) + " |")
            changed = True
        else:
            new_lines.append(line)
    if changed:
        OUTREACH_LOG.write_text("\n".join(new_lines) + ("\n" if text.endswith("\n") else ""), encoding="utf-8")
    return changed


def apply_actions(plan: dict, supervisor_callbacks: dict | None = None) -> list[str]:
    applied: list[str] = []
    callbacks = supervisor_callbacks or {}
    for entry in plan.get("autonomous_actions") or []:
        action = (entry.get("action") or "").strip()
        if action not in ALLOWED_AUTONOMOUS:
            applied.append(f"REJECT (not in allowlist): {action}")
            continue
        args = entry.get("args") or {}
        try:
            if action == "run_arxiv_watch":
                _spawn_arxiv_watch()
                applied.append("run_arxiv_watch")
            elif action == "run_lit_staleness":
                target_id = args.get("target_id") or "ALL"
                _spawn_lit_staleness(target_id)
                applied.append(f"run_lit_staleness target={target_id}")
            elif action == "run_inbox_watcher":
                days = args.get("days") or 14
                _spawn_inbox_watcher(days=days)
                applied.append(f"run_inbox_watcher days={days}")
            elif action == "run_profile_judge":
                _spawn_profile_judge()
                applied.append("run_profile_judge")
            elif action == "mark_target_stale":
                tid = args.get("target_id") or ""
                reason = args.get("reason") or "no reason given"
                ok = _mark_target_stale(tid, reason)
                applied.append(f"mark_target_stale target={tid} ok={ok}")
            elif action == "adjust_cooldown":
                cb = callbacks.get("adjust_cooldown")
                if cb:
                    cb(args)
                    applied.append(f"adjust_cooldown {args}")
                else:
                    applied.append("SKIP adjust_cooldown: no supervisor callback (standalone run)")
            elif action == "restart_inner":
                cb = callbacks.get("restart_inner")
                if cb:
                    cb()
                    applied.append("restart_inner")
                else:
                    applied.append("SKIP restart_inner: no supervisor callback")
            elif action == "revive_task":
                tid = (args.get("task_id") or "").strip()
                reason = (args.get("reason") or "PI revive").strip()
                ok, msg = _revive_task(tid, reason)
                applied.append(f"revive_task task={tid} ok={ok} ({msg})")
            elif action == "reroute_task":
                tid = (args.get("task_id") or "").strip()
                use_oracle = bool(args.get("use_oracle"))
                reason = (args.get("reason") or "PI reroute").strip()
                ok, msg = _reroute_task(tid, use_oracle=use_oracle, reason=reason)
                applied.append(f"reroute_task task={tid} use_oracle={use_oracle} ok={ok} ({msg})")
        except Exception as exc:
            applied.append(f"ERROR applying {action}: {exc}")
    return applied


# ---------------------------------------------------------------------------
# task-state mutation helpers (autonomous PI actions)
# ---------------------------------------------------------------------------


_TASK_QUEUE_DIR = STATE_DIR / "task_queue"


def _load_task(task_id: str) -> tuple[Path | None, dict]:
    p = _TASK_QUEUE_DIR / f"{task_id}.json"
    if not p.exists():
        return None, {}
    try:
        return p, json.loads(p.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return p, {}


def _save_task(p: Path, d: dict) -> None:
    p.write_text(json.dumps(d, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _revive_task(task_id: str, reason: str) -> tuple[bool, str]:
    """Reset rejected/blocked task to pending so task_runner re-attempts.

    Hard-blocks blocked tasks that need an external repo (`requires_external_repo`)
    and tasks already pending/in_progress (no-op).
    """
    if not task_id:
        return False, "task_id empty"
    p, d = _load_task(task_id)
    if p is None:
        return False, "task not found"
    cur = d.get("status", "")
    if cur in {"pending", "in_progress", "writeback_pending", "writeback_in_progress"}:
        return False, f"task already in workable state ({cur})"
    if d.get("requires_external_repo"):
        return False, "requires_external_repo; revive blocked"
    d["status"] = "pending"
    d["retries"] = 0
    d["last_verdict"] = ""
    d["last_reason"] = f"PI revive 2026-05-09: {reason[:200]}"
    d["last_run_iso"] = ""
    _save_task(p, d)
    return True, f"revived from {cur}"


def _reroute_task(task_id: str, *, use_oracle: bool, reason: str) -> tuple[bool, str]:
    """Flip context.use_oracle on a task. Use to escape a stuck deep-reason
    path (e.g. ChatGPT bridge stalls → switch to codex_track local) or to
    escalate a codex-track-exhausted task to ChatGPT Project context.

    Resets retries to 0 and status to pending in the same write so the
    task_runner picks up the new routing on the next poll.
    """
    if not task_id:
        return False, "task_id empty"
    p, d = _load_task(task_id)
    if p is None:
        return False, "task not found"
    ctx = d.get("context") or {}
    prev = bool(ctx.get("use_oracle"))
    if prev == use_oracle and d.get("status") in {"pending", "in_progress"}:
        return False, f"already use_oracle={use_oracle} and {d.get('status')}"
    ctx["use_oracle"] = use_oracle
    d["context"] = ctx
    d["status"] = "pending"
    d["retries"] = 0
    d["last_verdict"] = ""
    d["last_reason"] = f"PI reroute 2026-05-09 use_oracle={prev}->{use_oracle}: {reason[:200]}"
    d["last_run_iso"] = ""
    _save_task(p, d)
    return True, f"use_oracle {prev}->{use_oracle} status->pending retries->0"


def stage_inbox_items(plan: dict, escalated_concerns: list[dict]) -> list[str]:
    items: list[str] = []
    for entry in plan.get("human_inbox") or []:
        action = (entry.get("action") or "").strip()
        if action not in ALLOWED_INBOX:
            continue
        details = (entry.get("details") or "").strip()
        args = entry.get("args") or {}
        args_blob = json.dumps(args, ensure_ascii=False)[:400] if args else ""
        head = f"**{action}** — {details}"
        if args_blob:
            head += f"\n  args: `{args_blob}`"
        items.append(head)
    for c in escalated_concerns:
        items.append(
            f"**recurring concern** (seen {c.get('count')}× since {c.get('first_seen', '?')}): {c.get('text', '')[:300]}"
        )
    return items


def append_human_inbox(items: list[str]) -> None:
    if not items:
        return
    HUMAN_INBOX.parent.mkdir(parents=True, exist_ok=True)
    block = "\n## " + _now_iso() + "\n\n" + "\n".join(f"- {it}" for it in items) + "\n"
    with open(HUMAN_INBOX, "a", encoding="utf-8") as f:
        f.write(block)


def journal(entry: dict) -> None:
    PI_JOURNAL.parent.mkdir(parents=True, exist_ok=True)
    with open(PI_JOURNAL, "a", encoding="utf-8") as f:
        f.write(json.dumps(entry, ensure_ascii=False) + "\n")


# ---------------------------------------------------------------------------
# entry point
# ---------------------------------------------------------------------------


def run_review(supervisor_callbacks: dict | None = None) -> dict | None:
    snapshot = collect_snapshot()
    template = PROMPT_PATH.read_text(encoding="utf-8")
    snapshot_json = json.dumps(snapshot, ensure_ascii=False, indent=2)
    try:
        operator_memory = OPERATOR_MEMORY_PATH.read_text(encoding="utf-8")
    except OSError:
        operator_memory = "(operator memory unavailable)"
    prompt = template.format(
        snapshot=_safe(snapshot_json[:30000]),
        operator_memory=_safe(operator_memory[:12000]),
    )
    ok, stdout, rc = claude_exec(prompt, timeout=PI_TIMEOUT_S, log_tag="pi_review")

    plan: dict | None = None
    if ok:
        plan = _extract_json_object(stdout)

    applied: list[str] = []
    inbox: list[str] = []
    escalated: list[dict] = []
    if plan:
        escalated = bump_concerns(plan.get("concerns") or [])
        applied = apply_actions(plan, supervisor_callbacks=supervisor_callbacks)
        inbox = stage_inbox_items(plan, escalated)
        if inbox:
            append_human_inbox(inbox)

    journal({
        "ts": _now_iso(),
        "ok": ok,
        "rc": rc,
        "snapshot": snapshot,
        "plan": plan,
        "applied": applied,
        "escalated_concerns": escalated,
        "inbox_items_appended": inbox,
        "claude_stdout_truncated": (stdout or "")[:8000],
    })
    return plan


def main() -> int:
    plan = run_review()
    if plan is None:
        print("(no plan parsed; see outreach_state/pi_journal.jsonl)", file=sys.stderr)
        return 1
    print(json.dumps(plan, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
