#!/usr/bin/env python3
"""Human review queue for outreach.

Summarizes what is ready for the operator, what is blocked, and what the system
can safely do next. This command is read-only: it never sends email, posts,
comments, pushes, or starts agents.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
DRAFTS_DIR = SCRIPT_DIR / "drafts"
CONTEXT_REFRESH_PATH = SCRIPT_DIR / "outreach_state" / "context_refresh.json"

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_task_spec import list_tasks  # noqa: E402
from outreach_task_spec import save_task  # noqa: E402
from outreach_task_runner import cleanup_stale_in_progress_tasks  # noqa: E402
from outreach_profile_judge import select_candidates  # noqa: E402
from outreach_profile_judge import PROFILEABLE_INBOX_STATUSES  # noqa: E402
from outreach_preflight import judge_board  # noqa: E402
from outreach_candidate_inbox import list_candidates  # noqa: E402
from outreach_freshness_judge import required_targets as freshness_required_targets  # noqa: E402


def _file_info(rel: str) -> dict:
    p = Path(rel)
    if not p.is_absolute():
        p = REPO_ROOT / rel
    try:
        return {
            "path": rel,
            "exists": p.exists(),
            "size_bytes": p.stat().st_size if p.exists() else 0,
        }
    except OSError:
        return {"path": rel, "exists": False, "size_bytes": 0}


def _parse_iso_epoch(s: str) -> int:
    if not s:
        return 0
    try:
        return int(datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp())
    except ValueError:
        return 0


_ZH_MAIL_DATE_RE = re.compile(
    r"(?P<y>\d{4})年(?P<m>\d{1,2})月(?P<d>\d{1,2})日.*?"
    r"(?P<ampm>上午|下午)?(?P<h>\d{1,2}):(?P<mi>\d{2})(?::(?P<sec>\d{2}))?"
)


def _parse_mail_epoch(s: str) -> int:
    """Best-effort parse of Apple Mail's localized date string.

    Mail.app renders dates using the user's locale; on this machine that is
    Chinese, e.g. `2026年5月9日 星期六 下午3:59:43`. We only need ordering against
    task.last_run_iso, so local timezone is acceptable and more robust than
    trying to force AppleScript to emit an English epoch date.
    """
    s = s or ""
    m = _ZH_MAIL_DATE_RE.search(s)
    if m:
        y = int(m.group("y"))
        month = int(m.group("m"))
        day = int(m.group("d"))
        hour = int(m.group("h"))
        minute = int(m.group("mi"))
        sec = int(m.group("sec") or 0)
        ampm = m.group("ampm") or ""
        if ampm == "下午" and hour < 12:
            hour += 12
        if ampm == "上午" and hour == 12:
            hour = 0
        return int(datetime(y, month, day, hour, minute, sec).astimezone().timestamp())
    for fmt in ("%a, %d %b %Y %H:%M:%S %z", "%Y-%m-%d %H:%M:%S %z", "%Y-%m-%d %H:%M:%S"):
        try:
            return int(datetime.strptime(s, fmt).astimezone().timestamp())
        except ValueError:
            pass
    return 0


def _context_refresh() -> dict:
    try:
        return json.loads(CONTEXT_REFRESH_PATH.read_text(encoding="utf-8"))
    except Exception:
        return {}


def _task_thread_freshness(task, ctx_snapshot: dict) -> dict:
    """Detect registered mail/GitHub activity newer than a gated task run.

    A `gated_ready` task is only ready for human review if no registered
    external thread has moved after the task's last successful run. This is
    intentionally narrow: registered threads only, no broad inbox scanning.
    """
    last_run_epoch = _parse_iso_epoch(task.last_run_iso)
    if not last_run_epoch:
        return {"status": "unknown", "reason": "task has no last_run_iso"}
    ctx = task.context or {}
    thread = str(ctx.get("thread") or "").lower()
    external = str(ctx.get("external_party") or "").lower()
    updates: list[dict] = []

    for row in ctx_snapshot.get("mail") or []:
        subject = str(row.get("subject") or "").lower()
        email = str(row.get("email") or "").lower()
        if subject and subject not in thread:
            continue
        if email and email not in external and email not in thread:
            continue
        for m in row.get("messages") or []:
            if m.get("mailbox") != "inbox":
                continue
            epoch = int(m.get("epoch_seconds") or 0) or _parse_mail_epoch(str(m.get("date_str") or ""))
            if epoch > last_run_epoch:
                updates.append({
                    "kind": "mail",
                    "sender": m.get("sender"),
                    "subject": m.get("subject"),
                    "date_str": m.get("date_str"),
                    "body_head": (m.get("body_head") or "")[:1000],
                })

    for row in ctx_snapshot.get("github") or []:
        url = str(row.get("url") or "").lower()
        if url and url in thread:
            updated = row.get("updated_at") or ""
            if _parse_iso_epoch(updated) > last_run_epoch:
                updates.append({
                    "kind": "github",
                    "url": row.get("url"),
                    "title": row.get("title"),
                    "updated_at": updated,
                })

    if updates:
        return {
            "status": "stale_external_update",
            "reason": "registered external thread has newer activity than deliverable",
            "updates": updates[:5],
        }
    return {"status": "current", "reason": "no newer registered thread activity detected"}


def _message_epoch(message: dict) -> int:
    return int(message.get("epoch_seconds") or 0) or _parse_mail_epoch(str(message.get("date_str") or ""))


def _registered_thread_state(task, ctx_snapshot: dict) -> dict:
    """Classify the latest known external-thread state for a task.

    - incoming_needs_action: external party wrote after our last task run.
    - waiting_external_reply: our sent message is the latest known mail event.
    - current: no newer registered event is known.
    - unknown: insufficient local timestamp/thread data.
    """
    last_run_epoch = _parse_iso_epoch(task.last_run_iso)
    ctx = task.context or {}
    thread = str(ctx.get("thread") or "").lower()
    external = str(ctx.get("external_party") or "").lower()
    if not thread and not external:
        return {"status": "unknown", "reason": "task has no registered thread/external party"}

    latest: dict | None = None
    for row in ctx_snapshot.get("mail") or []:
        subject = str(row.get("subject") or "").lower()
        email = str(row.get("email") or "").lower()
        if subject and subject not in thread:
            continue
        if email and email not in external and email not in thread:
            continue
        for m in row.get("messages") or []:
            epoch = _message_epoch(m)
            if not epoch:
                continue
            if latest is None or epoch > int(latest.get("epoch") or 0):
                latest = {
                    "kind": "mail",
                    "mailbox": m.get("mailbox"),
                    "epoch": epoch,
                    "sender": m.get("sender"),
                    "subject": m.get("subject"),
                    "date_str": m.get("date_str"),
                    "body_head": (m.get("body_head") or "")[:1000],
                }

    for row in ctx_snapshot.get("github") or []:
        url = str(row.get("url") or "").lower()
        if url and url in thread:
            epoch = _parse_iso_epoch(str(row.get("updated_at") or ""))
            if epoch and (latest is None or epoch > int(latest.get("epoch") or 0)):
                latest = {
                    "kind": "github",
                    "mailbox": "",
                    "epoch": epoch,
                    "url": row.get("url"),
                    "title": row.get("title"),
                    "updated_at": row.get("updated_at"),
                    "body_head": "",
                }

    if latest is None:
        return {"status": "unknown", "reason": "no registered thread messages found"}
    if latest.get("kind") == "mail" and latest.get("mailbox") == "inbox" and task.status == "waiting_external_reply":
        try:
            necessity = reply_necessity(task)
        except NameError:
            necessity = {"action": "reply_now"}
        if necessity.get("action") == "wait_external":
            return {
                "status": "waiting_external_reply",
                "reason": necessity.get("reason") or "waiting for collaborator's promised next step",
                "latest": latest,
            }
        return {
            "status": "incoming_needs_action",
            "reason": "external registered mail event arrived while task was waiting for reply",
            "latest": latest,
        }
    if latest.get("kind") == "mail" and latest.get("mailbox") == "sent":
        return {
            "status": "waiting_external_reply",
            "reason": "latest registered mail event is our sent message",
            "latest": latest,
        }
    if last_run_epoch and int(latest.get("epoch") or 0) > last_run_epoch:
        return {
            "status": "incoming_needs_action",
            "reason": "external registered thread event is newer than deliverable",
            "latest": latest,
        }
    return {
        "status": "current",
        "reason": "latest registered event is already covered by deliverable",
        "latest": latest,
    }


def reply_necessity(task) -> dict:
    """Decide whether an email collaboration task should draft/reply now.

    This is a coarse deterministic gate before writing a polished email. It
    prevents a worker from turning every incoming acknowledgement into a reply
    when the collaborator has already taken the next action.
    """
    if task.type != "email_reply_draft":
        return {"action": "reply_now", "reason": "not an email reply task"}
    ctx = task.context or {}
    body = " ".join(
        [
            str(ctx.get("latest_reply_summary") or ""),
            str((ctx.get("latest_registered_reply") or {}).get("body_head") or ""),
        ]
    )
    low = " ".join(body.lower().split())
    if not low:
        return {"action": "reply_now", "reason": "no latest reply summary available"}

    external_takes_next = (
        "i'll start" in low
        or "i will start" in low
        or "i’ll start" in low
        or "i'll proceed" in low
        or "i will proceed" in low
        or "i’ll proceed" in low
        or "once it's in shape i'll send it over" in low
        or "once it is in shape i will send it over" in low
        or "i'll send it over" in low
        or "i will send it over" in low
        or "then we can meet" in low
        or "we can meet on" in low
    )
    asks_us_for_material = (
        "send the prompt" in low
        or "send me" in low
        or "please send" in low
        or "could you send" in low
        or "can you send" in low
        or "i would be grateful" in low
        or "question" in low and "?" in body
    )
    if external_takes_next and not asks_us_for_material:
        return {
            "action": "wait_external",
            "reason": "latest collaborator reply assigns the next concrete step to them",
        }
    return {"action": "reply_now", "reason": "latest reply still calls for our response or clarification"}


def _newer_covering_task(task, tasks: list, freshness: dict) -> dict | None:
    """Find a newer gated task on the same registered thread.

    Example: an older Israel paper-trade packet is stale relative to Israel's
    latest email, but a newer frontier-subset task already incorporates that
    email and depends on the older task. In that case we should not requeue the
    older packet and create churn.
    """
    ctx = task.context or {}
    thread = str(ctx.get("thread") or "").lower()
    if not thread:
        return None
    latest_update_epoch = 0
    for upd in freshness.get("updates") or []:
        latest_update_epoch = max(
            latest_update_epoch,
            _parse_iso_epoch(str(upd.get("updated_at") or ""))
            or _parse_mail_epoch(str(upd.get("date_str") or "")),
        )
    for other in tasks:
        if other.id == task.id or other.status != "gated_ready":
            continue
        other_ctx = other.context or {}
        other_thread = str(other_ctx.get("thread") or "").lower()
        if not other_thread or other_thread != thread:
            continue
        if other_ctx.get("depends_on_task") == task.id or _parse_iso_epoch(other.last_run_iso) > latest_update_epoch:
            return {
                "id": other.id,
                "title": other.title,
                "last_run_iso": other.last_run_iso,
                "reason": "newer gated_ready task on same registered thread covers the update",
            }
    return None


def _apply_latest_external_context(task, latest: dict | None) -> None:
    if not latest:
        return
    if latest.get("kind") == "mail":
        task.context["latest_reply_date"] = str(latest.get("date_str") or "")
        task.context["latest_reply_summary"] = str(latest.get("body_head") or "")[:2000]
        task.context["latest_registered_reply"] = {
            "kind": "mail",
            "mailbox": latest.get("mailbox"),
            "sender": latest.get("sender"),
            "subject": latest.get("subject"),
            "date_str": latest.get("date_str"),
            "body_head": str(latest.get("body_head") or "")[:4000],
        }
    elif latest.get("kind") == "github":
        task.context["latest_registered_reply"] = {
            "kind": "github",
            "url": latest.get("url"),
            "title": latest.get("title"),
            "updated_at": latest.get("updated_at"),
            "body_head": str(latest.get("body_head") or "")[:4000],
        }


def build_queue() -> dict:
    tasks = list_tasks()
    ctx_snapshot = _context_refresh()
    ready = []
    waiting_external = []
    needs_refresh = []
    superseded = []
    blocked = []
    stale = cleanup_stale_in_progress_tasks(dry_run=True)
    for t in tasks:
        if t.status == "gated_ready":
            necessity = reply_necessity(t)
            if necessity.get("action") == "wait_external":
                item = {
                    "id": t.id,
                    "title": t.title,
                    "type": t.type,
                    "priority_score": t.priority_score(),
                    "last_run_iso": t.last_run_iso,
                    "last_reason": t.last_reason,
                    "deliverables": [_file_info(p) for p in t.deliverable_paths],
                    "operator_action": "waiting for collaborator's promised next step; do not send draft now",
                    "thread_freshness": {},
                    "thread_state": {"status": "waiting_external_reply", "reason": necessity.get("reason")},
                }
                waiting_external.append(item)
                continue
            item = {
                "id": t.id,
                "title": t.title,
                "type": t.type,
                "priority_score": t.priority_score(),
                "last_run_iso": t.last_run_iso,
                "last_reason": t.last_reason,
                "deliverables": [_file_info(p) for p in t.deliverable_paths],
                "operator_action": "review deliverables; explicitly approve before any external send",
                "thread_freshness": _task_thread_freshness(t, ctx_snapshot),
                "thread_state": _registered_thread_state(t, ctx_snapshot),
            }
            if item["thread_state"]["status"] == "waiting_external_reply":
                item["operator_action"] = "waiting for external reply; do not continue autonomously"
                waiting_external.append(item)
            elif item["thread_freshness"]["status"] == "stale_external_update":
                covering = _newer_covering_task(t, tasks, item["thread_freshness"])
                if covering:
                    item["operator_action"] = "superseded by newer gated task on the same registered thread"
                    item["superseded_by"] = covering
                    superseded.append(item)
                else:
                    item["operator_action"] = "registered thread updated after deliverable; revise draft before review/send"
                    needs_refresh.append(item)
            else:
                ready.append(item)
        elif t.status == "blocked":
            blocked.append({
                "id": t.id,
                "title": t.title,
                "reason": t.last_reason,
                "requires_external_repo": t.requires_external_repo,
            })
        elif t.status == "waiting_external_reply":
            waiting_external.append({
                "id": t.id,
                "title": t.title,
                "type": t.type,
                "priority_score": t.priority_score(),
                "last_run_iso": t.last_run_iso,
                "last_reason": t.last_reason,
                "deliverables": [_file_info(p) for p in t.deliverable_paths],
                "operator_action": "waiting for external reply; do not continue autonomously",
                "thread_freshness": {},
                "thread_state": _registered_thread_state(t, ctx_snapshot),
            })

    preflight = judge_board()
    profile_candidates = select_candidates(top=8, min_score=12)
    candidate_inbox = list_candidates()
    freshness_targets = freshness_required_targets()
    return {
        "ready_for_operator": sorted(ready, key=lambda x: (-int(x.get("priority_score") or 0), x.get("last_run_iso") or "")),
        "waiting_external_reply": sorted(waiting_external, key=lambda x: (-int(x.get("priority_score") or 0), x.get("last_run_iso") or "")),
        "needs_refresh": needs_refresh,
        "superseded_ready": superseded,
        "blocked_tasks": blocked,
        "stale_in_progress": stale,
        "profile_candidates": profile_candidates,
        "candidate_inbox": {
            "total": len(candidate_inbox),
            "needs_profile_judge": sum(1 for c in candidate_inbox if c.get("status") == "needs_profile_judge"),
            "operator_requested_review": sum(1 for c in candidate_inbox if c.get("status") == "operator_requested_review"),
            "long_horizon_review": sum(1 for c in candidate_inbox if c.get("status") == "long_horizon_review"),
            "profileable": sum(1 for c in candidate_inbox if c.get("status") in PROFILEABLE_INBOX_STATUSES),
            "invalid": sum(1 for c in candidate_inbox if c.get("status") == "invalid"),
        },
        "freshness_judges": {
            "required": len(freshness_targets),
            "passing": sum(1 for r in freshness_targets if r.get("ok")),
            "missing_or_blocked": [
                {
                    "todo_id": r.get("todo_id"),
                    "slug": r.get("slug"),
                    "title": r.get("title"),
                    "errors": r.get("errors"),
                }
                for r in freshness_targets
                if not r.get("ok")
            ][:8],
        },
        "board_histogram": {
            k: sum(1 for r in preflight if r.verdict == k)
            for k in sorted({r.verdict for r in preflight})
        },
        "drafts_dir": str(DRAFTS_DIR.relative_to(REPO_ROOT)),
        "external_send_policy": "forbidden without explicit operator approval",
    }


def requeue_stale_ready_tasks(*, dry_run: bool = False) -> list[dict]:
    """Return stale gated_ready collaboration tasks to pending.

    This is deliberately narrow: only registered external-thread updates found
    by targeted context refresh can requeue a task. It does not scan the broad
    inbox and it never sends anything externally.
    """
    tasks = list_tasks()
    ctx_snapshot = _context_refresh()
    changed: list[dict] = []
    for task in tasks:
        if task.status == "waiting_external_reply":
            thread_state = _registered_thread_state(task, ctx_snapshot)
            if thread_state.get("status") != "incoming_needs_action":
                continue
            row = {
                "id": task.id,
                "from_status": "waiting_external_reply",
                "to_status": "pending",
                "reason": thread_state.get("reason"),
                "latest": thread_state.get("latest"),
                "dry_run": dry_run,
            }
            changed.append(row)
            if dry_run:
                continue
            _apply_latest_external_context(task, thread_state.get("latest"))
            task.status = "pending"
            task.last_verdict = "incoming_needs_action"
            task.last_reason = "external registered mail event arrived; rerun draft/review task before operator approval"
            save_task(task)
            continue
        if task.status != "gated_ready":
            continue
        thread_state = _registered_thread_state(task, ctx_snapshot)
        if thread_state.get("status") == "waiting_external_reply":
            changed.append({
                "id": task.id,
                "from_status": "gated_ready",
                "to_status": "gated_ready",
                "reason": "not requeued; latest registered mail event is our sent message",
                "thread_state": thread_state,
                "dry_run": dry_run,
            })
            continue
        freshness = _task_thread_freshness(task, ctx_snapshot)
        if freshness.get("status") != "stale_external_update":
            continue
        covering = _newer_covering_task(task, tasks, freshness)
        if covering:
            changed.append({
                "id": task.id,
                "from_status": "gated_ready",
                "to_status": "gated_ready",
                "reason": "not requeued; newer gated task covers registered thread update",
                "superseded_by": covering,
                "dry_run": dry_run,
            })
            continue
        row = {
            "id": task.id,
            "from_status": "gated_ready",
            "to_status": "pending",
            "reason": freshness.get("reason"),
            "updates": freshness.get("updates") or [],
            "dry_run": dry_run,
        }
        changed.append(row)
        if dry_run:
            continue
        latest_update = (freshness.get("updates") or [{}])[-1]
        _apply_latest_external_context(task, latest_update)
        task.status = "pending"
        task.last_verdict = "needs_refresh"
        task.last_reason = "registered external thread updated after deliverable; rerun before operator review"
        save_task(task)
    return changed


def mark_waiting_external_reply(*, dry_run: bool = False) -> list[dict]:
    """Persist waiting_external_reply when our sent mail is the latest event."""
    tasks = list_tasks()
    ctx_snapshot = _context_refresh()
    changed: list[dict] = []
    for task in tasks:
        if task.status not in {"pending", "rejected", "gated_ready"}:
            continue
        thread_state = _registered_thread_state(task, ctx_snapshot)
        if thread_state.get("status") != "waiting_external_reply":
            continue
        row = {
            "id": task.id,
            "from_status": task.status,
            "to_status": "waiting_external_reply",
            "reason": thread_state.get("reason"),
            "thread_state": thread_state,
            "dry_run": dry_run,
        }
        changed.append(row)
        if dry_run:
            continue
        task.status = "waiting_external_reply"
        task.last_verdict = "waiting_external_reply"
        task.last_reason = "latest registered mail event is our sent message; wait for external reply"
        save_task(task)
    return changed


def _print_text(q: dict) -> None:
    print("External send policy: explicit operator approval required")
    print(f"Board: {q['board_histogram']}")
    print("")
    print(f"Ready for review: {len(q['ready_for_operator'])}")
    for item in q["ready_for_operator"]:
        print(f"- {item['id']} priority={item.get('priority_score', 0)} :: {item['title']}")
        print(f"  action: {item['operator_action']}")
        ts = item.get("thread_state") or {}
        if ts:
            print(f"  thread: {ts.get('status')} — {ts.get('reason')}")
            latest = ts.get("latest") if isinstance(ts.get("latest"), dict) else {}
            if latest:
                when = latest.get("date_str") or latest.get("updated_at") or ""
                subject = latest.get("subject") or latest.get("title") or ""
                print(f"  latest: {when} — {subject}")
        for f in item["deliverables"]:
            status = "ok" if f["exists"] else "missing"
            print(f"  - {status} {f['path']} ({f['size_bytes']} bytes)")
    if q.get("waiting_external_reply"):
        print("")
        print(f"Waiting for external reply: {len(q['waiting_external_reply'])}")
        for item in q["waiting_external_reply"]:
            print(f"- {item['id']} priority={item.get('priority_score', 0)} :: {item['title']}")
            ts = item.get("thread_state") or {}
            if ts:
                print(f"  thread: {ts.get('status')} — {ts.get('reason')}")
                latest = ts.get("latest") if isinstance(ts.get("latest"), dict) else {}
                if latest:
                    when = latest.get("date_str") or latest.get("updated_at") or ""
                    subject = latest.get("subject") or latest.get("title") or ""
                    print(f"  latest: {when} — {subject}")
            for f in item["deliverables"]:
                status = "ok" if f["exists"] else "missing"
                print(f"  - {status} {f['path']} ({f['size_bytes']} bytes)")
    if q.get("needs_refresh"):
        print("")
        print(f"Needs refresh before review: {len(q['needs_refresh'])}")
        for item in q["needs_refresh"]:
            print(f"- {item['id']} :: {item['title']}")
            print(f"  action: {item['operator_action']}")
            for upd in (item.get("thread_freshness") or {}).get("updates") or []:
                print(f"  - {upd.get('kind')} {upd.get('date_str') or upd.get('updated_at')}: {upd.get('subject') or upd.get('title')}")
    if q.get("superseded_ready"):
        print("")
        print(f"Superseded by newer task: {len(q['superseded_ready'])}")
        for item in q["superseded_ready"]:
            cover = item.get("superseded_by") or {}
            print(f"- {item['id']} -> {cover.get('id')}: {item['operator_action']}")
    print("")
    print(f"Blocked/stale: {len(q['blocked_tasks']) + len(q['stale_in_progress'])}")
    for item in q["blocked_tasks"]:
        print(f"- blocked {item['id']}: {item['reason']}")
    for item in q["stale_in_progress"]:
        print(f"- stale {item['task_id']}: {item['reason']}")
    print("")
    print(f"Profile candidates: {len(q['profile_candidates'])}")
    for c in q["profile_candidates"]:
        print(f"- {c['todo_id']} score={c['score']} {c['slug']} :: {c['title']}")
    inbox = q.get("candidate_inbox") or {}
    if inbox:
        print("")
        print(
            f"Candidate inbox: total={inbox.get('total')} "
            f"needs_profile_judge={inbox.get('needs_profile_judge')} invalid={inbox.get('invalid')}"
        )
    fresh = q.get("freshness_judges") or {}
    if fresh:
        print("")
        print(
            f"Freshness judges: required={fresh.get('required')} "
            f"passing={fresh.get('passing')} "
            f"missing_or_blocked={len(fresh.get('missing_or_blocked') or [])}"
        )


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--json", action="store_true")
    p.add_argument("--requeue-stale-ready", action="store_true",
                   help="turn gated_ready tasks with newer registered thread activity back to pending")
    p.add_argument("--mark-waiting-external-reply", action="store_true",
                   help="persist waiting_external_reply when our sent mail is the latest registered event")
    p.add_argument("--dry-run", action="store_true")
    args = p.parse_args(argv)
    if args.mark_waiting_external_reply:
        rows = mark_waiting_external_reply(dry_run=args.dry_run)
        print(json.dumps({"marked": rows, "dry_run": args.dry_run}, ensure_ascii=False, indent=2))
        return 0
    if args.requeue_stale_ready:
        rows = requeue_stale_ready_tasks(dry_run=args.dry_run)
        print(json.dumps({"requeued": rows, "dry_run": args.dry_run}, ensure_ascii=False, indent=2))
        return 0
    q = build_queue()
    if args.json:
        print(json.dumps(q, ensure_ascii=False, indent=2))
    else:
        _print_text(q)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
