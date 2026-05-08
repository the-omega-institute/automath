#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Outreach Oracle bridge server — multi-turn deep reasoning for community-outreach.

Forked structure tracks tools/bedc-deep/bedc_oracle_server.py from newmath, with
outreach-specific overlays (port 8766, 2-tab cap, openproblem Project URL).

Differences vs the paper oracle:
  - Port 8766 (paper oracle is 8765, BEDC oracle is 8767).
  - Task payload accepts `conversation_id` and `conversation_url`. When set, the
    userscript MUST navigate to that URL and post as a follow-up there.
  - After each turn, the userscript POSTs back the chat URL it landed on. The
    server stores it on the session so subsequent turns reuse the same chat.
  - Sessions persist to disk at tools/community-outreach/outreach_oracle/sessions/
    so server restart doesn't lose the conversation thread.

Protective layer (ported from bedc-deep 2026-05-08):
  - Project-URL enforcement: agent polls/results from outside the openproblem
    Project URL are rejected; the offending pending task is re-queued.
  - URL mismatch detection: if a follow-up task carries `conversation_url=X` but
    the userscript reports a result while on URL Y, the result is ignored and
    the task is re-queued. Prevents the BEDC-contamination failure mode where
    the wrong tab returns a stale prior conversation's content.
  - Response cleaning: strip `ChatGPT said:`, `Thought for ...`, footer chrome
    before persisting.
  - Contamination detection: reject responses containing canonical BEDC paper /
    paper-trade markers (we are openproblem outreach, not BEDC).
  - Minimum userscript version (`outreach-1.9`): older scripts can't push
    results, prevents bad data from a half-upgraded environment.

Usage:
    python3 tools/community-outreach/outreach_oracle_server.py

    # Open ChatGPT.com tab(s) with outreach_oracle_macos.user.js installed,
    # set ACTIVE in the panel, server will dispatch tasks.

Hard rules:
  - Server never speaks to chatgpt.com directly. The userscript is the only
    code that touches the model.
  - Server never auto-publishes anything. Results land in sessions/ and are
    consumed by oracle_consultant.py / outreach_state JSON merge.
"""

from __future__ import annotations

import json
import re
import sys
import threading
import time
import uuid
from http.server import HTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from datetime import datetime, timezone
from collections import deque
from urllib.parse import urlparse, parse_qs

PORT = 8766
ORACLE_DIR = Path(__file__).parent / "outreach_oracle"
SESSIONS_DIR = ORACLE_DIR / "sessions"
RESULTS_DIR = ORACLE_DIR / "results"

MAX_AGENTS = 2  # operator memory: tab cap = 2 on this machine
TASK_TIMEOUT = 14400  # 4 hours; ChatGPT Pro thinking can be 60+ min/turn
AGENT_RECENT_SECONDS = 120
SESSION_IDLE_RETENTION = 14 * 24 * 3600  # keep sessions on disk for 14 days
MIN_SCRIPT_VERSION = "outreach-1.9"
OPENPROBLEM_PROJECT_PREFIX = "/g/g-p-69fdba181e648191a0eb330852658373-openproblem"
OPENPROBLEM_PROJECT_URL = f"https://chatgpt.com{OPENPROBLEM_PROJECT_PREFIX}/project"

# In-memory state (durable copy on disk)
task_queue: deque[dict] = deque()
results: dict[str, dict] = {}             # task_id -> result record
pending_tasks: dict[str, dict] = {}       # agent_id -> task currently in flight
dispatch_times: dict[str, float] = {}     # agent_id -> dispatch timestamp
recent_agents: dict[str, dict] = {}       # agent_id -> latest poll/ack/result
sessions: dict[str, dict] = {}            # conv_id -> session record
cancelled_tasks: set[str] = set()
_lock = threading.Lock()


# ---------------------------------------------------------------------------
# Session persistence
# ---------------------------------------------------------------------------


def _now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _ensure_dirs() -> None:
    SESSIONS_DIR.mkdir(parents=True, exist_ok=True)
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)


def _session_path(conv_id: str) -> Path:
    return SESSIONS_DIR / f"{conv_id}.json"


def _load_session(conv_id: str) -> dict:
    p = _session_path(conv_id)
    if not p.exists():
        return {}
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}


def _write_session(session: dict) -> None:
    conv_id = session.get("conversation_id")
    if not conv_id:
        return
    _session_path(conv_id).write_text(
        json.dumps(session, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def _hydrate_sessions() -> None:
    _ensure_dirs()
    for p in SESSIONS_DIR.glob("*.json"):
        try:
            sess = json.loads(p.read_text(encoding="utf-8"))
            cid = sess.get("conversation_id")
            if cid:
                sessions[cid] = sess
        except Exception:
            continue


def _new_conversation_id() -> str:
    return f"conv_{uuid.uuid4().hex[:16]}"


def _record_turn(conv_id: str, turn: dict) -> None:
    with _lock:
        sess = sessions.get(conv_id) or _load_session(conv_id) or {
            "conversation_id": conv_id,
            "created_at": _now(),
            "turns": [],
        }
        sess.setdefault("turns", []).append(turn)
        sess["updated_at"] = _now()
        if "chatgpt_url" in turn and turn["chatgpt_url"]:
            sess["chatgpt_url"] = turn["chatgpt_url"]
        sessions[conv_id] = sess
        _write_session(sess)


# ---------------------------------------------------------------------------
# Agent tracking + drift / contamination protection
# ---------------------------------------------------------------------------


def _record_agent_seen(agent_id: str, *, event: str, metrics: dict | None = None) -> None:
    if not agent_id:
        return
    rec = {
        "agent_id": agent_id,
        "event": event,
        "last_seen": time.time(),
        "last_seen_at": _now(),
    }
    if metrics:
        rec["metrics"] = metrics
    recent_agents[agent_id] = rec


def _agent_summary(now: float) -> dict[str, dict]:
    summary: dict[str, dict] = {}
    for aid, rec in recent_agents.items():
        idle = int(now - float(rec.get("last_seen", now)))
        summary[aid] = {
            "event": rec.get("event", ""),
            "last_seen_at": rec.get("last_seen_at", ""),
            "idle_seconds": idle,
            "recent": idle <= AGENT_RECENT_SECONDS,
        }
        if isinstance(rec.get("metrics"), dict):
            summary[aid]["metrics"] = rec["metrics"]
    return summary


def _chat_id(url: str) -> str:
    m = re.search(r"/c/([a-f0-9-]{6,})", url or "")
    return m.group(1) if m else ""


def _same_chat_url(expected: str, seen: str) -> bool:
    if not expected:
        return True
    if not seen:
        return False
    expected_id = _chat_id(expected)
    seen_id = _chat_id(seen)
    if expected_id or seen_id:
        return bool(expected_id and seen_id and expected_id == seen_id)
    return seen.startswith(expected)


def _task_url_mismatch(task: dict, seen_url: str) -> bool:
    expected = str(task.get("conversation_url") or "")
    if not expected or not task.get("is_followup"):
        return False
    return not _same_chat_url(expected, seen_url)


def _busy_agent_is_current(aid: str, rec: dict | None, task: dict) -> bool:
    if not rec or not rec.get("recent", False):
        return False
    event = rec.get("event", "")
    metrics = rec.get("metrics") or {}
    seen_task_id = str(metrics.get("task_id") or "")
    pending_task_id = str(task.get("task_id") or "")
    if event in {"ack", "heartbeat"} and seen_task_id and seen_task_id != pending_task_id:
        return False
    seen_url = str(metrics.get("chatgpt_url") or metrics.get("page_url") or "")
    if event in {"ack", "heartbeat"} and _task_url_mismatch(task, seen_url):
        return False
    return True


def _script_version_tuple(version: str) -> tuple[int, ...]:
    m = re.search(r"(\d+(?:\.\d+)*)", version or "")
    if not m:
        return ()
    return tuple(int(p) for p in m.group(1).split("."))


def _script_version_ok(version: str) -> bool:
    return _script_version_tuple(version) >= _script_version_tuple(MIN_SCRIPT_VERSION)


def _page_in_openproblem_project(url: str) -> bool:
    if not url:
        return False
    try:
        parsed = urlparse(url)
    except Exception:
        return False
    return parsed.netloc in {"chatgpt.com", "chat.openai.com"} and parsed.path.startswith(OPENPROBLEM_PROJECT_PREFIX)


def _cancel_pending_for_agent(agent_id: str, *, reason: str) -> str:
    task = pending_tasks.pop(agent_id, None)
    dispatch_times.pop(agent_id, None)
    recent_agents.pop(agent_id, None)
    task_id = str((task or {}).get("task_id") or "")
    if task_id:
        cancelled_tasks.add(task_id)
        print(f"[server] Cancelled {task_id} for {agent_id}: {reason}", flush=True)
    return task_id


def _cancel_pending_task_id(task_id: str, *, reason: str) -> str:
    if not task_id:
        return ""
    for aid, task in list(pending_tasks.items()):
        if task.get("task_id") == task_id:
            pending_tasks.pop(aid, None)
            dispatch_times.pop(aid, None)
            recent_agents.pop(aid, None)
            cancelled_tasks.add(task_id)
            print(f"[server] Cancelled {task_id} for {aid}: {reason}", flush=True)
            return aid
    return ""


def _queued_summary(now: float) -> list[dict]:
    items: list[dict] = []
    for task in list(task_queue)[:10]:
        submitted_ts = float(task.get("submitted_ts", now))
        items.append({
            "task_id": task.get("task_id", ""),
            "conversation_id": task.get("conversation_id", ""),
            "tag": task.get("tag", ""),
            "age_seconds": int(now - submitted_ts),
            "prompt_chars": len(task.get("prompt", "")),
            "is_followup": bool(task.get("is_followup")),
        })
    return items


def _clean_response_text(text: str) -> str:
    cleaned = text or ""
    cleaned = re.sub(r"^\s*ChatGPT said:\s*", "", cleaned)
    cleaned = re.sub(r"\bThought for [0-9hm s]+", "", cleaned)
    cleaned = re.sub(r"\n?window\.__oai_logHTML\?.*\Z", "", cleaned, flags=re.DOTALL)
    cleaned = re.sub(r"\n?Extended Pro\s*ChatGPT can make mistakes\..*\Z", "", cleaned, flags=re.DOTALL)
    cleaned = re.sub(r"\n?ChatGPT can make mistakes\..*\Z", "", cleaned, flags=re.DOTALL)
    return cleaned.strip()


def _response_is_error(text: str) -> bool:
    return bool(re.match(r"\s*ERROR\b", text or "", re.IGNORECASE))


def _response_is_contaminated(text: str) -> bool:
    """Detect content that clearly belongs to other pipelines bleeding in.

    Outreach drafts are public-facing letters / forum posts / issue replies in
    plain English. The markers below come from BEDC paper-claim packets and
    paper-trade research summaries (newmath / chatgpt-oracle pipelines), and
    must never appear in an outreach result.
    """
    markers = (
        # BEDC paper-claim packet (newmath bedc-deep)
        "Round 1: Discovery",
        "Candidate open problems",
        "Omega Project capability digest",
        "Survivors ranked",
        "TOP-3 picks for deep reasoning",
        "EXPECTED-PUBLICATION:",
        # BEDC LaTeX boilerplate
        "papers/bedc/parts/",
        "BEDC.Derived.",
        "AbelianCat^",
        "AbGroup^",
        "Cat^",
        # Paper-trade pipeline (publication oracle)
        "VERDICT/SCORE/TOP-RISK/TOP-RECOMMENDATION",
    )
    return any(marker in (text or "") for marker in markers)


def _should_replace_result(existing: dict | None, response: str) -> bool:
    if not existing:
        return True
    old_response = existing.get("response", "")
    if _response_is_error(old_response) and not _response_is_error(response):
        return True
    if not _response_is_error(old_response) and _response_is_error(response):
        return False
    return len(response) >= len(old_response)


# ---------------------------------------------------------------------------
# HTTP handler
# ---------------------------------------------------------------------------


class OutreachOracleHandler(BaseHTTPRequestHandler):

    def log_message(self, fmt, *args):
        return  # silence default logging

    def _send_json(self, data: dict, status: int = 200):
        body = json.dumps(data, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()
        self.wfile.write(body)

    def do_OPTIONS(self):
        self._send_json({})

    def _cleanup_stale(self):
        now = time.time()
        with _lock:
            stale = [aid for aid, t in dispatch_times.items()
                     if now - t > TASK_TIMEOUT and aid in pending_tasks]
            for aid in stale:
                task = pending_tasks.pop(aid)
                dispatch_times.pop(aid, None)
                task_queue.appendleft(task)
                print(f"[server] Agent {aid} timed out — task {task['task_id']} re-queued")

    def do_GET(self):
        parsed = urlparse(self.path)
        qs = parse_qs(parsed.query)

        if parsed.path == "/task":
            self._cleanup_stale()
            agent_id = (qs.get("agent", [None])[0]
                        or qs.get("agent_id", [None])[0]
                        or "default")
            poll_metrics = {
                "script_version": (qs.get("script_version", [""])[0] or ""),
                "page_url": (qs.get("page_url", [""])[0] or ""),
                "chatgpt_url": (qs.get("chatgpt_url", [""])[0] or ""),
            }
            compatible_script = _script_version_ok(poll_metrics["script_version"])
            in_project = _page_in_openproblem_project(poll_metrics["page_url"])
            with _lock:
                if not in_project:
                    cancelled_id = ""
                    if agent_id in pending_tasks:
                        cancelled_id = _cancel_pending_for_agent(
                            agent_id,
                            reason=f"outside openproblem Project poll ({poll_metrics['page_url'][-80:]})",
                        )
                    else:
                        recent_agents.pop(agent_id, None)
                    self._send_json({
                        "status": "cancelled" if cancelled_id else "idle",
                        "task_id": cancelled_id,
                        "required_project_url": OPENPROBLEM_PROJECT_URL,
                        "reason": "agent outside openproblem Project",
                    })
                    return
                _record_agent_seen(agent_id, event="poll", metrics=poll_metrics)
                if agent_id in pending_tasks:
                    self._send_json(pending_tasks[agent_id])
                    return
                if not compatible_script:
                    self._send_json({
                        "status": "idle",
                        "required_script_version": MIN_SCRIPT_VERSION,
                        "agent_script_version": poll_metrics["script_version"],
                    })
                    return
                if task_queue and len(pending_tasks) < MAX_AGENTS:
                    task = task_queue.popleft()
                    task["assigned_agent"] = agent_id
                    pending_tasks[agent_id] = task
                    dispatch_times[agent_id] = time.time()
                    print(f"[server] Dispatched {task['task_id']} → {agent_id} "
                          f"(conv={task.get('conversation_id','-')[:12]} "
                          f"agents={len(pending_tasks)}/{MAX_AGENTS} "
                          f"queue={len(task_queue)})")
                    self._send_json(task)
                    return
                self._send_json({"status": "idle"})
            return

        if parsed.path == "/status":
            self._cleanup_stale()
            with _lock:
                now = time.time()
                agents_info = {
                    aid: {"task_id": t.get("task_id", "?"),
                          "conversation_id": t.get("conversation_id", ""),
                          "elapsed": int(time.time() - dispatch_times.get(aid, time.time()))}
                    for aid, t in pending_tasks.items()
                }
                recent = _agent_summary(now)
                active_recent = [aid for aid, rec in recent.items() if rec["recent"]]
                active_poll = [
                    aid for aid, rec in recent.items()
                    if rec["recent"] and rec.get("event") == "poll"
                ]
                compatible_active_poll = [
                    aid for aid in active_poll
                    if _script_version_ok(
                        ((recent.get(aid, {}).get("metrics") or {}).get("script_version") or "")
                    )
                ]
                project_active_poll = [
                    aid for aid in compatible_active_poll
                    if _page_in_openproblem_project(
                        ((recent.get(aid, {}).get("metrics") or {}).get("page_url") or "")
                    )
                ]
                stale_busy = [
                    aid for aid, task in pending_tasks.items()
                    if not _busy_agent_is_current(aid, recent.get(aid), task)
                ]
                mismatched_busy = [
                    aid for aid, task in pending_tasks.items()
                    if recent.get(aid, {}).get("recent", False)
                    and not _busy_agent_is_current(aid, recent.get(aid), task)
                ]
                if task_queue and not pending_tasks and not active_poll:
                    diagnosis = "queue_waiting_for_browser_agent"
                elif task_queue and not pending_tasks and not compatible_active_poll:
                    diagnosis = "queue_waiting_for_compatible_agent"
                elif task_queue and not pending_tasks and not project_active_poll:
                    diagnosis = "queue_waiting_for_project_agent"
                elif pending_tasks:
                    diagnosis = "agent_busy_with_stale" if stale_busy else "agent_busy"
                elif task_queue:
                    diagnosis = "queue_waiting_for_free_agent"
                else:
                    diagnosis = "idle"
                self._send_json({
                    "queue_length": len(task_queue),
                    "queued_tasks": _queued_summary(now),
                    "agents_busy": len(pending_tasks),
                    "max_agents": MAX_AGENTS,
                    "agents": agents_info,
                    "recent_agents": recent,
                    "active_recent_agents": active_recent,
                    "active_poll_agents": active_poll,
                    "compatible_active_poll_agents": compatible_active_poll,
                    "project_active_poll_agents": project_active_poll,
                    "stale_busy_agents": stale_busy,
                    "mismatched_busy_agents": mismatched_busy,
                    "agent_recent_seconds": AGENT_RECENT_SECONDS,
                    "completed": len(results),
                    "active_sessions": len(sessions),
                    "port": PORT,
                    "kind": "outreach-oracle",
                    "required_script_version": MIN_SCRIPT_VERSION,
                    "required_project_url": OPENPROBLEM_PROJECT_URL,
                    "diagnosis": diagnosis,
                })
            return

        if parsed.path.startswith("/result/"):
            task_id = parsed.path[len("/result/"):]
            with _lock:
                rec = results.get(task_id)
                cancelled = task_id in cancelled_tasks
            if rec:
                self._send_json(rec)
            elif cancelled:
                self._send_json({"status": "cancelled", "task_id": task_id})
            else:
                self._send_json({"status": "not_found"}, 404)
            return

        if parsed.path.startswith("/session/"):
            conv_id = parsed.path[len("/session/"):]
            with _lock:
                sess = sessions.get(conv_id) or _load_session(conv_id)
            if sess:
                self._send_json(sess)
            else:
                self._send_json({"status": "not_found"}, 404)
            return

        if parsed.path == "/sessions":
            with _lock:
                summary = [
                    {
                        "conversation_id": s["conversation_id"],
                        "turns": len(s.get("turns", [])),
                        "updated_at": s.get("updated_at", ""),
                        "chatgpt_url": s.get("chatgpt_url", ""),
                        "tag": s.get("tag", ""),
                    }
                    for s in sessions.values()
                ]
            self._send_json({"sessions": sorted(summary, key=lambda x: x["updated_at"], reverse=True)})
            return

        self._send_json({"error": "unknown endpoint"}, 404)

    def do_POST(self):
        length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(length).decode("utf-8") if length else ""
        try:
            data = json.loads(body) if body else {}
        except json.JSONDecodeError:
            self._send_json({"error": "invalid JSON"}, 400)
            return

        if self.path == "/submit":
            self._handle_submit(data, is_continue=False)
            return
        if self.path == "/continue":
            self._handle_submit(data, is_continue=True)
            return
        if self.path == "/result":
            self._handle_result(data)
            return
        if self.path == "/ack":
            self._handle_ack(data)
            return
        if self.path == "/close":
            self._handle_close(data)
            return
        if self.path == "/retry":
            self._handle_retry(data)
            return
        if self.path == "/cancel":
            self._handle_cancel(data)
            return
        if self.path == "/pin-conv-url":
            self._handle_pin_conv_url(data)
            return

        self._send_json({"error": "unknown endpoint"}, 404)

    def _handle_submit(self, data: dict, *, is_continue: bool):
        prompt = data.get("prompt", "")
        if not prompt:
            self._send_json({"error": "prompt required"}, 400)
            return
        task_id = data.get("task_id") or f"outreach_{int(time.time())}_{uuid.uuid4().hex[:6]}"
        conv_id = data.get("conversation_id")
        if is_continue:
            if not conv_id:
                self._send_json({"error": "/continue requires conversation_id"}, 400)
                return
            with _lock:
                sess = sessions.get(conv_id) or _load_session(conv_id)
            if not sess:
                self._send_json({"error": f"unknown conversation_id {conv_id}"}, 404)
                return
            chatgpt_url = sess.get("chatgpt_url", "")
        else:
            if not conv_id:
                conv_id = _new_conversation_id()
            with _lock:
                sess = sessions.get(conv_id) or _load_session(conv_id) or {
                    "conversation_id": conv_id,
                    "created_at": _now(),
                    "turns": [],
                    "tag": data.get("tag", ""),
                }
                sessions[conv_id] = sess
                _write_session(sess)
            chatgpt_url = sess.get("chatgpt_url", "")

        task = {
            "task_id": task_id,
            "prompt": prompt,
            "conversation_id": conv_id,
            "conversation_url": chatgpt_url,
            "is_followup": bool(is_continue or chatgpt_url),
            "model": data.get("model", "chatgpt-5.5-pro"),
            "tag": data.get("tag", ""),
            "submitted_at": _now(),
            "submitted_ts": time.time(),
            "status": "queued",
        }
        with _lock:
            cancelled_tasks.discard(task_id)
        if "pdf_base64" in data:
            task["pdf_base64"] = data["pdf_base64"]
            task["pdf_name"] = data.get("pdf_name", "attachment.pdf")
        with _lock:
            task_queue.append(task)
        print(f"[server] {'CONT ' if is_continue else 'NEW  '}queued {task_id} "
              f"conv={conv_id[:12]} prompt={len(prompt)} chars "
              f"queue={len(task_queue)}")
        self._send_json({
            "status": "queued",
            "task_id": task_id,
            "conversation_id": conv_id,
            "queue_position": len(task_queue),
        })

    def _handle_result(self, data: dict):
        task_id = data.get("task_id", "")
        raw_response = data.get("response", "")
        response = _clean_response_text(raw_response)
        agent_id = data.get("agent_id", "")
        chatgpt_url = data.get("chatgpt_url", "")
        if not task_id or not response:
            self._send_json({"error": "task_id and response required"}, 400)
            return
        if not _page_in_openproblem_project(data.get("page_url", "")):
            with _lock:
                _cancel_pending_task_id(task_id, reason="outside-project result")
                if agent_id:
                    recent_agents.pop(agent_id, None)
            print(
                f"[server] Ignored outside-project result {task_id} "
                f"page={str(data.get('page_url', ''))[-80:]}",
                flush=True,
            )
            self._send_json({"status": "ignored_outside_project", "task_id": task_id})
            return

        with _lock:
            task = None
            freed_agent = ""
            for aid in list(pending_tasks):
                if pending_tasks[aid].get("task_id") == task_id:
                    task = pending_tasks.pop(aid)
                    dispatch_times.pop(aid, None)
                    freed_agent = aid
                    break
            existing = results.get(task_id)
        if task is None and existing is None:
            print(f"[server] Ignored orphan result {task_id} ({len(response)} chars)")
            self._send_json({"status": "ignored_orphan", "task_id": task_id})
            return
        conv_id = (task or {}).get("conversation_id", "") or (existing or {}).get("conversation_id", "")
        if not chatgpt_url:
            chatgpt_url = (task or {}).get("conversation_url", "") or (existing or {}).get("chatgpt_url", "")
        seen_url = chatgpt_url or data.get("page_url", "")
        if task is not None and _task_url_mismatch(task, seen_url):
            with _lock:
                task["status"] = "queued"
                task.pop("assigned_agent", None)
                task_queue.appendleft(task)
            expected = str(task.get("conversation_url") or "")
            print(
                f"[server] Ignored mismatched-url result {task_id} "
                f"expected={expected[-50:]} seen={seen_url[-50:]} requeued",
                flush=True,
            )
            self._send_json({"status": "ignored_mismatched_url", "task_id": task_id})
            return
        if _response_is_contaminated(response):
            print(f"[server] Ignored contaminated result {task_id} ({len(response)} chars)")
            self._send_json({"status": "ignored_contaminated", "task_id": task_id})
            return

        record = {
            "task_id": task_id,
            "response": response,
            "conversation_id": conv_id,
            "chatgpt_url": chatgpt_url,
            "model": data.get("model", "chatgpt-5.5-pro"),
            "agent_id": agent_id,
            "script_version": data.get("script_version", ""),
            "page_url": data.get("page_url", ""),
            "completed_at": _now(),
            "status": "completed",
            "response_chars": len(response),
            "raw_response_chars": len(raw_response),
        }
        if not _should_replace_result(existing, response):
            print(f"[server] Ignored stale result {task_id} ({len(response)} chars) "
                  f"conv={conv_id[:12]} freed={freed_agent}")
            self._send_json({"status": "ignored", "task_id": task_id})
            return
        with _lock:
            _record_agent_seen(agent_id, event="result")
            results[task_id] = record

        if conv_id:
            _record_turn(conv_id, {
                "task_id": task_id,
                "prompt": (task or {}).get("prompt", ""),
                "response": response,
                "chatgpt_url": chatgpt_url,
                "completed_at": record["completed_at"],
                "model": record["model"],
                "response_chars": len(response),
                "raw_response_chars": len(raw_response),
            })

        _ensure_dirs()
        out = RESULTS_DIR / f"{task_id}.md"
        meta = {k: v for k, v in record.items() if k != "response"}
        out.write_text(
            f"<!-- outreach-oracle: {json.dumps(meta, ensure_ascii=False)} -->\n\n{response}",
            encoding="utf-8",
        )
        print(f"[server] Result {task_id} ({len(response)} chars) "
              f"conv={conv_id[:12]} freed={freed_agent}")
        self._send_json({"status": "saved", "task_id": task_id})

    def _handle_ack(self, data: dict):
        task_id = data.get("task_id", "")
        agent_id = data.get("agent_id", "?")
        event = "heartbeat" if data.get("heartbeat") else "ack"
        metrics = data.get("metrics") if isinstance(data.get("metrics"), dict) else None
        if metrics:
            metrics = {
                "task_id": task_id,
                "script_version": data.get("script_version", ""),
                "page_url": data.get("page_url", ""),
                "chatgpt_url": data.get("chatgpt_url", ""),
                "elapsed_seconds": metrics.get("elapsed_seconds"),
                "extracted_chars": metrics.get("extracted_chars"),
                "page_chars": metrics.get("page_chars"),
                "stable_count": metrics.get("stable_count"),
                "generating": metrics.get("generating"),
                "url_tail": metrics.get("url_tail"),
            }
        else:
            metrics = {
                "task_id": task_id,
                "script_version": data.get("script_version", ""),
                "page_url": data.get("page_url", ""),
                "chatgpt_url": data.get("chatgpt_url", ""),
            }
        with _lock:
            in_project = _page_in_openproblem_project(metrics.get("page_url", ""))
            if not in_project:
                cancelled_id = ""
                if task_id and pending_tasks.get(agent_id, {}).get("task_id") == task_id:
                    cancelled_id = _cancel_pending_for_agent(agent_id, reason="outside-project ack/heartbeat")
                else:
                    recent_agents.pop(agent_id, None)
                self._send_json({
                    "status": "cancelled" if cancelled_id else "ignored_outside_project",
                    "task_id": cancelled_id or task_id,
                    "required_project_url": OPENPROBLEM_PROJECT_URL,
                    "reason": "agent outside openproblem Project",
                })
                return
            _record_agent_seen(agent_id, event=event, metrics=metrics)
            if event == "heartbeat" and task_id:
                assigned = pending_tasks.get(agent_id)
                assigned_task_id = str((assigned or {}).get("task_id") or "")
                still_pending = any(t.get("task_id") == task_id for t in pending_tasks.values())
                seen_url = str(metrics.get("chatgpt_url") or metrics.get("page_url") or "")
                if (
                    task_id in cancelled_tasks
                    or (assigned_task_id and assigned_task_id != task_id)
                    or (assigned and _task_url_mismatch(assigned, seen_url))
                    or not still_pending
                ):
                    self._send_json({"status": "cancelled", "task_id": task_id})
                    return
            if agent_id in dispatch_times:
                dispatch_times[agent_id] = time.time()
        if event == "ack":
            print(f"[server] Ack {task_id} by {agent_id}")
        self._send_json({"status": "ok"})

    def _handle_cancel(self, data: dict):
        task_id = data.get("task_id", "")
        cancel_all = bool(data.get("all", False))
        cancelled: list[str] = []
        with _lock:
            if cancel_all:
                while task_queue:
                    task = task_queue.popleft()
                    tid = task.get("task_id", "")
                    cancelled.append(tid)
                    if tid:
                        cancelled_tasks.add(tid)
                for aid, task in list(pending_tasks.items()):
                    tid = task.get("task_id", "")
                    cancelled.append(tid)
                    if tid:
                        cancelled_tasks.add(tid)
                    pending_tasks.pop(aid, None)
                    dispatch_times.pop(aid, None)
                    recent_agents.pop(aid, None)
            elif task_id:
                kept: deque[dict] = deque()
                while task_queue:
                    task = task_queue.popleft()
                    if task.get("task_id") == task_id:
                        cancelled.append(task_id)
                        cancelled_tasks.add(task_id)
                    else:
                        kept.append(task)
                task_queue.extend(kept)
                for aid, task in list(pending_tasks.items()):
                    if task.get("task_id") == task_id:
                        cancelled.append(task_id)
                        cancelled_tasks.add(task_id)
                        pending_tasks.pop(aid, None)
                        dispatch_times.pop(aid, None)
                        recent_agents.pop(aid, None)
            else:
                self._send_json({"error": "task_id or all=true required"}, 400)
                return
        print(f"[server] Cancelled {len(cancelled)} task(s): {cancelled}")
        self._send_json({"status": "cancelled", "tasks": cancelled})

    def _handle_close(self, data: dict):
        conv_id = data.get("conversation_id", "")
        if not conv_id:
            self._send_json({"error": "conversation_id required"}, 400)
            return
        with _lock:
            sess = sessions.get(conv_id) or _load_session(conv_id)
            if sess:
                sess["closed_at"] = _now()
                sessions[conv_id] = sess
                _write_session(sess)
        self._send_json({"status": "closed", "conversation_id": conv_id})

    def _handle_pin_conv_url(self, data: dict):
        task_id = data.get("task_id", "")
        chatgpt_url = data.get("chatgpt_url", "")
        if not task_id or not chatgpt_url:
            self._send_json({"error": "task_id and chatgpt_url required"}, 400)
            return
        if not _page_in_openproblem_project(chatgpt_url):
            self._send_json({
                "status": "ignored_outside_project",
                "task_id": task_id,
                "required_project_url": OPENPROBLEM_PROJECT_URL,
                "reason": "chatgpt_url outside openproblem Project",
            })
            return
        with _lock:
            conv_id = ""
            rec = results.get(task_id)
            if rec:
                conv_id = rec.get("conversation_id", "")
            if not conv_id:
                for aid, t in pending_tasks.items():
                    if t.get("task_id") == task_id:
                        conv_id = t.get("conversation_id", "")
                        break
            if not conv_id:
                self._send_json({"error": f"unknown task_id {task_id}"}, 404)
                return
            sess = sessions.get(conv_id) or _load_session(conv_id) or {
                "conversation_id": conv_id, "created_at": _now(), "turns": [],
            }
            sess["chatgpt_url"] = chatgpt_url
            sess["updated_at"] = _now()
            sessions[conv_id] = sess
            _write_session(sess)
        print(f"[server] pinned chatgpt_url={chatgpt_url[-50:]} to conv={conv_id[:12]}")
        self._send_json({"status": "pinned", "conversation_id": conv_id, "chatgpt_url": chatgpt_url})

    def _handle_retry(self, data: dict):
        task_id = data.get("task_id", "")
        conv_id = data.get("conversation_id", "")
        if not task_id and not conv_id:
            self._send_json({"error": "task_id or conversation_id required"}, 400)
            return
        with _lock:
            if not conv_id:
                rec = results.get(task_id)
                if rec:
                    conv_id = rec.get("conversation_id", "")
            if not conv_id:
                self._send_json({"error": f"could not resolve conversation_id for {task_id}"}, 404)
                return
            sess = sessions.get(conv_id) or _load_session(conv_id)
            if not sess:
                self._send_json({"error": f"unknown conversation {conv_id}"}, 404)
                return
            chatgpt_url = sess.get("chatgpt_url", "")

        new_task_id = f"retry_{conv_id[:12]}_{int(time.time())}_{uuid.uuid4().hex[:4]}"
        original_prompt = ""
        for t in sess.get("turns", []) or []:
            if isinstance(t, dict) and t.get("prompt"):
                original_prompt = t["prompt"]
                break
        if chatgpt_url:
            task = {
                "task_id": new_task_id,
                "prompt": original_prompt,
                "conversation_id": conv_id,
                "conversation_url": chatgpt_url,
                "is_followup": True,
                "re_extract": True,
                "model": data.get("model", "chatgpt-5.5-pro"),
                "tag": data.get("tag", "retry"),
                "submitted_at": _now(),
                "submitted_ts": time.time(),
                "status": "queued",
            }
            mode = "re-extract"
        else:
            task = {
                "task_id": new_task_id,
                "prompt": ("Please paste your final draft from the previous turn verbatim, "
                           "no preamble, no commentary, just the message text."),
                "conversation_id": conv_id,
                "conversation_url": "",
                "is_followup": True,
                "model": data.get("model", "chatgpt-5.5-pro"),
                "tag": data.get("tag", "retry-repeat"),
                "submitted_at": _now(),
                "submitted_ts": time.time(),
                "status": "queued",
            }
            mode = "repeat-prompt"
        with _lock:
            task_queue.append(task)
        print(f"[server] retry {mode} → queued {new_task_id} conv={conv_id[:12]}")
        self._send_json({
            "status": "queued",
            "task_id": new_task_id,
            "conversation_id": conv_id,
            "mode": mode,
            "queue_position": len(task_queue),
        })


def main():
    _ensure_dirs()
    _hydrate_sessions()
    server = HTTPServer(("127.0.0.1", PORT), OutreachOracleHandler)
    print(f"[outreach-oracle] running on http://localhost:{PORT}")
    print(f"[outreach-oracle] sessions dir: {SESSIONS_DIR}")
    print(f"[outreach-oracle] results dir:  {RESULTS_DIR}")
    print(f"[outreach-oracle] hydrated {len(sessions)} sessions from disk")
    print(f"[outreach-oracle] max {MAX_AGENTS} concurrent tabs (multi-turn capable)")
    print(f"[outreach-oracle] required script version: {MIN_SCRIPT_VERSION}")
    print(f"[outreach-oracle] required project URL: {OPENPROBLEM_PROJECT_URL}")
    print(f"[outreach-oracle] open tabs:")
    for i in range(1, MAX_AGENTS + 1):
        print(f"  Tab {i}: {OPENPROBLEM_PROJECT_URL}?outreach={i}")
    print(f"[outreach-oracle] Ctrl+C to stop.\n")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n[outreach-oracle] stopped.")
        server.server_close()


if __name__ == "__main__":
    main()
