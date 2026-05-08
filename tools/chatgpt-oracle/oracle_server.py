#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Local HTTP server for ChatGPT oracle automation.

Bridges between Claude agents and a Tampermonkey userscript running
inside the user's Chrome browser on chatgpt.com.

Two modes coexist on this server (port 8765):

  * Single-shot (legacy, paper review): submit a prompt, get a result.
    Tasks without `conversation_id` keep the original behaviour. The
    Tampermonkey userscript opens a fresh chat for each task.

  * Multi-turn (deepening / Project follow-up): callers thread several
    prompts into the same ChatGPT conversation. The first turn issues a
    `conversation_id`; follow-up turns are submitted via /continue and
    the userscript navigates to the pinned chatgpt_url before posting.
    Sessions persist on disk so server restart never loses the thread.

Endpoints:

    POST /submit              new conversation (or single-shot if no conv_id)
    POST /continue            follow-up in an existing conversation
    POST /result              userscript posts the assistant response
    POST /ack                 userscript heartbeat for a claimed task
    POST /cancel              caller drops a task before result arrives
    POST /close               mark a conversation done
    POST /pin-conv-url        userscript reports the /c/<id> URL it landed on
    POST /retry               re-extract / repeat a prior turn

    GET  /task                userscript polls for next task (?agent=oracle_1)
    GET  /status              queue + agent + session counts (port=8765)
    GET  /task_status/<id>    queued/active/result lookup
    GET  /result/<id>         result record by task_id
    GET  /session/<conv_id>   session history (turns, chatgpt_url, tag)
    GET  /sessions            summary of all known sessions

Hard rules:
  - Server never speaks to chatgpt.com directly. The userscript is the
    only code that touches the model.
  - Server never auto-publishes anything; results land in oracle/ and
    state JSON files. Callers decide what to publish.

Usage:
    python oracle_server.py
"""

from __future__ import annotations

import base64
import json
import sys
import threading
import time
import uuid
from collections import deque
from datetime import datetime, timezone
from http.server import HTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from urllib.parse import unquote, urlparse, parse_qs

PORT = 8765
ORACLE_DIR = Path(__file__).parent / "oracle"
SESSIONS_DIR = ORACLE_DIR / "sessions"

MAX_AGENTS = 3          # max concurrent browser tabs
TASK_TIMEOUT = 14400    # 4 hours — ChatGPT Pro can think 60+ min per task
SESSION_RETENTION_S = 14 * 24 * 3600  # keep sessions on disk for 14 days

# In-memory state (durable copy on disk for sessions)
task_queue: deque[dict] = deque()
results: dict[str, dict] = {}             # task_id -> result
pending_tasks: dict[str, dict] = {}       # agent_id -> task currently in flight
dispatch_times: dict[str, float] = {}     # agent_id -> dispatch timestamp
sessions: dict[str, dict] = {}            # conversation_id -> session record
_lock = threading.RLock()  # reentrant: handlers may chain helper calls under lock


def _is_extraction_failure_response(response: str) -> bool:
    """Detect userscript diagnostics that are not substantive reviews."""
    cleaned = response.strip()
    return cleaned.startswith("ERROR: Response too short or empty")


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _ensure_dirs() -> None:
    SESSIONS_DIR.mkdir(parents=True, exist_ok=True)
    (ORACLE_DIR / "done").mkdir(parents=True, exist_ok=True)
    (ORACLE_DIR / "bad").mkdir(parents=True, exist_ok=True)


def _session_path(conv_id: str) -> Path:
    return SESSIONS_DIR / f"{conv_id}.json"


def _load_session(conv_id: str) -> dict:
    p = _session_path(conv_id)
    if not p.exists():
        return {}
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return {}


def _write_session(session: dict) -> None:
    conv_id = session.get("conversation_id")
    if not conv_id:
        return
    SESSIONS_DIR.mkdir(parents=True, exist_ok=True)
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
        except (json.JSONDecodeError, OSError):
            continue


def _new_conversation_id() -> str:
    return f"conv_{uuid.uuid4().hex[:16]}"


def _record_turn(conv_id: str, turn: dict) -> None:
    with _lock:
        sess = sessions.get(conv_id) or _load_session(conv_id) or {
            "conversation_id": conv_id,
            "created_at": _now_iso(),
            "turns": [],
        }
        sess.setdefault("turns", []).append(turn)
        sess["updated_at"] = _now_iso()
        if turn.get("chatgpt_url"):
            sess["chatgpt_url"] = turn["chatgpt_url"]
        sessions[conv_id] = sess
        _write_session(sess)


class OracleHandler(BaseHTTPRequestHandler):
    """HTTP request handler for oracle bridge."""

    def log_message(self, format, *args):
        """Suppress default logging, use custom."""
        pass

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
        """Handle CORS preflight."""
        self._send_json({})

    def _cleanup_stale_agents(self):
        """Return stale pending tasks (older than TASK_TIMEOUT) to the queue."""
        now = time.time()
        with _lock:
            stale = [aid for aid, t in dispatch_times.items()
                     if now - t > TASK_TIMEOUT and aid in pending_tasks]
            for aid in stale:
                task = pending_tasks.pop(aid)
                dispatch_times.pop(aid, None)
                task_queue.appendleft(task)  # re-queue at front
                print(f"[server] Agent {aid} timed out — task {task['task_id']} returned to queue")

    def _queue_age_seconds(self) -> int:
        """Oldest queued task's age. Used by supervisors to detect stuck tabs."""
        with _lock:
            if not task_queue:
                return 0
            oldest = task_queue[0].get("queued_at_s", 0)
        return int(time.time() - oldest) if oldest else 0

    def _diagnosis(self) -> str:
        with _lock:
            queue_n = len(task_queue)
            agents_n = len(pending_tasks)
        if queue_n > 0 and agents_n == 0:
            return "queue_waiting_for_browser_agent"
        if queue_n == 0 and agents_n == 0:
            return "idle"
        return "running"

    def do_GET(self):
        parsed = urlparse(self.path)
        qs = parse_qs(parsed.query)

        if parsed.path == "/task":
            self._cleanup_stale_agents()
            agent_id = (qs.get("agent", [None])[0]
                        or qs.get("agent_id", [None])[0]
                        or "default")
            resume_task_id = qs.get("resume", [""])[0]
            with _lock:
                if agent_id in pending_tasks:
                    task = pending_tasks[agent_id]
                    if resume_task_id and resume_task_id == task.get("task_id"):
                        self._send_json(task)
                    else:
                        self._send_json({
                            "status": "busy",
                            "assigned_agent": agent_id,
                            "elapsed": int(time.time() - dispatch_times.get(agent_id, time.time())),
                        })
                    return
                if task_queue and len(pending_tasks) < MAX_AGENTS:
                    task = task_queue.popleft()
                    task["assigned_agent"] = agent_id
                    pending_tasks[agent_id] = task
                    dispatch_times[agent_id] = time.time()
                    print(f"[server] Dispatched {task['task_id']} → {agent_id} "
                          f"(conv={(task.get('conversation_id') or '-')[:12]} "
                          f"agents={len(pending_tasks)}/{MAX_AGENTS}, "
                          f"queue={len(task_queue)})")
                    self._send_json(task)
                    return
            self._send_json({"status": "idle"})
            return

        if parsed.path == "/status":
            self._cleanup_stale_agents()
            with _lock:
                agents_info = {
                    aid: {
                        "task_id": t.get("task_id", "?"),
                        "conversation_id": t.get("conversation_id", "") or "",
                        "elapsed": int(time.time() - dispatch_times.get(aid, time.time())),
                    }
                    for aid, t in pending_tasks.items()
                }
                queued_tasks = [
                    {
                        "task_id": t.get("task_id"),
                        "conversation_id": t.get("conversation_id") or "",
                        "age_seconds": int(time.time() - t.get("queued_at_s", time.time())),
                    }
                    for t in task_queue
                ]
                payload = {
                    "port": PORT,
                    "queue_length": len(task_queue),
                    "queued": [t["task_id"] for t in task_queue],
                    "queued_tasks": queued_tasks,
                    "agents_busy": len(pending_tasks),
                    "max_agents": MAX_AGENTS,
                    "agents": agents_info,
                    "active_recent_agents": list(agents_info.keys()),
                    "completed": len(results),
                    "active_sessions": len(sessions),
                    "diagnosis": self._diagnosis(),
                }
            self._send_json(payload)
            return

        if parsed.path.startswith("/task_status/"):
            task_id = unquote(parsed.path.split("/task_status/", 1)[1])
            with _lock:
                if task_id in results:
                    data = dict(results[task_id])
                    data.setdefault("phase", data.get("status", "result"))
                    self._send_json(data)
                    return
                for aid, task in pending_tasks.items():
                    if task.get("task_id") == task_id:
                        self._send_json({
                            "task_id": task_id,
                            "phase": "active",
                            "agent_id": aid,
                            "elapsed": int(time.time() - dispatch_times.get(aid, time.time())),
                        })
                        return
                for idx, task in enumerate(task_queue, start=1):
                    if task.get("task_id") == task_id:
                        self._send_json({
                            "task_id": task_id,
                            "phase": "queued",
                            "position": idx,
                            "queue_length": len(task_queue),
                        })
                        return
            self._send_json({"task_id": task_id, "phase": "not_found"}, 404)
            return

        if parsed.path.startswith("/result/"):
            task_id = parsed.path.split("/result/")[1]
            with _lock:
                rec = results.get(task_id)
            if rec:
                self._send_json(rec)
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
                        "closed_at": s.get("closed_at", ""),
                    }
                    for s in sessions.values()
                ]
            self._send_json({
                "sessions": sorted(summary, key=lambda x: x["updated_at"], reverse=True),
            })
            return

        self._send_json({"error": "unknown endpoint"}, 404)

    def do_POST(self):
        content_length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(content_length).decode("utf-8") if content_length else ""

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
        if self.path == "/cancel":
            self._handle_cancel(data)
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
        if self.path == "/pin-conv-url":
            self._handle_pin_conv_url(data)
            return
        if self.path == "/retry":
            self._handle_retry(data)
            return

        self._send_json({"error": "unknown endpoint"}, 404)

    # ---------------------------- task lifecycle ----------------------------

    def _handle_submit(self, data: dict, *, is_continue: bool) -> None:
        prompt = data.get("prompt", "")
        if not prompt and not data.get("re_extract"):
            self._send_json({"error": "prompt required"}, 400)
            return

        task_id = data.get("task_id") or f"task_{int(time.time())}_{uuid.uuid4().hex[:6]}"
        conv_id = data.get("conversation_id")
        project_url = (data.get("project_url") or "").strip()

        if is_continue:
            if not conv_id:
                self._send_json({"error": "/continue requires conversation_id"}, 400)
                return
            with _lock:
                sess = sessions.get(conv_id) or _load_session(conv_id)
            if not sess:
                self._send_json({"error": f"unknown conversation_id {conv_id}"}, 404)
                return
            chatgpt_url = sess.get("chatgpt_url", "") or project_url
        else:
            # New task. Multi-turn callers may supply a known conv_id (rare); the
            # common case is no conv_id → server issues one. If conv_id is empty
            # the task behaves as single-shot for /result purposes.
            chatgpt_url = ""
            if conv_id is not None:
                conv_id = conv_id or _new_conversation_id()
                with _lock:
                    sess = sessions.get(conv_id) or _load_session(conv_id) or {
                        "conversation_id": conv_id,
                        "created_at": _now_iso(),
                        "turns": [],
                        "tag": data.get("tag", ""),
                        "project_url": project_url,
                    }
                    sessions[conv_id] = sess
                    _write_session(sess)
                chatgpt_url = sess.get("chatgpt_url", "") or project_url

        task: dict = {
            "task_id": task_id,
            "prompt": prompt,
            "conversation_id": conv_id or "",
            "conversation_url": chatgpt_url,
            "project_url": project_url,
            "is_followup": bool(is_continue or chatgpt_url),
            "re_extract": bool(data.get("re_extract", False)),
            "model": data.get("model", "chatgpt-5.4-pro"),
            "tag": data.get("tag", ""),
            "submitted_at": _now_iso(),
            "queued_at_s": time.time(),
            "status": "queued",
        }

        # PDF attachment (optional, single-shot pipeline still uses this)
        if "pdf_base64" in data:
            task["pdf_base64"] = data["pdf_base64"]
            task["pdf_name"] = data.get("pdf_name", "paper.pdf")
        elif "pdf_path" in data:
            pdf_path = Path(data["pdf_path"])
            if pdf_path.exists():
                with open(pdf_path, "rb") as f:
                    task["pdf_base64"] = base64.b64encode(f.read()).decode("ascii")
                task["pdf_name"] = pdf_path.name
                print(f"[server] PDF loaded: {pdf_path.name} ({pdf_path.stat().st_size // 1024} KB)")

        with _lock:
            task_queue.append(task)

        kind = "CONT " if is_continue else ("NEW  " if conv_id else "ONE  ")
        print(f"[server] {kind}queued {task_id} "
              f"conv={(conv_id or '-')[:12]} prompt={len(prompt)} chars "
              f"queue={len(task_queue)} agents={len(pending_tasks)}/{MAX_AGENTS}")
        self._send_json({
            "status": "queued",
            "task_id": task_id,
            "conversation_id": conv_id or "",
            "queue_position": len(task_queue),
        })

    def _handle_cancel(self, data: dict) -> None:
        # Pipeline agents use this when their own oracle wait budget expires.
        task_id = data.get("task_id", "")
        reason = data.get("reason", "cancelled")
        if not task_id:
            self._send_json({"error": "need task_id"}, 400)
            return

        with _lock:
            removed_queue = 0
            kept: deque[dict] = deque()
            while task_queue:
                task = task_queue.popleft()
                if task.get("task_id") == task_id:
                    removed_queue += 1
                else:
                    kept.append(task)
            task_queue.extend(kept)

            removed_agents: list[str] = []
            for aid, task in list(pending_tasks.items()):
                if task.get("task_id") == task_id:
                    del pending_tasks[aid]
                    dispatch_times.pop(aid, None)
                    removed_agents.append(aid)

            results[task_id] = {
                "task_id": task_id,
                "response": "",
                "timestamp": _now_iso(),
                "model": "",
                "status": "cancelled",
                "reason": reason,
            }

        print(f"[server] Cancelled {task_id}: queue={removed_queue}, "
              f"agents={removed_agents or '-'} ({reason})")
        self._send_json({
            "status": "cancelled",
            "task_id": task_id,
            "removed_queue": removed_queue,
            "removed_agents": removed_agents,
        })

    def _handle_result(self, data: dict) -> None:
        response = data.get("response", "")
        agent_id = data.get("agent_id", "")
        chatgpt_url = data.get("chatgpt_url", "")
        task_id = data.get("task_id", "")

        # Reconcile task_id from the agent's pending task — pipeline's stable ID
        # wins over any ID the userscript carries internally.
        with _lock:
            if agent_id and agent_id in pending_tasks:
                task_id = pending_tasks[agent_id]["task_id"]
            if not task_id or not response:
                self._send_json({"error": "need task_id and response"}, 400)
                return

            # Pull the matching pending task (carries our conversation_id)
            task = None
            for aid in list(pending_tasks):
                if pending_tasks[aid].get("task_id") == task_id:
                    task = pending_tasks.pop(aid)
                    dispatch_times.pop(aid, None)
                    break
            extraction_failed = _is_extraction_failure_response(response)
            conv_id = (task or {}).get("conversation_id", "") or ""

            record = {
                "task_id": task_id,
                "response": response,
                "conversation_id": conv_id,
                "chatgpt_url": chatgpt_url or (task or {}).get("conversation_url", ""),
                "timestamp": _now_iso(),
                "model": data.get("model", ""),
                "agent_id": agent_id,
                "status": "failed" if extraction_failed else "completed",
                "reason": "extraction_failure" if extraction_failed else "",
                "response_chars": len(response),
            }
            results[task_id] = record

        if conv_id:
            _record_turn(conv_id, {
                "task_id": task_id,
                "prompt": (task or {}).get("prompt", ""),
                "response": response,
                "chatgpt_url": chatgpt_url,
                "completed_at": record["timestamp"],
                "model": record["model"],
                "response_chars": len(response),
            })

        # Mirror to disk for offline inspection.
        _ensure_dirs()
        done_dir = ORACLE_DIR / ("bad" if extraction_failed else "done")
        out_file = done_dir / f"{task_id}.md"
        metadata = {
            "timestamp": record["timestamp"],
            "model": record["model"] or "chatgpt-5.4-pro",
            "response_length": len(response),
            "agent_id": agent_id,
            "conversation_id": conv_id,
            "chatgpt_url": record["chatgpt_url"],
        }
        try:
            out_file.write_text(
                f"<!-- oracle metadata: {json.dumps(metadata, ensure_ascii=False)} -->\n\n{response}",
                encoding="utf-8",
            )
        except OSError as exc:
            print(f"[server] WARN: failed to mirror result to {out_file}: {exc}")

        kind = "Extraction failure" if extraction_failed else "Result"
        print(f"[server] {kind}: {task_id} ({len(response)} chars) "
              f"conv={(conv_id or '-')[:12]} freed={agent_id or '-'} "
              f"agents={len(pending_tasks)}/{MAX_AGENTS}, queue={len(task_queue)}")
        print(f"[server] Saved to: {out_file}")
        self._send_json({"status": "saved", "task_id": task_id})

    def _handle_ack(self, data: dict) -> None:
        task_id = data.get("task_id", "")
        agent_id = data.get("agent_id", "?")
        with _lock:
            if agent_id in dispatch_times:
                dispatch_times[agent_id] = time.time()
        print(f"[server] Ack: {task_id} by {agent_id}")
        self._send_json({"status": "ok"})

    def _handle_close(self, data: dict) -> None:
        conv_id = data.get("conversation_id", "")
        if not conv_id:
            self._send_json({"error": "conversation_id required"}, 400)
            return
        with _lock:
            sess = sessions.get(conv_id) or _load_session(conv_id)
            if sess:
                sess["closed_at"] = _now_iso()
                sessions[conv_id] = sess
                _write_session(sess)
        self._send_json({"status": "closed", "conversation_id": conv_id})

    def _handle_pin_conv_url(self, data: dict) -> None:
        """Userscript reports the /c/<uuid> URL it landed on for an in-flight task.

        Pin the URL to the task's conversation so future re-extract / follow-up
        tasks know where to navigate.
        """
        task_id = data.get("task_id", "")
        chatgpt_url = data.get("chatgpt_url", "")
        if not task_id or not chatgpt_url:
            self._send_json({"error": "task_id and chatgpt_url required"}, 400)
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
                "conversation_id": conv_id,
                "created_at": _now_iso(),
                "turns": [],
            }
            sess["chatgpt_url"] = chatgpt_url
            sess["updated_at"] = _now_iso()
            sessions[conv_id] = sess
            _write_session(sess)
        print(f"[server] pinned chatgpt_url={chatgpt_url[-50:]} to conv={conv_id[:12]}")
        self._send_json({"status": "pinned", "conversation_id": conv_id, "chatgpt_url": chatgpt_url})

    def _handle_retry(self, data: dict) -> None:
        """Re-queue an existing task as a re-extract task.

        Used when oracle review came back ERROR / sub-threshold but the
        ChatGPT conversation actually has a real response. We re-dispatch
        the same conv with re_extract=True so the userscript navigates back
        and reads the latest assistant message; if no chatgpt_url is pinned,
        we instead enqueue a follow-up that asks for verbatim repeat.
        """
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
                "model": data.get("model", "chatgpt-5.4-pro"),
                "tag": data.get("tag", "retry"),
                "submitted_at": _now_iso(),
                "queued_at_s": time.time(),
                "status": "queued",
            }
            mode = "re-extract"
        else:
            task = {
                "task_id": new_task_id,
                "prompt": ("Please paste your final review from the previous turn verbatim, "
                           "no preamble, no commentary, just the review text."),
                "conversation_id": conv_id,
                "conversation_url": "",
                "is_followup": True,
                "model": data.get("model", "chatgpt-5.4-pro"),
                "tag": data.get("tag", "retry-repeat"),
                "submitted_at": _now_iso(),
                "queued_at_s": time.time(),
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


# --------------------------------------------------------------------------- #
# Convenience helpers (used by oracle_dispatch / pipeline scripts)            #
# --------------------------------------------------------------------------- #


def submit_task(prompt: str, pdf_path: Path | None = None,
                task_id: str | None = None, model: str = "chatgpt-5.4-pro",
                conversation_id: str | None = None,
                project_url: str = "",
                tag: str = "") -> dict:
    """Submit a task to the server (called by agents).

    When `conversation_id` is None, behaves as legacy single-shot. When set
    (even to "" → server issues), behaves as multi-turn-capable new
    conversation.
    """
    import urllib.request

    if not task_id:
        task_id = f"task_{int(time.time())}"

    data: dict = {
        "task_id": task_id,
        "prompt": prompt,
        "model": model,
        "tag": tag,
    }
    if conversation_id is not None:
        data["conversation_id"] = conversation_id
    if project_url:
        data["project_url"] = project_url
    if pdf_path and pdf_path.exists():
        data["pdf_path"] = str(pdf_path)

    req = urllib.request.Request(
        f"http://localhost:{PORT}/submit",
        data=json.dumps(data).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    resp = urllib.request.urlopen(req, timeout=10)
    return json.loads(resp.read().decode("utf-8"))


def submit_continue(prompt: str, conversation_id: str,
                    task_id: str | None = None,
                    model: str = "chatgpt-5.4-pro",
                    tag: str = "") -> dict:
    """Follow up in an existing conversation."""
    import urllib.request

    if not task_id:
        task_id = f"cont_{int(time.time())}"
    data = {
        "task_id": task_id,
        "prompt": prompt,
        "model": model,
        "tag": tag,
        "conversation_id": conversation_id,
    }
    req = urllib.request.Request(
        f"http://localhost:{PORT}/continue",
        data=json.dumps(data).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    resp = urllib.request.urlopen(req, timeout=10)
    return json.loads(resp.read().decode("utf-8"))


def wait_for_result(task_id: str, timeout: int = 900) -> str:
    """Poll the server for a task result; returns response text or ''."""
    import urllib.request

    start = time.time()
    while time.time() - start < timeout:
        try:
            resp = urllib.request.urlopen(
                f"http://localhost:{PORT}/result/{task_id}", timeout=5
            )
            data = json.loads(resp.read().decode("utf-8"))
            if data.get("status") == "completed":
                return data["response"]
            if data.get("status") in {"failed", "cancelled"}:
                return ""
        except Exception:
            pass

        elapsed = int(time.time() - start)
        if elapsed and elapsed % 30 == 0:
            print(f"[dispatch] Waiting for {task_id}... ({elapsed}s)")
        time.sleep(3)

    return ""


def wait_for_result_record(task_id: str, timeout: int = 900) -> dict:
    """Like wait_for_result but returns the full record (incl. conversation_id)."""
    import urllib.request

    start = time.time()
    while time.time() - start < timeout:
        try:
            resp = urllib.request.urlopen(
                f"http://localhost:{PORT}/result/{task_id}", timeout=5
            )
            data = json.loads(resp.read().decode("utf-8"))
            if data.get("status") in {"completed", "failed", "cancelled"}:
                return data
        except Exception:
            pass
        time.sleep(3)
    return {"status": "timeout", "task_id": task_id, "response": ""}


def close_conversation(conversation_id: str) -> dict:
    import urllib.request

    req = urllib.request.Request(
        f"http://localhost:{PORT}/close",
        data=json.dumps({"conversation_id": conversation_id}).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    resp = urllib.request.urlopen(req, timeout=10)
    return json.loads(resp.read().decode("utf-8"))


def main():
    _ensure_dirs()
    _hydrate_sessions()
    server = HTTPServer(("127.0.0.1", PORT), OracleHandler)
    print(f"[server] Oracle server running on http://localhost:{PORT}")
    print(f"[server] Sessions dir: {SESSIONS_DIR}")
    print(f"[server] Hydrated {len(sessions)} session(s) from disk")
    print(f"[server] Max {MAX_AGENTS} concurrent agents (single-shot + multi-turn)")
    print(f"[server] Open browser tabs:")
    for i in range(1, MAX_AGENTS + 1):
        print(f"  Tab {i}: https://chatgpt.com/?oracle={i}")
    print(f"[server] Press Ctrl+C to stop.\n")

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n[server] Stopped.")
        server.server_close()


if __name__ == "__main__":
    main()
