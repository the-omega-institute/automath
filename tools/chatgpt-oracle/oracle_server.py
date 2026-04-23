#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Local HTTP server for ChatGPT oracle automation.

Bridges between Claude agents and a Tampermonkey userscript running
inside the user's Chrome browser on chatgpt.com.

Usage:
    # Start the server (keep running):
    python oracle_server.py

    # Agents submit tasks via oracle_dispatch.py or directly:
    curl -X POST http://127.0.0.1:8765/submit -d '{"prompt":"...", "pdf":"base64..."}'

    # The Tampermonkey userscript polls /task, processes it in ChatGPT,
    # and POSTs the result to /result.
"""

from __future__ import annotations

import base64
import json
import sys
import threading
import time
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from datetime import datetime
from collections import deque

PORT = 8765
ORACLE_DIR = Path(__file__).parent / "oracle"

MAX_AGENTS = 3          # max concurrent browser tabs
TASK_TIMEOUT = 14400    # 4 hours; ChatGPT Pro can think 60+ min per task

# Task queue (thread-safe via GIL for simple operations)
task_queue: deque[dict] = deque()
results: dict[str, dict] = {}  # task_id -> result
# Multi-agent: each browser tab claims a slot keyed by agent_id
pending_tasks: dict[str, dict] = {}   # agent_id -> task
# Track when each task was dispatched (for timeout cleanup)
dispatch_times: dict[str, float] = {}  # agent_id -> timestamp
agent_phases: dict[str, dict] = {}     # agent_id -> latest browser-side phase


class OracleHandler(BaseHTTPRequestHandler):
    """HTTP request handler for oracle bridge."""

    def log_message(self, format, *args):
        """Suppress default logging, use custom."""
        pass

    def _send_json(self, data: dict, status: int = 200):
        try:
            self.send_response(status)
            self.send_header("Content-Type", "application/json")
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
            self.send_header("Access-Control-Allow-Headers", "Content-Type")
            self.end_headers()
            self.wfile.write(json.dumps(data).encode("utf-8"))
        except (BrokenPipeError, ConnectionAbortedError, ConnectionResetError):
            return

    def do_OPTIONS(self):
        """Handle CORS preflight."""
        self._send_json({})

    def _cleanup_stale_agents(self):
        """Return stale pending tasks (older than TASK_TIMEOUT) to the queue."""
        now = time.time()
        stale = [aid for aid, t in dispatch_times.items()
                 if now - t > TASK_TIMEOUT and aid in pending_tasks]
        for aid in stale:
            task = pending_tasks.pop(aid)
            dispatch_times.pop(aid, None)
            task_queue.appendleft(task)  # re-queue at front
            print(f"[server] Agent {aid} timed out; task {task['task_id']} returned to queue")

    def do_GET(self):
        from urllib.parse import urlparse, parse_qs
        parsed = urlparse(self.path)
        qs = parse_qs(parsed.query)

        if parsed.path == "/task":
            self._cleanup_stale_agents()
            # Agent identifies itself via ?agent=oracle_1 (or legacy no-param)
            agent_id = (qs.get("agent", [None])[0]
                        or qs.get("agent_id", [None])[0]
                        or "default")

            if agent_id in pending_tasks:
                # Already has a task; return it (idempotent poll)
                self._send_json(pending_tasks[agent_id])
            elif task_queue and len(pending_tasks) < MAX_AGENTS:
                # Assign next task from queue to this agent
                task = task_queue.popleft()
                task["assigned_agent"] = agent_id
                pending_tasks[agent_id] = task
                dispatch_times[agent_id] = time.time()
                print(f"[server] Dispatched {task['task_id']} -> {agent_id} "
                      f"(agents={len(pending_tasks)}/{MAX_AGENTS}, queue={len(task_queue)})")
                self._send_json(task)
            else:
                self._send_json({"status": "idle"})

        elif parsed.path == "/status":
            self._cleanup_stale_agents()
            agents_info = {
                aid: {"task_id": t["task_id"],
                      "elapsed": int(time.time() - dispatch_times.get(aid, time.time())),
                      "phase": agent_phases.get(aid, {}).get("phase", "assigned"),
                      "last_seen": agent_phases.get(aid, {}).get("last_seen", None)}
                for aid, t in pending_tasks.items()
            }
            self._send_json({
                "queue_length": len(task_queue),
                "agents_busy": len(pending_tasks),
                "max_agents": MAX_AGENTS,
                "agents": agents_info,
                "completed": len(results),
            })

        elif parsed.path.startswith("/result/"):
            task_id = parsed.path.split("/result/")[1]
            if task_id in results:
                self._send_json(results[task_id])
            else:
                self._send_json({"status": "not_found"}, 404)

        else:
            self._send_json({"error": "unknown endpoint"}, 404)

    def do_POST(self):
        global pending_task

        content_length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(content_length).decode("utf-8")

        try:
            data = json.loads(body) if body else {}
        except json.JSONDecodeError:
            self._send_json({"error": "invalid JSON"}, 400)
            return

        if self.path == "/submit":
            # Pipeline agent submits a new task to the queue
            task_id = data.get("task_id", f"task_{int(time.time())}")
            task = {
                "task_id": task_id,
                "prompt": data.get("prompt", ""),
                "model": data.get("model", "chatgpt-5.4-pro"),
                "status": "queued",
            }
            if "min_response_length" in data:
                task["min_response_length"] = data["min_response_length"]
            if "task_kind" in data:
                task["task_kind"] = data["task_kind"]

            # Handle PDF: either base64 data or file path
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

            task_queue.append(task)
            print(f"[server] Task queued: {task_id} "
                  f"({len(task['prompt'])} chars, queue={len(task_queue)}, "
                  f"agents={len(pending_tasks)}/{MAX_AGENTS})")
            self._send_json({"status": "queued", "task_id": task_id,
                             "position": len(task_queue)})

        elif self.path == "/result":
            # Browser tab posts the ChatGPT response
            response = data.get("response", "")
            agent_id = data.get("agent_id", "")
            # Prefer the server-side pending assignment.  Browser automation can
            # survive ChatGPT page navigation, and stale userscript task ids must
            # not be allowed to complete the wrong pipeline task.
            task_id = data.get("task_id", "")
            if agent_id and agent_id in pending_tasks:
                task_id = pending_tasks[agent_id]["task_id"]

            if not task_id or not response:
                self._send_json({"error": "need task_id and response"}, 400)
                return

            # Save result
            results[task_id] = {
                "task_id": task_id,
                "response": response,
                "timestamp": datetime.now().isoformat(),
                "model": data.get("model", ""),
                "status": "completed",
            }

            # Save to file
            done_dir = ORACLE_DIR / "done"
            done_dir.mkdir(parents=True, exist_ok=True)
            out_file = done_dir / f"{task_id}.md"
            metadata = {
                "timestamp": datetime.now().isoformat(),
                "model": data.get("model", "chatgpt-5.4-pro"),
                "response_length": len(response),
                "agent_id": agent_id,
            }
            out_file.write_text(
                f"<!-- oracle metadata: {json.dumps(metadata)} -->\n\n{response}",
                encoding="utf-8",
            )

            # Free the agent slot that held this task
            freed = ""
            for aid in list(pending_tasks):
                if pending_tasks[aid]["task_id"] == task_id:
                    del pending_tasks[aid]
                    dispatch_times.pop(aid, None)
                    agent_phases.pop(aid, None)
                    freed = f" (freed {aid})"
                    break

            print(f"[server] Result: {task_id} ({len(response)} chars){freed} "
                  f"- agents={len(pending_tasks)}/{MAX_AGENTS}, queue={len(task_queue)}")
            print(f"[server] Saved to: {out_file}")
            self._send_json({"status": "saved", "task_id": task_id})

        elif self.path == "/ack":
            # Browser tab acknowledges it picked up the task
            task_id = data.get("task_id", "")
            agent_id = data.get("agent_id", "?")
            # Refresh dispatch time to prevent timeout
            if agent_id in dispatch_times:
                dispatch_times[agent_id] = time.time()
            agent_phases[agent_id] = {
                "task_id": task_id,
                "phase": data.get("phase", "ack"),
                "last_seen": datetime.now().isoformat(),
            }
            print(f"[server] Ack: {task_id} by {agent_id}")
            self._send_json({"status": "ok"})

        elif self.path == "/phase":
            task_id = data.get("task_id", "")
            agent_id = data.get("agent_id", "?")
            if agent_id in dispatch_times:
                dispatch_times[agent_id] = time.time()
            agent_phases[agent_id] = {
                "task_id": task_id,
                "phase": data.get("phase", "unknown"),
                "last_seen": datetime.now().isoformat(),
                "detail": data.get("detail", ""),
            }
            self._send_json({"status": "ok"})

        elif self.path == "/release":
            task_id = data.get("task_id", "")
            agent_id = data.get("agent_id", "")
            reason = data.get("reason", "unspecified")
            released = False
            if agent_id in pending_tasks and pending_tasks[agent_id].get("task_id") == task_id:
                task = pending_tasks.pop(agent_id)
                dispatch_times.pop(agent_id, None)
                agent_phases.pop(agent_id, None)
                task_queue.appendleft(task)
                released = True
                print(f"[server] Released {task_id} from {agent_id}: {reason}")
            self._send_json({"status": "released" if released else "not_pending"})

        elif self.path == "/cancel":
            task_id = data.get("task_id", "")
            reason = data.get("reason", "unspecified")
            removed = False
            for aid in list(pending_tasks):
                if pending_tasks[aid].get("task_id") == task_id:
                    del pending_tasks[aid]
                    dispatch_times.pop(aid, None)
                    agent_phases.pop(aid, None)
                    removed = True
            if task_id:
                kept = deque()
                while task_queue:
                    task = task_queue.popleft()
                    if task.get("task_id") == task_id:
                        removed = True
                    else:
                        kept.append(task)
                task_queue.extend(kept)
            if removed:
                print(f"[server] Canceled {task_id}: {reason}")
            self._send_json({"status": "canceled" if removed else "not_found"})

        else:
            self._send_json({"error": "unknown endpoint"}, 404)


def submit_task(prompt: str, pdf_path: Path | None = None,
                task_id: str | None = None, model: str = "chatgpt-5.4-pro"):
    """Submit a task to the server (called by agents)."""
    import urllib.request

    if not task_id:
        task_id = f"task_{int(time.time())}"

    data: dict = {
        "task_id": task_id,
        "prompt": prompt,
        "model": model,
    }

    if pdf_path and pdf_path.exists():
        data["pdf_path"] = str(pdf_path)

    req = urllib.request.Request(
        f"http://127.0.0.1:{PORT}/submit",
        data=json.dumps(data).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    resp = urllib.request.urlopen(req, timeout=10)
    return json.loads(resp.read().decode("utf-8"))


def wait_for_result(task_id: str, timeout: int = 900) -> str:
    """Poll the server for a task result."""
    import urllib.request

    start = time.time()
    while time.time() - start < timeout:
        try:
            resp = urllib.request.urlopen(
                f"http://127.0.0.1:{PORT}/result/{task_id}", timeout=5
            )
            data = json.loads(resp.read().decode("utf-8"))
            if data.get("status") == "completed":
                return data["response"]
        except Exception:
            pass

        elapsed = int(time.time() - start)
        if elapsed % 30 == 0 and elapsed > 0:
            print(f"[dispatch] Waiting for {task_id}... ({elapsed}s)")
        time.sleep(3)

    return ""


def main():
    server = ThreadingHTTPServer(("127.0.0.1", PORT), OracleHandler)
    print(f"[server] Oracle server running on http://127.0.0.1:{PORT}")
    print(f"[server] Max {MAX_AGENTS} concurrent agents")
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
