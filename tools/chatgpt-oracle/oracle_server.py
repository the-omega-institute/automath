#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Local HTTP server for ChatGPT oracle automation.

Bridges between Claude agents and a Tampermonkey userscript running
inside the user's Chrome browser on chatgpt.com.

Usage:
    # Start the server (keep running):
    python oracle_server.py

    # Agents submit tasks via oracle_dispatch.py or directly:
    curl -X POST http://localhost:8765/submit -d '{"prompt":"...", "pdf":"base64..."}'

    # The Tampermonkey userscript polls /task, processes it in ChatGPT,
    # and POSTs the result to /result.
"""

from __future__ import annotations

import base64
import json
import sys
import threading
import time
from http.server import HTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from datetime import datetime
from collections import deque

PORT = 8765
ORACLE_DIR = Path(__file__).parent / "oracle"

# Task queue (thread-safe via GIL for simple operations)
task_queue: deque[dict] = deque()
results: dict[str, dict] = {}  # task_id -> result
pending_task: dict | None = None  # currently dispatched to browser


class OracleHandler(BaseHTTPRequestHandler):
    """HTTP request handler for oracle bridge."""

    def log_message(self, format, *args):
        """Suppress default logging, use custom."""
        pass

    def _send_json(self, data: dict, status: int = 200):
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()
        self.wfile.write(json.dumps(data).encode("utf-8"))

    def do_OPTIONS(self):
        """Handle CORS preflight."""
        self._send_json({})

    def do_GET(self):
        global pending_task

        if self.path == "/task":
            # Tampermonkey polls this endpoint for new tasks
            if pending_task:
                self._send_json(pending_task)
            elif task_queue:
                pending_task = task_queue.popleft()
                print(f"[server] Dispatching task: {pending_task['task_id']}")
                self._send_json(pending_task)
            else:
                self._send_json({"status": "idle"})

        elif self.path == "/status":
            # Optional ?agent_id= filter
            from urllib.parse import urlparse, parse_qs
            qs = parse_qs(urlparse(self.path).query)
            aid = qs.get("agent_id", [None])[0]
            if aid:
                filtered_q = sum(1 for t in task_queue if t.get("agent_id") == aid)
                filtered_r = sum(1 for r in results.values() if r.get("agent_id") == aid)
                self._send_json({
                    "queue_length": filtered_q,
                    "pending": pending_task["task_id"] if pending_task and pending_task.get("agent_id") == aid else None,
                    "completed": filtered_r,
                    "agent_id": aid,
                })
            else:
                self._send_json({
                    "queue_length": len(task_queue),
                    "pending": pending_task["task_id"] if pending_task else None,
                    "completed": len(results),
                })

        elif self.path.startswith("/result/"):
            task_id = self.path.split("/result/")[1]
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
            # Agent submits a new task
            # agent_id isolates results so multiple agents don't collide
            agent_id = data.get("agent_id", "default")
            task_id = data.get("task_id", f"task_{int(time.time())}")
            task = {
                "task_id": task_id,
                "agent_id": agent_id,
                "prompt": data.get("prompt", ""),
                "model": data.get("model", "chatgpt-5.4-pro"),
                "status": "queued",
            }

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
            print(f"[server] Task queued: {task_id} ({len(task['prompt'])} chars prompt)")
            self._send_json({"status": "queued", "task_id": task_id, "position": len(task_queue)})

        elif self.path == "/result":
            # Tampermonkey posts the ChatGPT response
            task_id = data.get("task_id", "")
            response = data.get("response", "")

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
            }
            out_file.write_text(
                f"<!-- oracle metadata: {json.dumps(metadata)} -->\n\n{response}",
                encoding="utf-8",
            )

            # Clear pending task
            if pending_task and pending_task["task_id"] == task_id:
                pending_task = None

            print(f"[server] Result received: {task_id} ({len(response)} chars)")
            print(f"[server] Saved to: {out_file}")
            self._send_json({"status": "saved", "task_id": task_id})

        elif self.path == "/ack":
            # Tampermonkey acknowledges it picked up the task
            task_id = data.get("task_id", "")
            print(f"[server] Task acknowledged by browser: {task_id}")
            self._send_json({"status": "ok"})

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
        f"http://localhost:{PORT}/submit",
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
                f"http://localhost:{PORT}/result/{task_id}", timeout=5
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
    server = HTTPServer(("127.0.0.1", PORT), OracleHandler)
    print(f"[server] Oracle server running on http://localhost:{PORT}")
    print(f"[server] Install the Tampermonkey userscript, then open https://chatgpt.com")
    print(f"[server] Press Ctrl+C to stop.\n")

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n[server] Stopped.")
        server.server_close()


if __name__ == "__main__":
    main()
