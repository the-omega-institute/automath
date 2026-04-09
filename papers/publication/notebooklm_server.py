#!/usr/bin/env python3
"""NotebookLM Oracle Server — HTTP bridge for NotebookLM automation.

Port 8766 (separate from ChatGPT oracle on 8765).
Same protocol as oracle_server.py but for NotebookLM tasks.

Tasks: upload PDF sources → generate audio overview / study guide / chat
"""

import json
import os
import threading
from http.server import HTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from datetime import datetime

PORT = 8766
DONE_DIR = Path(__file__).parent / "notebooklm" / "done"
DONE_DIR.mkdir(parents=True, exist_ok=True)

# ── State ─────────────────────────────────────────────────────────────
task_queue = []
current_task = None
completed = []
lock = threading.Lock()


class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass  # suppress default logging

    def _json(self, code, data):
        body = json.dumps(data).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Content-Length", len(body))
        self.end_headers()
        self.wfile.write(body)

    def _read_body(self):
        length = int(self.headers.get("Content-Length", 0))
        return json.loads(self.rfile.read(length)) if length else {}

    def do_OPTIONS(self):
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()

    def do_GET(self):
        global current_task
        if self.path == "/status":
            with lock:
                self._json(200, {
                    "queue_length": len(task_queue),
                    "pending": current_task["task_id"] if current_task else None,
                    "completed": len(completed),
                })
        elif self.path == "/task":
            with lock:
                if current_task:
                    self._json(200, current_task)
                elif task_queue:
                    current_task = task_queue.pop(0)
                    self._json(200, current_task)
                else:
                    self._json(200, {"status": "idle"})
        else:
            self._json(404, {"error": "not found"})

    def do_POST(self):
        global current_task
        data = self._read_body()

        if self.path == "/submit":
            task_id = data.get("task_id", f"nlm_{datetime.now().strftime('%H%M%S')}")
            data["task_id"] = task_id
            data["status"] = "pending"
            with lock:
                task_queue.append(data)
                pos = len(task_queue)
            self._json(200, {"status": "queued", "task_id": task_id, "position": pos})

        elif self.path == "/ack":
            self._json(200, {"status": "acked"})

        elif self.path == "/result":
            task_id = data.get("task_id", "unknown")
            response = data.get("response", "")
            # Save result
            safe_id = "".join(c if c.isalnum() or c in "_-" else "_" for c in task_id)
            out = DONE_DIR / f"{safe_id}.md"
            meta = {
                "timestamp": datetime.now().isoformat(),
                "task_id": task_id,
                "response_length": len(response),
                "task_type": data.get("task_type", "unknown"),
            }
            out.write_text(
                f"<!-- notebooklm metadata: {json.dumps(meta)} -->\n\n{response}",
                encoding="utf-8",
            )
            with lock:
                completed.append(task_id)
                current_task = None
            self._json(200, {"status": "saved", "task_id": task_id})
        else:
            self._json(404, {"error": "not found"})


if __name__ == "__main__":
    print(f"NotebookLM Oracle Server on http://localhost:{PORT}")
    HTTPServer(("", PORT), Handler).serve_forever()
