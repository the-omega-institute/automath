#!/usr/bin/env python3
"""ChatGPT Oracle Server — local HTTP bridge for browser automation.

Bridges between any agent/CLI and a Tampermonkey userscript running
inside Chrome on chatgpt.com.

    python oracle_server.py              # start server
    curl localhost:8765/status           # check status
"""

from __future__ import annotations

import base64
import json
import time
from http.server import HTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from datetime import datetime
from collections import deque

PORT = 8765
DONE_DIR = Path(__file__).parent / "done"

task_queue: deque[dict] = deque()
results: dict[str, dict] = {}
pending_task: dict | None = None


class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass

    def _json(self, data: dict, status: int = 200):
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()
        self.wfile.write(json.dumps(data).encode("utf-8"))

    def do_OPTIONS(self):
        self._json({})

    def do_GET(self):
        global pending_task
        if self.path == "/task":
            if pending_task:
                self._json(pending_task)
            elif task_queue:
                pending_task = task_queue.popleft()
                print(f"[server] Dispatch: {pending_task['task_id']}")
                self._json(pending_task)
            else:
                self._json({"status": "idle"})
        elif self.path == "/status":
            self._json({
                "queue": len(task_queue),
                "pending": pending_task["task_id"] if pending_task else None,
                "done": len(results),
            })
        elif self.path.startswith("/result/"):
            tid = self.path.split("/result/")[1]
            self._json(results[tid] if tid in results else {"status": "not_found"}, 200 if tid in results else 404)
        else:
            self._json({"error": "not found"}, 404)

    def do_POST(self):
        global pending_task
        body = self.rfile.read(int(self.headers.get("Content-Length", 0))).decode("utf-8")
        try:
            data = json.loads(body) if body else {}
        except json.JSONDecodeError:
            self._json({"error": "bad json"}, 400)
            return

        if self.path == "/submit":
            tid = data.get("task_id", f"task_{int(time.time())}")
            task = {"task_id": tid, "prompt": data.get("prompt", ""), "model": data.get("model", ""), "status": "queued"}
            if "pdf_base64" in data:
                task["pdf_base64"] = data["pdf_base64"]
                task["pdf_name"] = data.get("pdf_name", "paper.pdf")
            elif "pdf_path" in data:
                p = Path(data["pdf_path"])
                if p.exists():
                    task["pdf_base64"] = base64.b64encode(p.read_bytes()).decode("ascii")
                    task["pdf_name"] = p.name
            task_queue.append(task)
            print(f"[server] Queued: {tid} ({len(task['prompt'])} chars)")
            self._json({"status": "queued", "task_id": tid, "position": len(task_queue)})

        elif self.path == "/result":
            tid = data.get("task_id", "")
            response = data.get("response", "")
            if not tid or not response:
                self._json({"error": "need task_id and response"}, 400)
                return
            results[tid] = {"task_id": tid, "response": response, "timestamp": datetime.now().isoformat(), "status": "completed"}
            DONE_DIR.mkdir(parents=True, exist_ok=True)
            out = DONE_DIR / f"{tid}.md"
            meta = {"timestamp": datetime.now().isoformat(), "model": data.get("model", ""), "length": len(response)}
            out.write_text(f"<!-- {json.dumps(meta)} -->\n\n{response}", encoding="utf-8")
            if pending_task and pending_task["task_id"] == tid:
                pending_task = None
            print(f"[server] Done: {tid} ({len(response)} chars) -> {out}")
            self._json({"status": "saved", "task_id": tid})

        elif self.path == "/ack":
            print(f"[server] Ack: {data.get('task_id', '?')}")
            self._json({"status": "ok"})
        else:
            self._json({"error": "not found"}, 404)


if __name__ == "__main__":
    DONE_DIR.mkdir(parents=True, exist_ok=True)
    srv = HTTPServer(("127.0.0.1", PORT), Handler)
    print(f"Oracle server on http://localhost:{PORT}  (Ctrl+C to stop)")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")
        srv.server_close()
