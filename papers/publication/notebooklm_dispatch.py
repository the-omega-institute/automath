#!/usr/bin/env python3
"""Dispatch tasks to NotebookLM via the oracle bridge (port 8766).

Usage:
    python notebooklm_dispatch.py --paper <paper_dir> --type audio_overview
    python notebooklm_dispatch.py --paper <paper_dir> --type chat --prompt "Summarize key results"
    python notebooklm_dispatch.py --paper <paper_dir> --type study_guide
"""

import argparse
import base64
import json
import sys
import time
import urllib.request
from pathlib import Path

SERVER = "http://localhost:8766"
PUBLICATION_DIR = Path(__file__).parent


def post_json(path: str, data: dict) -> dict:
    body = json.dumps(data).encode()
    req = urllib.request.Request(
        f"{SERVER}{path}",
        data=body,
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=30) as resp:
        return json.loads(resp.read())


def get_json(path: str) -> dict:
    with urllib.request.urlopen(f"{SERVER}{path}", timeout=10) as resp:
        return json.loads(resp.read())


def find_pdf(paper_dir: Path) -> Path | None:
    """Find compiled PDF in paper directory."""
    candidates = list(paper_dir.glob("*.pdf"))
    if not candidates:
        candidates = list(paper_dir.glob("**/*.pdf"))
    if candidates:
        # Prefer main.pdf or the largest
        for c in candidates:
            if c.stem == "main":
                return c
        candidates.sort(key=lambda f: f.stat().st_size, reverse=True)
        return candidates[0]
    return None


def submit_task(paper_dir: Path, task_type: str, prompt: str = None,
                task_id: str = None) -> dict:
    """Submit a task to the NotebookLM oracle server."""
    pdf_path = find_pdf(paper_dir)
    if not pdf_path:
        print(f"[nlm] ERROR: No PDF found in {paper_dir}")
        sys.exit(1)

    print(f"[nlm] PDF: {pdf_path.name} ({pdf_path.stat().st_size / 1024:.0f} KB)")

    pdf_b64 = base64.b64encode(pdf_path.read_bytes()).decode("ascii")
    paper_name = paper_dir.name.replace("2026_", "")

    if not task_id:
        short = "_".join(paper_name.split("_")[:3])
        task_id = f"nlm_{short}_{task_type}"

    payload = {
        "task_id": task_id,
        "task_type": task_type,
        "pdf_base64": pdf_b64,
        "pdf_name": f"{paper_dir.name}.pdf",
    }

    if prompt:
        payload["prompt"] = prompt
    elif task_type == "study_guide":
        payload["prompt"] = (
            "Please generate a comprehensive study guide for this mathematical paper. "
            "Include: (1) Key definitions and notation, (2) Main theorems and their significance, "
            "(3) Proof strategy overview, (4) Open questions, (5) Prerequisites for understanding."
        )
    elif task_type == "chat":
        payload["prompt"] = prompt or "Summarize the main contributions of this paper."

    result = post_json("/submit", payload)
    print(f"[nlm] Submitted: {result}")
    return result


def wait_for_result(task_id: str, timeout: int = 3600) -> str | None:
    """Poll server for task completion."""
    start = time.time()
    last_log = 0

    while time.time() - start < timeout:
        try:
            status = get_json("/status")
            elapsed = int(time.time() - start)

            if elapsed - last_log >= 60:
                last_log = elapsed
                print(f"[nlm] Waiting... {elapsed}s, queue={status.get('queue_length', '?')}, "
                      f"pending={status.get('pending', 'none')}, "
                      f"completed={status.get('completed', 0)}")

            # Check if our task completed
            if status.get("pending") is None and status.get("queue_length", 0) == 0:
                # Check done directory
                done_dir = PUBLICATION_DIR / "notebooklm" / "done"
                safe_id = "".join(c if c.isalnum() or c in "_-" else "_" for c in task_id)
                result_file = done_dir / f"{safe_id}.md"
                if result_file.exists():
                    content = result_file.read_text(encoding="utf-8")
                    print(f"[nlm] Result saved: {result_file} ({len(content)} chars)")
                    return content

        except Exception:
            pass

        time.sleep(30)

    print(f"[nlm] TIMEOUT after {timeout}s")
    return None


def main():
    parser = argparse.ArgumentParser(description="NotebookLM Oracle Dispatch")
    parser.add_argument("--paper", required=True, help="Paper directory path")
    parser.add_argument("--type", default="study_guide",
                        choices=["audio_overview", "chat", "study_guide", "review"],
                        help="Task type")
    parser.add_argument("--prompt", help="Custom prompt (for chat/review)")
    parser.add_argument("--task-id", help="Custom task ID")
    parser.add_argument("--no-wait", action="store_true", help="Submit without waiting")
    parser.add_argument("--timeout", type=int, default=3600, help="Wait timeout in seconds")
    args = parser.parse_args()

    paper_dir = Path(args.paper).resolve()
    if not paper_dir.exists():
        print(f"[nlm] ERROR: Paper directory not found: {paper_dir}")
        sys.exit(1)

    # Check server
    try:
        status = get_json("/status")
        print(f"[nlm] Server OK — queue={status.get('queue_length', 0)}, "
              f"completed={status.get('completed', 0)}")
    except Exception:
        print("[nlm] ERROR: NotebookLM server not running on port 8766")
        print("[nlm] Start it: python notebooklm_server.py")
        sys.exit(1)

    result = submit_task(paper_dir, args.type, args.prompt, args.task_id)
    task_id = result.get("task_id", "unknown")

    if args.no_wait:
        print(f"[nlm] Task {task_id} queued. Check results in notebooklm/done/")
        return

    print(f"[nlm] Waiting for completion (timeout={args.timeout}s)...")
    print(f"[nlm] Make sure NotebookLM is open in Chrome with the Tampermonkey script ACTIVE")
    wait_for_result(task_id, args.timeout)


if __name__ == "__main__":
    main()
