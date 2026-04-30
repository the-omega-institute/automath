#!/usr/bin/env python3
"""ChatGPT Oracle — submit a question and get a response.

Minimal CLI: zero pip dependencies, just Python 3.8+.

Usage:
    # Simple question
    python oracle_ask.py "What is the Cauchy distribution?"

    # Question with PDF attachment
    python oracle_ask.py "Review this paper" --pdf paper.pdf

    # Custom task name + longer timeout
    python oracle_ask.py "Verify proofs" --pdf paper.pdf --name my_review --timeout 600

    # Read prompt from file
    python oracle_ask.py --file prompt.txt --pdf paper.pdf
"""

from __future__ import annotations

import argparse
import base64
import io
import json
import sys
import time
import urllib.request
from datetime import datetime
from pathlib import Path

SERVER = "http://127.0.0.1:8765"


def submit(prompt: str, pdf_path: Path | None = None, name: str | None = None,
           timeout: int = 1800) -> str:
    """Submit task, wait for response, return text."""
    task_id = name or f"ask_{int(time.time())}"

    payload: dict = {"task_id": task_id, "prompt": prompt}
    if pdf_path and pdf_path.exists():
        payload["pdf_base64"] = base64.b64encode(pdf_path.read_bytes()).decode("ascii")
        payload["pdf_name"] = pdf_path.name
        print(f"[oracle] PDF: {pdf_path.name} ({pdf_path.stat().st_size // 1024} KB)")

    # Submit
    print(f"[oracle] Submitting '{task_id}'...")
    req = urllib.request.Request(
        f"{SERVER}/submit",
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    try:
        urllib.request.urlopen(req, timeout=15)
    except Exception as e:
        print(f"[oracle] ERROR: server unreachable at {SERVER}", file=sys.stderr)
        print(f"[oracle] Start it: python oracle_server.py", file=sys.stderr)
        sys.exit(1)

    # Poll
    print(f"[oracle] Waiting (up to {timeout}s)...")
    start = time.time()
    while time.time() - start < timeout:
        try:
            resp = urllib.request.urlopen(f"{SERVER}/result/{task_id}", timeout=5)
            data = json.loads(resp.read().decode("utf-8"))
            if data.get("status") == "completed":
                response = data["response"]
                print(f"[oracle] Done: {len(response)} chars")
                return response
        except Exception:
            pass
        elapsed = int(time.time() - start)
        if elapsed > 0 and elapsed % 30 == 0:
            print(f"[oracle] Waiting... ({elapsed}s)")
        time.sleep(3)

    print(f"[oracle] Timeout after {timeout}s", file=sys.stderr)
    return ""


def main():
    parser = argparse.ArgumentParser(description="Ask ChatGPT via oracle bridge")
    parser.add_argument("prompt", nargs="?", help="Question or instruction")
    parser.add_argument("--file", "-f", type=Path, help="Read prompt from file")
    parser.add_argument("--pdf", type=Path, help="Attach a PDF file")
    parser.add_argument("--name", "-n", type=str, help="Task name (default: auto)")
    parser.add_argument("--timeout", "-t", type=int, default=1800, help="Timeout seconds (default: 1800)")
    args = parser.parse_args()

    if args.file:
        prompt = args.file.read_text(encoding="utf-8")
    elif args.prompt:
        prompt = args.prompt
    else:
        print("Error: provide a prompt or --file", file=sys.stderr)
        sys.exit(1)

    response = submit(prompt, args.pdf, args.name, args.timeout)
    if response:
        # Safe print for Windows
        out = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")
        out.write(f"\n{'='*60}\n{response}\n")
        out.flush()
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
