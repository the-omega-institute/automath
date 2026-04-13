#!/usr/bin/env python3
"""NotebookLM Dispatch — upload PDF and generate content via notebooklm-py.

Uses the notebooklm-py RPC API (no browser automation needed).
Requires: pip install notebooklm-py && notebooklm login

Usage:
    python notebooklm_dispatch.py --paper <dir> --type study_guide
    python notebooklm_dispatch.py --paper <dir> --type audio
    python notebooklm_dispatch.py --paper <dir> --type chat --prompt "Summarize key results"
    python notebooklm_dispatch.py --paper <dir> --type slide_deck
    python notebooklm_dispatch.py --list
"""

import argparse
import json
import os
import re
import subprocess
import sys
from datetime import datetime
from pathlib import Path

PUBLICATION_DIR = Path(__file__).resolve().parent.parent.parent / "papers" / "publication"
DONE_DIR = PUBLICATION_DIR / "notebooklm" / "done"
DONE_DIR.mkdir(parents=True, exist_ok=True)


def find_pdf(paper_dir: Path) -> Path | None:
    for c in paper_dir.glob("*.pdf"):
        if c.stem == "main":
            return c
    candidates = list(paper_dir.glob("**/*.pdf"))
    if candidates:
        candidates.sort(key=lambda f: f.stat().st_size, reverse=True)
        return candidates[0]
    return None


def paper_slug(paper_dir: Path) -> str:
    name = paper_dir.name.replace("2026_", "")
    return "_".join(name.split("_")[:3])


def run_nlm(*args, timeout=120) -> str:
    env = os.environ.copy()
    env["PYTHONIOENCODING"] = "utf-8"
    result = subprocess.run(
        ["notebooklm"] + list(args),
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        timeout=timeout, env=env,
    )
    stdout = result.stdout.decode("utf-8", errors="replace").strip()
    stderr = result.stderr.decode("utf-8", errors="replace").strip()
    if result.returncode != 0 and stderr:
        if "UnicodeEncodeError" not in stderr:
            print(f"[nlm] WARN: {stderr[:300]}")
    return stdout


def save_result(task_id: str, content: str, task_type: str):
    safe_id = "".join(c if c.isalnum() or c in "_-" else "_" for c in task_id)
    out = DONE_DIR / f"{safe_id}.md"
    meta = {
        "timestamp": datetime.now().isoformat(),
        "task_id": task_id,
        "task_type": task_type,
        "response_length": len(content),
    }
    out.write_text(
        f"<!-- notebooklm metadata: {json.dumps(meta)} -->\n\n{content}",
        encoding="utf-8",
    )
    print(f"[nlm] Saved: {out} ({len(content)} chars)")


def main():
    parser = argparse.ArgumentParser(description="NotebookLM Dispatch (via notebooklm-py)")
    parser.add_argument("--paper", help="Paper directory path")
    parser.add_argument("--type", default="study_guide",
                        choices=["study_guide", "audio", "chat", "slide_deck", "quiz", "summary"],
                        help="Task type")
    parser.add_argument("--prompt", help="Custom prompt (for chat)")
    parser.add_argument("--notebook", help="Reuse existing notebook ID (prefix ok)")
    parser.add_argument("--list", action="store_true", help="List notebooks")
    parser.add_argument("--keep", action="store_true", help="Keep notebook after")
    args = parser.parse_args()

    if args.list:
        print(run_nlm("list"))
        return

    if not args.paper:
        parser.print_help()
        sys.exit(1)

    paper_dir = Path(args.paper).resolve()
    if not paper_dir.exists():
        print(f"[nlm] ERROR: {paper_dir} not found")
        sys.exit(1)

    pdf_path = find_pdf(paper_dir)
    if not pdf_path:
        print(f"[nlm] ERROR: No PDF in {paper_dir}")
        sys.exit(1)

    slug = paper_slug(paper_dir)
    task_id = f"nlm_{slug}_{args.type}"
    print(f"[nlm] Paper: {paper_dir.name}")
    print(f"[nlm] PDF: {pdf_path.name} ({pdf_path.stat().st_size / 1024:.0f} KB)")

    # Step 1: Create or reuse notebook
    nb_id = args.notebook
    if not nb_id:
        title = paper_dir.name.replace("2026_", "").replace("_", " ").title()[:60]
        print(f"[nlm] Creating notebook: {title}")
        out = run_nlm("create", title)
        m = re.search(r"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})", out)
        if not m:
            print(f"[nlm] ERROR creating notebook: {out}")
            sys.exit(1)
        nb_id = m.group(1)
    print(f"[nlm] Notebook: {nb_id[:12]}...")

    # Step 2: Set active notebook
    run_nlm("use", nb_id[:8])

    # Step 3: Upload PDF
    print(f"[nlm] Uploading PDF...")
    out = run_nlm("source", "add", str(pdf_path), timeout=120)
    if "Added source" not in out:
        print(f"[nlm] ERROR uploading: {out}")
        sys.exit(1)
    print(f"[nlm] {out}")

    # Step 4: Execute task
    print(f"[nlm] Running: {args.type}")
    content = ""

    if args.type == "study_guide":
        content = run_nlm("source", "guide", timeout=300)
        if not content or len(content) < 50:
            content = run_nlm("ask",
                "Provide a comprehensive study guide: (1) Key definitions, "
                "(2) Main theorems, (3) Proof strategies, (4) Open questions, "
                "(5) Prerequisites.", timeout=300)

    elif args.type == "audio":
        print("[nlm] Generating audio (may take minutes)...")
        content = run_nlm("generate", "audio", timeout=600)
        dl_path = DONE_DIR / f"{task_id}.wav"
        dl = run_nlm("download", "audio", str(dl_path), timeout=120)
        if dl_path.exists():
            print(f"[nlm] Audio: {dl_path} ({dl_path.stat().st_size / 1024:.0f} KB)")

    elif args.type == "chat":
        prompt = args.prompt or "Summarize the main contributions of this paper."
        content = run_nlm("ask", prompt, timeout=300)

    elif args.type == "slide_deck":
        content = run_nlm("generate", "slide-deck", timeout=300)

    elif args.type == "quiz":
        content = run_nlm("generate", "quiz", timeout=300)

    elif args.type == "summary":
        content = run_nlm("summary", timeout=300)

    if content:
        save_result(task_id, content, args.type)

    print(f"[nlm] Done: {task_id}")
    if not args.keep and not args.notebook:
        print(f"[nlm] Tip: --keep to preserve, --notebook {nb_id[:8]} to reuse")


if __name__ == "__main__":
    main()
