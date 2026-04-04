#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ChatGPT Pro oracle — automated clipboard bridge for agent integration.

Supports two modes:
  A) Text-only: prompt copied to clipboard, paste into ChatGPT
  B) PDF+prompt: PDF opened for drag-drop upload, short instruction prompt on clipboard

The script auto-detects when you copy the response — no manual Enter needed.

Usage:
    # Text-only mode:
    python chatgpt_oracle.py --send prompt.md --recv result.md

    # PDF mode (upload PDF + paste instruction):
    python chatgpt_oracle.py --send prompt.md --pdf paper.pdf --recv result.md

    # Watch mode for agents (fully automated queue):
    python chatgpt_oracle.py --watch oracle/
    # Agents write to oracle/pending/:
    #   task_name.md          — instruction prompt (required)
    #   task_name.pdf         — PDF attachment (optional)
    # Results saved to oracle/done/task_name.md

    # Compile LaTeX to PDF before sending:
    python chatgpt_oracle.py --compile paper_dir/ --send prompt.md --recv result.md
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
import webbrowser
from pathlib import Path
from datetime import datetime

CHATGPT_URL = "https://chatgpt.com"
DEFAULT_MODEL = "o3-mini-high"
POLL_INTERVAL = 2        # seconds between clipboard checks
STABILITY_WAIT = 3       # seconds to confirm clipboard is stable
MIN_RESPONSE_LEN = 20    # minimum chars to accept as valid response


# ---------------------------------------------------------------------------
# Clipboard helpers (Windows)
# ---------------------------------------------------------------------------

def copy_to_clipboard(text: str):
    """Copy text to system clipboard."""
    proc = subprocess.Popen(["clip"], stdin=subprocess.PIPE)
    proc.communicate(text.encode("utf-16-le"))


def read_from_clipboard() -> str:
    """Read text from system clipboard."""
    result = subprocess.run(
        ["powershell", "-Command", "Get-Clipboard"],
        capture_output=True, text=True, encoding="utf-8"
    )
    return result.stdout.strip()


# ---------------------------------------------------------------------------
# Browser / file helpers
# ---------------------------------------------------------------------------

def open_chatgpt():
    """Open ChatGPT in default browser."""
    webbrowser.open(CHATGPT_URL)


def open_file_location(file_path: Path):
    """Open file explorer with the file selected (Windows)."""
    subprocess.Popen(["explorer", "/select,", str(file_path.resolve())])


# ---------------------------------------------------------------------------
# LaTeX compilation
# ---------------------------------------------------------------------------

def compile_latex(paper_dir: Path) -> Path:
    """Compile main.tex in paper_dir to PDF using pdflatex.

    Returns path to the compiled PDF.
    """
    main_tex = paper_dir / "main.tex"
    if not main_tex.exists():
        print(f"[oracle] ERROR: {main_tex} not found", file=sys.stderr)
        sys.exit(1)

    print(f"[oracle] Compiling {main_tex}...")
    for i in range(2):  # two passes for references
        result = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
            cwd=str(paper_dir), capture_output=True, text=True, timeout=120
        )
        if result.returncode != 0 and i == 1:
            print(f"[oracle] LaTeX compilation failed:\n{result.stdout[-500:]}", file=sys.stderr)
            sys.exit(1)

    # Run bibtex if .bib exists
    if (paper_dir / "references.bib").exists():
        subprocess.run(
            ["bibtex", "main"], cwd=str(paper_dir),
            capture_output=True, text=True, timeout=60
        )
        # Two more passes after bibtex
        for _ in range(2):
            subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
                cwd=str(paper_dir), capture_output=True, text=True, timeout=120
            )

    pdf_path = paper_dir / "main.pdf"
    if not pdf_path.exists():
        print(f"[oracle] ERROR: PDF not generated at {pdf_path}", file=sys.stderr)
        sys.exit(1)

    print(f"[oracle] PDF compiled: {pdf_path} ({pdf_path.stat().st_size // 1024} KB)")
    return pdf_path


# ---------------------------------------------------------------------------
# Content matching
# ---------------------------------------------------------------------------

def _is_same_content(a: str, b: str) -> bool:
    """Fuzzy match: ignore whitespace differences."""
    return a.strip().replace("\r\n", "\n") == b.strip().replace("\r\n", "\n")


# ---------------------------------------------------------------------------
# Clipboard change detection
# ---------------------------------------------------------------------------

def wait_for_clipboard_change(original: str, timeout: int = 600) -> str:
    """Poll clipboard until content changes from original.

    Returns the new clipboard content, or empty string on timeout.
    Uses a stability check to ensure the full response has been copied.
    """
    start = time.time()
    elapsed_msg_interval = 30
    last_msg = start

    while time.time() - start < timeout:
        current = read_from_clipboard()

        if (not _is_same_content(current, original)
                and len(current) >= MIN_RESPONSE_LEN):
            print(f"[oracle] Clipboard change detected ({len(current)} chars), verifying...")
            time.sleep(STABILITY_WAIT)
            stable = read_from_clipboard()
            if _is_same_content(stable, current):
                return stable
            print(f"[oracle] Content still changing, waiting...")

        now = time.time()
        if now - last_msg >= elapsed_msg_interval:
            elapsed = int(now - start)
            print(f"[oracle] Waiting for response... ({elapsed}s elapsed)")
            last_msg = now

        time.sleep(POLL_INTERVAL)

    print(f"[oracle] Timeout after {timeout}s", file=sys.stderr)
    return ""


# ---------------------------------------------------------------------------
# Response persistence
# ---------------------------------------------------------------------------

def save_response(output_path: Path, response: str, model: str,
                  prompt_len: int = 0, source: str = "", pdf: str = ""):
    """Save response with metadata to file."""
    output_path.parent.mkdir(parents=True, exist_ok=True)
    metadata = {
        "timestamp": datetime.now().isoformat(),
        "model": model,
        "prompt_length": prompt_len,
        "response_length": len(response),
    }
    if source:
        metadata["source"] = source
    if pdf:
        metadata["pdf"] = pdf
    output_path.write_text(
        f"<!-- oracle metadata: {json.dumps(metadata)} -->\n\n{response}",
        encoding="utf-8",
    )
    print(f"[oracle] Response saved to {output_path} ({len(response)} chars)")


# ---------------------------------------------------------------------------
# Send prompt (with optional PDF)
# ---------------------------------------------------------------------------

def send_prompt(prompt_path: Path, pdf_path: Path | None = None) -> str:
    """Copy prompt to clipboard, open ChatGPT, optionally show PDF for upload."""
    prompt = prompt_path.read_text(encoding="utf-8")
    copy_to_clipboard(prompt)
    open_chatgpt()

    print(f"[oracle] Prompt copied to clipboard ({len(prompt)} chars)")

    if pdf_path and pdf_path.exists():
        open_file_location(pdf_path)
        print(f"[oracle] PDF: {pdf_path.name} ({pdf_path.stat().st_size // 1024} KB)")
        print(f"[oracle] Steps:")
        print(f"  1. Drag-drop the PDF into the ChatGPT input box")
        print(f"  2. Paste the instruction prompt (Ctrl+V)")
        print(f"  3. Send, wait for response, copy the response (Ctrl+C)")
    else:
        print(f"[oracle] Paste with Ctrl+V, wait for response, copy the response.")

    return prompt


# ---------------------------------------------------------------------------
# Full auto: send + wait + save
# ---------------------------------------------------------------------------

def send_and_recv(prompt_path: Path, output_path: Path, model: str,
                  timeout: int, pdf_path: Path | None = None):
    """Full auto: send prompt (+ PDF), wait for clipboard change, save response."""
    prompt = send_prompt(prompt_path, pdf_path)
    print(f"[oracle] Auto-detecting response (polling every {POLL_INTERVAL}s)...")
    print(f"[oracle] Just copy the ChatGPT response when ready.\n")

    response = wait_for_clipboard_change(prompt, timeout=timeout)
    if response:
        save_response(output_path, response, model, len(prompt),
                      pdf=str(pdf_path) if pdf_path else "")
    else:
        print("[oracle] ERROR: No response detected.", file=sys.stderr)
        sys.exit(1)


# ---------------------------------------------------------------------------
# Watch mode (agent queue)
# ---------------------------------------------------------------------------

def watch_mode(watch_dir: str, model: str, timeout: int):
    """Watch for pending prompts with auto clipboard detection.

    Agent writes to pending/:
      task_name.md   — instruction prompt (required)
      task_name.pdf  — PDF attachment (optional, e.g. compiled paper)
    Results auto-saved to done/task_name.md when clipboard changes.
    """
    watch = Path(watch_dir)
    pending = watch / "pending"
    done = watch / "done"
    pending.mkdir(parents=True, exist_ok=True)
    done.mkdir(parents=True, exist_ok=True)

    print(f"[oracle] Watch mode active (auto-detect)")
    print(f"[oracle] Agents write prompts to: {pending}/")
    print(f"[oracle]   .md = instruction prompt (required)")
    print(f"[oracle]   .pdf = paper attachment (optional)")
    print(f"[oracle] Results saved to: {done}/")
    print(f"[oracle] Press Ctrl+C to stop.\n")

    try:
        while True:
            for prompt_file in sorted(pending.glob("*.md")):
                name = prompt_file.stem
                out_file = done / f"{name}.md"

                if out_file.exists():
                    prompt_file.unlink()
                    continue

                prompt = prompt_file.read_text(encoding="utf-8")
                prompt_len = len(prompt)

                # Check for companion PDF
                pdf_file = pending / f"{name}.pdf"
                has_pdf = pdf_file.exists()

                print(f"\n{'='*60}")
                print(f"  NEW PROMPT: {prompt_file.name} ({prompt_len} chars)")
                if has_pdf:
                    print(f"  ATTACHMENT: {pdf_file.name} ({pdf_file.stat().st_size // 1024} KB)")
                print(f"{'='*60}")

                # Copy prompt to clipboard and open ChatGPT
                copy_to_clipboard(prompt)
                open_chatgpt()

                if has_pdf:
                    open_file_location(pdf_file)
                    print(f"  1. Drag-drop {pdf_file.name} into ChatGPT")
                    print(f"  2. Paste instruction (Ctrl+V)")
                    print(f"  3. Send, wait for response, copy it (Ctrl+C)")
                else:
                    print(f"  1. Paste into ChatGPT (Ctrl+V)")
                    print(f"  2. Wait for response, copy it (Ctrl+C)")
                print(f"  >> Auto-detecting clipboard change...\n")

                response = wait_for_clipboard_change(prompt, timeout=timeout)
                if response:
                    save_response(out_file, response, model, prompt_len,
                                  source=str(prompt_file),
                                  pdf=str(pdf_file) if has_pdf else "")
                else:
                    out_file.write_text(
                        "<!-- oracle: ERROR - timeout waiting for response -->\n",
                        encoding="utf-8",
                    )
                    print(f"  WARNING: Timeout, saved error marker.")

                # Cleanup pending files
                prompt_file.unlink()
                if has_pdf:
                    pdf_file.unlink()

            time.sleep(2)

    except KeyboardInterrupt:
        print("\n[oracle] Stopped.")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="ChatGPT Pro oracle (auto clipboard + PDF upload)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Text-only:
  python chatgpt_oracle.py --send prompt.md --recv result.md

  # PDF + instruction:
  python chatgpt_oracle.py --send prompt.md --pdf paper.pdf --recv result.md

  # Compile + send:
  python chatgpt_oracle.py --compile paper_dir/ --send prompt.md --recv result.md

  # Agent queue:
  python chatgpt_oracle.py --watch oracle/
""",
    )
    parser.add_argument("--send", type=Path,
                        help="Instruction prompt file (copied to clipboard)")
    parser.add_argument("--recv", type=Path,
                        help="Output file for the response")
    parser.add_argument("--pdf", type=Path,
                        help="PDF file to upload (opens file explorer for drag-drop)")
    parser.add_argument("--compile", type=Path,
                        help="Compile main.tex in this directory to PDF before sending")
    parser.add_argument("--watch", type=str,
                        help="Watch mode: monitor dir/pending/ for prompts")
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL,
                        help=f"Model tag for metadata (default: {DEFAULT_MODEL})")
    parser.add_argument("--timeout", type=int, default=600,
                        help="Max seconds to wait for response (default: 600)")
    args = parser.parse_args()

    # Compile PDF if requested
    pdf_path = args.pdf
    if args.compile:
        pdf_path = compile_latex(args.compile)

    if args.watch:
        watch_mode(args.watch, args.model, args.timeout)
        return

    if args.send and args.recv:
        send_and_recv(args.send, args.recv, args.model, args.timeout, pdf_path)
        return

    if args.send:
        if not args.send.exists():
            print(f"Error: {args.send} not found", file=sys.stderr)
            sys.exit(1)
        send_prompt(args.send, pdf_path)
        return

    if args.recv:
        response = read_from_clipboard()
        if not response:
            print("[oracle] ERROR: Clipboard is empty.", file=sys.stderr)
            sys.exit(1)
        save_response(args.recv, response, args.model)
        return

    parser.print_help()


if __name__ == "__main__":
    main()
