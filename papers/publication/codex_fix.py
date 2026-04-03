#!/usr/bin/env python3
"""Gate 2: Use OpenAI Codex to fix a paper based on ChatGPT review feedback.

Usage:
    python codex_fix.py --paper <paper_dir> --review <review_file>
    python codex_fix.py --paper <paper_dir> --review-text "inline review"

Codex reads the paper source files, applies fixes based on reviewer feedback,
and writes changes directly to the paper directory.
"""

import argparse
import json
import subprocess
import sys
import os
from pathlib import Path

PUBLICATION_DIR = Path(__file__).parent


def build_prompt(review_text: str, paper_dir: Path) -> str:
    """Build the prompt for Codex to fix the paper."""
    # List .tex files in the paper directory
    tex_files = sorted(paper_dir.glob("**/*.tex"))
    tex_list = "\n".join(f"  - {f.relative_to(paper_dir)}" for f in tex_files)

    return f"""You are a mathematics paper editor fixing a manuscript based on reviewer feedback.

PAPER DIRECTORY: {paper_dir.name}
TEX FILES:
{tex_list}

REVIEWER FEEDBACK:
{review_text}

INSTRUCTIONS:
1. Read all .tex source files in this directory.
2. Apply every concrete fix the reviewer identified — especially BLOCKERs and MEDIUM issues.
3. For each issue:
   - If the reviewer gave an explicit fix (corrected proof, formula, statement), apply it directly.
   - If the reviewer identified a gap, add the missing argument or citation.
   - If the reviewer said "define X", add the definition.
4. Do NOT add revision markers, changelogs, or comments like "fixed issue I3".
5. Do NOT change the file structure or create new files unless absolutely necessary.
6. Preserve all existing mathematical content that the reviewer did not flag.
7. Write clean, publication-ready LaTeX.
8. After fixing, briefly list what you changed (for verification).

CONSTRAINTS:
- Only edit .tex and .bib files.
- Do not delete theorems or sections unless the reviewer explicitly said to remove them.
- Keep the paper's voice and style consistent.
"""


def run_codex(prompt: str, paper_dir: Path, model: str = None, timeout: int = 3600) -> dict:
    """Run Codex exec on the paper directory."""
    cmd = ["codex", "exec", "--json"]

    if model:
        cmd += ["-c", f'model="{model}"']

    # Full auto mode — let Codex read/write files without asking
    cmd += ["--full-auto"]
    cmd += [prompt]

    print(f"[codex] Running Codex on {paper_dir.name}...")
    print(f"[codex] Model: {model or 'default'}")
    print(f"[codex] Timeout: {timeout}s")

    try:
        result = subprocess.run(
            cmd,
            cwd=str(paper_dir),
            capture_output=True,
            text=True,
            timeout=timeout,
            encoding="utf-8",
            errors="replace",
        )

        # Parse JSON output (newline-delimited JSON)
        output_lines = []
        for line in result.stdout.strip().split("\n"):
            line = line.strip()
            if line:
                try:
                    output_lines.append(json.loads(line))
                except json.JSONDecodeError:
                    output_lines.append({"raw": line})

        return {
            "returncode": result.returncode,
            "output": output_lines,
            "stderr": result.stderr,
            "success": result.returncode == 0,
        }

    except subprocess.TimeoutExpired:
        return {"returncode": -1, "output": [], "stderr": "Timeout", "success": False}
    except Exception as e:
        return {"returncode": -1, "output": [], "stderr": str(e), "success": False}


def find_latest_review(paper_dir: Path) -> Path | None:
    """Find the latest review file for a paper in oracle/done/."""
    done_dir = PUBLICATION_DIR / "oracle" / "done"
    paper_name = paper_dir.name.replace("2026_", "")
    prefix = "_".join(paper_name.split("_")[:3])

    candidates = []
    for f in done_dir.glob(f"*{prefix}*review*.md"):
        size = f.stat().st_size
        if size > 500:
            content = f.read_text(encoding="utf-8", errors="replace")
            if "ERROR:" not in content[:200]:
                candidates.append((f.stat().st_mtime, f))

    if candidates:
        candidates.sort(reverse=True)
        return candidates[0][1]
    return None


def main():
    parser = argparse.ArgumentParser(description="Gate 2: Codex paper fix")
    parser.add_argument("--paper", required=True, help="Paper directory path")
    parser.add_argument("--review", help="Review file path (auto-detect if omitted)")
    parser.add_argument("--review-text", help="Inline review text")
    parser.add_argument("--model", default=None, help="Codex model (default: auto)")
    parser.add_argument("--timeout", type=int, default=3600, help="Timeout in seconds")
    parser.add_argument("--dry-run", action="store_true", help="Print prompt without running")
    args = parser.parse_args()

    paper_dir = Path(args.paper).resolve()
    if not paper_dir.exists():
        print(f"[codex] ERROR: Paper directory not found: {paper_dir}")
        sys.exit(1)

    # Get review text
    if args.review_text:
        review_text = args.review_text
    elif args.review:
        review_path = Path(args.review)
        if not review_path.exists():
            print(f"[codex] ERROR: Review file not found: {review_path}")
            sys.exit(1)
        review_text = review_path.read_text(encoding="utf-8", errors="replace")
    else:
        # Auto-detect latest review
        review_path = find_latest_review(paper_dir)
        if not review_path:
            print(f"[codex] ERROR: No review found for {paper_dir.name}")
            print(f"[codex] Run Gate 1 first (oracle_dispatch.py)")
            sys.exit(1)
        print(f"[codex] Auto-detected review: {review_path.name}")
        review_text = review_path.read_text(encoding="utf-8", errors="replace")

    # Strip metadata comment from review
    if review_text.startswith("<!--"):
        review_text = review_text.split("-->", 1)[-1].strip()

    prompt = build_prompt(review_text, paper_dir)

    if args.dry_run:
        print("=== PROMPT ===")
        print(prompt[:2000])
        print(f"... ({len(prompt)} chars total)")
        return

    result = run_codex(prompt, paper_dir, model=args.model, timeout=args.timeout)

    if result["success"]:
        print(f"[codex] SUCCESS")
        # Show what files were changed
        for item in result["output"]:
            if isinstance(item, dict):
                if "fileChanges" in item:
                    for fc in item["fileChanges"]:
                        print(f"  Changed: {fc}")
                if "finalMessage" in item:
                    print(f"  Summary: {item['finalMessage'][:500]}")
    else:
        print(f"[codex] FAILED (exit {result['returncode']})")
        if result["stderr"]:
            print(f"  {result['stderr'][:500]}")

    return result


if __name__ == "__main__":
    main()
