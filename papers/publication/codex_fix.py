#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Gate 2: Use OpenAI Codex to fix a paper based on ChatGPT review feedback.

Usage:
    python codex_fix.py --paper <paper_dir> --review <review_file>
    python codex_fix.py --paper <paper_dir> --review-text "inline review"

Codex reads the paper source files, applies fixes based on reviewer feedback,
and writes changes directly to the paper directory.
"""

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

# Ensure UTF-8 stdout on Windows (avoids cp1252 errors with non-ASCII paths)
if sys.platform == "win32" and not os.environ.get("PYTHONIOENCODING"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

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
- ONLY edit .tex and .bib files INSIDE this directory ({paper_dir.name}/).
- Do NOT navigate to parent directories or modify any files outside this directory.
- Do not delete theorems or sections unless the reviewer explicitly said to remove them.
- Keep the paper's voice and style consistent.
"""


def find_codex_binary() -> str:
    """Find the codex CLI binary, handling Windows .cmd wrapper."""
    import shutil
    codex = shutil.which("codex")
    if codex:
        return codex
    # Windows: try explicit .cmd path
    if sys.platform == "win32":
        npm_path = Path.home() / "AppData" / "Roaming" / "npm" / "codex.cmd"
        if npm_path.exists():
            return str(npm_path)
    return "codex"  # fallback, let subprocess find it


def run_codex(prompt: str, paper_dir: Path, model: str = None, timeout: int = 3600) -> dict:
    """Run Codex exec on the paper directory."""
    codex_bin = find_codex_binary()
    cmd = [codex_bin, "exec", "--json"]

    if model:
        cmd += ["-c", f'model="{model}"']
        # gpt-5-codex does not support reasoning effort 'xhigh'; cap at 'high'
        if "codex" in model.lower():
            cmd += ["-c", 'model_reasoning_effort="high"']

    # Full auto mode — let Codex read/write files without asking
    cmd += ["--full-auto"]
    # Pass prompt via stdin (avoid Windows command-line length limit)
    cmd += ["-"]

    print(f"[codex] Running Codex on {paper_dir.name}...")
    print(f"[codex] Prompt: {len(prompt)} chars (via stdin)")
    print(f"[codex] Model: {model or 'default'}")
    print(f"[codex] Timeout: {timeout}s")

    try:
        # On Windows, .cmd wrappers need shell=True
        use_shell = sys.platform == "win32" and codex_bin.lower().endswith(".cmd")
        result = subprocess.run(
            cmd,
            cwd=str(paper_dir),
            input=prompt,
            capture_output=True,
            text=True,
            timeout=timeout,
            encoding="utf-8",
            errors="replace",
            shell=use_shell,
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
    """Find the latest review file for a paper in oracle/done/.

    Searches for both legacy *review*.md files and gate_R*.md files,
    preferring the largest real review (>5000 bytes).
    """
    import re as _re
    done_dir = PUBLICATION_DIR / "oracle" / "done"
    paper_name = paper_dir.name.replace("2026_", "")
    prefix = "_".join(paper_name.split("_")[:3])

    # Also resolve known aliases for gate review naming
    aliases = {
        "circle_dimension_haar": "circle_dim",
        "conservative_extension_chain": "conservative_ext",
        "cubical_stokes_inverse": "cubical_stokes",
        "dynamical_zeta_finite": "dynamical_zeta",
        "fibonacci_folding_zeckendorf": "fibonacci_folding",
        "fold_truncation_defect": "fold_truncation",
        "fredholm_witt_cyclic": "fredholm_witt",
        "gluing_failure_visible": "gluing_failure",
        "JphisComm_待投稿": "JphisComm",
        "JphisComm": "JphisComm",
        "prefix_scan_error": "prefix_scan",
        "prime_languages_sofic": "prime_languages",
        "projection_ontological_mathematics": "projection_ontological",
        "recursive_addressing_prefix": "recursive_addressing",
        "scan_projection_address": "scan_projection",
        "self_dual_synchronisation": "self_dual_sync",
        "yang_lee_quartic": "yang_lee",
    }
    gate_prefix = aliases.get(prefix, prefix)

    candidates = []
    # Search legacy review files
    for f in done_dir.glob(f"*{prefix}*review*.md"):
        size = f.stat().st_size
        if size > 500:
            content = f.read_text(encoding="utf-8", errors="replace")
            if "ERROR:" not in content[:200]:
                candidates.append((size, f.stat().st_mtime, f))

    # Search gate review files (gate_R*.md)
    for f in done_dir.glob(f"{gate_prefix}_gate_R*.md"):
        size = f.stat().st_size
        if size > 5000:  # only real reviews, skip stubs
            candidates.append((size, f.stat().st_mtime, f))

    if candidates:
        # Prefer largest real review, break ties by recency
        candidates.sort(key=lambda x: (x[0] > 5000, x[1]), reverse=True)
        return candidates[0][2]
    return None


def main():
    parser = argparse.ArgumentParser(description="Gate 2: Codex paper fix")
    parser.add_argument("--paper", required=True, help="Paper directory path")
    parser.add_argument("--review", help="Review file path (auto-detect if omitted)")
    parser.add_argument("--review-text", help="Inline review text")
    parser.add_argument("--model", default=None, help="Codex model (default: from config, options: gpt-5.3-codex-spark, etc.)")
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
        # Dump last few stdout items for diagnosis
        for item in result["output"][-5:]:
            if isinstance(item, dict):
                for key in ("raw", "finalMessage", "error", "message"):
                    if key in item:
                        print(f"  [{key}] {str(item[key])[:300]}")

    return result


if __name__ == "__main__":
    result = main()
    if result and not result.get("success", False):
        sys.exit(1)
