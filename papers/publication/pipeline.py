#!/usr/bin/env python3
"""Four-Gate Publication Pipeline Orchestrator.

Gate 1: ChatGPT Editorial Review (oracle_dispatch.py)
Gate 2: Codex Fix (codex_fix.py) + ChatGPT re-review loop
Gate 3: Claude Final Review (pub-editorial agent)
Gate 4: NotebookLM Output (slides + audio)

Usage:
    python pipeline.py --paper <paper_dir> [--gate 1|2|3|4|all] [--max-rounds 3]
"""

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

PUBLICATION_DIR = Path(__file__).parent
ORACLE_DISPATCH = PUBLICATION_DIR / "oracle_dispatch.py"
CODEX_FIX = PUBLICATION_DIR / "codex_fix.py"
ORACLE_DONE = PUBLICATION_DIR / "oracle" / "done"


def log(gate: int, msg: str):
    ts = time.strftime("%H:%M:%S")
    print(f"[{ts}] [G{gate}] {msg}")


def find_latest_review(paper_dir: Path) -> tuple[Path | None, str]:
    """Find the latest review file and extract its assessment."""
    paper_name = paper_dir.name.replace("2026_", "")
    prefix = "_".join(paper_name.split("_")[:3])

    candidates = []
    for f in ORACLE_DONE.glob(f"*{prefix}*review*.md"):
        size = f.stat().st_size
        if size > 500:
            content = f.read_text(encoding="utf-8", errors="replace")
            if "ERROR:" not in content[:200]:
                candidates.append((f.stat().st_mtime, f, content))

    if not candidates:
        return None, ""

    candidates.sort(reverse=True)
    _, path, content = candidates[0]

    # Extract assessment
    assessment = "UNKNOWN"
    content_lower = content.lower()
    if "accept" in content_lower[:500] and "reject" not in content_lower[:500]:
        assessment = "ACCEPT"
    elif "minor revision" in content_lower[:500]:
        assessment = "MINOR_REVISION"
    elif "major revision" in content_lower[:500]:
        assessment = "MAJOR_REVISION"
    elif "reject" in content_lower[:500]:
        assessment = "REJECT"

    return path, assessment


def gate1_chatgpt_review(paper_dir: Path, name: str) -> tuple[bool, str]:
    """Gate 1: Submit paper for ChatGPT editorial review."""
    log(1, f"Submitting {paper_dir.name} for ChatGPT review...")

    result = subprocess.run(
        [sys.executable, str(ORACLE_DISPATCH),
         "--paper", str(paper_dir),
         "--task", "editorial_review",
         "--name", name,
         "--no-compile",
         "--wait",
         "--timeout", "7200"],
        capture_output=True, text=True, timeout=7500,
        encoding="utf-8", errors="replace",
    )

    review_path, assessment = find_latest_review(paper_dir)
    if review_path and review_path.stat().st_size > 500:
        log(1, f"Review received: {assessment} ({review_path.name}, {review_path.stat().st_size} bytes)")
        return True, assessment
    else:
        log(1, f"Review failed or too short")
        return False, "FAILED"


def gate2_codex_fix(paper_dir: Path, max_rounds: int = 3) -> bool:
    """Gate 2: Codex fix loop — fix paper, resubmit to ChatGPT, repeat."""
    for round_num in range(1, max_rounds + 1):
        log(2, f"=== Round {round_num}/{max_rounds} ===")

        # Find latest review
        review_path, assessment = find_latest_review(paper_dir)
        if not review_path:
            log(2, "No review found — run Gate 1 first")
            return False

        if assessment in ("ACCEPT", "MINOR_REVISION"):
            log(2, f"Paper already at {assessment} — Gate 2 passed!")
            return True

        # Run Codex to apply fixes
        log(2, f"Running Codex to fix issues (assessment: {assessment})...")
        result = subprocess.run(
            [sys.executable, str(CODEX_FIX),
             "--paper", str(paper_dir),
             "--review", str(review_path),
             "--timeout", "3600"],
            capture_output=True, text=True, timeout=3700,
            encoding="utf-8", errors="replace",
        )

        if result.returncode != 0:
            log(2, f"Codex fix failed: {result.stderr[:200]}")
            return False

        log(2, "Codex fixes applied. Recompiling PDF...")

        # Recompile PDF
        compile_result = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
            cwd=str(paper_dir), capture_output=True, timeout=120,
        )
        if not (paper_dir / "main.pdf").exists():
            log(2, "PDF compilation failed after Codex fix")
            return False

        # Resubmit to ChatGPT
        name = f"g2_round{round_num}_{paper_dir.name[:20]}"
        log(2, f"Resubmitting to ChatGPT (round {round_num})...")
        success, new_assessment = gate1_chatgpt_review(paper_dir, name)

        if not success:
            log(2, "ChatGPT re-review failed")
            continue

        if new_assessment in ("ACCEPT", "MINOR_REVISION"):
            log(2, f"Paper reached {new_assessment} after round {round_num}!")
            return True

        log(2, f"Still {new_assessment} after round {round_num}")

    log(2, f"Max rounds ({max_rounds}) exhausted")
    return False


def gate3_claude_review(paper_dir: Path) -> bool:
    """Gate 3: Claude final review (placeholder — runs pub-editorial agent)."""
    log(3, "Claude final review — to be triggered via pub-editorial agent")
    log(3, "This gate runs inside Claude Code as the orchestrator")
    # In practice, this is done by the human invoking Claude Code
    # with the pub-editorial agent on the paper
    return True


def gate4_notebooklm_output(paper_dir: Path) -> bool:
    """Gate 4: NotebookLM output generation (placeholder)."""
    log(4, "NotebookLM output — to be implemented")
    log(4, "Will generate: slides + audio overview")
    # Future: Tampermonkey bridge to NotebookLM
    return True


def main():
    parser = argparse.ArgumentParser(description="Four-Gate Publication Pipeline")
    parser.add_argument("--paper", required=True, help="Paper directory path")
    parser.add_argument("--gate", default="all", help="Which gate to run: 1|2|3|4|all")
    parser.add_argument("--max-rounds", type=int, default=3, help="Max Gate 2 rounds")
    parser.add_argument("--name", default=None, help="Task name for Gate 1")
    args = parser.parse_args()

    paper_dir = Path(args.paper).resolve()
    if not paper_dir.exists():
        print(f"ERROR: {paper_dir} not found")
        sys.exit(1)

    gate = args.gate
    paper_short = paper_dir.name.replace("2026_", "")[:30]
    name = args.name or f"pipeline_{paper_short}"

    print(f"=== Pipeline: {paper_dir.name} ===")
    print(f"Gate: {gate}, Max rounds: {args.max_rounds}")
    print()

    if gate in ("1", "all"):
        success, assessment = gate1_chatgpt_review(paper_dir, name)
        if not success:
            print("PIPELINE STOPPED: Gate 1 failed")
            sys.exit(1)
        print(f"Gate 1 result: {assessment}")
        if gate == "1":
            sys.exit(0)

    if gate in ("2", "all"):
        if not gate2_codex_fix(paper_dir, args.max_rounds):
            print("PIPELINE STOPPED: Gate 2 failed (max rounds exceeded)")
            sys.exit(1)
        print("Gate 2 passed!")
        if gate == "2":
            sys.exit(0)

    if gate in ("3", "all"):
        gate3_claude_review(paper_dir)
        print("Gate 3: Claude review (manual step)")
        if gate == "3":
            sys.exit(0)

    if gate in ("4", "all"):
        gate4_notebooklm_output(paper_dir)
        print("Gate 4: NotebookLM output (to be implemented)")

    print()
    print("=== Pipeline complete ===")


if __name__ == "__main__":
    main()
