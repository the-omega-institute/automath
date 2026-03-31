#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Oracle dispatch — agent-side interface for ChatGPT Pro oracle.

This script is called by agents to submit work to the ChatGPT oracle
and wait for results. The human operator runs chatgpt_oracle.py --watch
in a separate terminal.

Usage:
    # Submit a paper for editorial review:
    python oracle_dispatch.py --paper paper_dir/ --task editorial_review --wait

    # Submit with custom prompt:
    python oracle_dispatch.py --paper paper_dir/ --prompt custom.md --wait

    # Submit text-only (no PDF):
    python oracle_dispatch.py --prompt-text "Prove that ..." --task reasoning --wait

    # Just dispatch (don't wait):
    python oracle_dispatch.py --paper paper_dir/ --task editorial_review

Workflow:
    1. Compiles paper to PDF (if --paper given)
    2. Generates instruction prompt from template (if --task given)
    3. Writes .md + .pdf to oracle/pending/
    4. If --wait: polls oracle/done/ until result appears
    5. Returns result path (or prints to stdout)
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import time
from pathlib import Path
from datetime import datetime

ORACLE_DIR = Path(__file__).parent / "oracle"
PROMPTS_DIR = Path(__file__).parent / "prompts"

# Task templates: short instructions for ChatGPT (the PDF provides context)
TASK_TEMPLATES = {
    "editorial_review": """Please review the attached paper as a journal editor/referee.

Provide:
1. **Overall assessment**: Accept / Major revision / Minor revision / Reject
2. **Novelty rating** for each theorem: HIGH / MEDIUM / LOW with one-line justification
3. **Issue table**: ID | Section | Severity (BLOCKER/MEDIUM/LOW) | Description | Suggested fix
4. **Missing references**: List any important related work not cited
5. **Specific improvements** needed to reach acceptance

Be rigorous. Identify every mathematical gap, unclear argument, and expository weakness.
Use academic language. Do not summarize what the paper already says — focus on what needs to change.""",

    "deep_research": """Please read the attached paper and conduct deep research to strengthen it.

Requirements:
- Find genuinely novel, publishable results that extend the paper's framework
- Do NOT repeat known results or standard proofs — cite them if needed
- Do NOT provide intermediate or trivial conclusions
- Each new result must be stated as a formal theorem/proposition with proof
- Use rigorous academic language throughout

Deliverables:
1. **New theorems** (2-4) that would strengthen the paper, with complete proofs
2. **Gap analysis**: mathematical gaps in the current version with fixes
3. **Scope recommendations**: what to keep, cut, or defer to a sequel
4. **Key insight**: what is the one deep observation that makes this paper important?""",

    "literature_search": """Please read the attached paper and identify all relevant competing/related work.

For each related paper, provide:
- Full citation (authors, title, journal, year)
- How our paper differs from or extends their work
- Whether any of our results overlap with theirs

Also identify any results we use without citation.
Focus on the last 10 years but include foundational references.""",

    "proof_verification": """Please carefully verify every proof in the attached paper.

For each theorem/proposition/lemma:
1. State whether the proof is COMPLETE, has GAPS, or is INCORRECT
2. If gaps exist, describe exactly what is missing
3. Suggest how to fix any issues
4. Rate the difficulty: ROUTINE / MODERATE / DEEP

Flag any implicit assumptions that should be stated explicitly.""",

    "journal_fit": """Please assess the attached paper's fit for its target journal.

Evaluate:
1. **Scope match**: Does the content match the journal's typical publications?
2. **Technical level**: Is it at the right level for the journal's readership?
3. **Length**: Is it appropriate? Too long? Too short?
4. **Presentation quality**: Abstract, introduction, exposition
5. **Impact**: Would this paper be cited? By whom?
6. **Recommendation**: Submit as-is / Revise / Try different journal (suggest which)""",
}


def compile_paper(paper_dir: Path) -> Path | None:
    """Compile main.tex to PDF. Returns PDF path or None on failure."""
    main_tex = paper_dir / "main.tex"
    if not main_tex.exists():
        print(f"[dispatch] No main.tex in {paper_dir}", file=sys.stderr)
        return None

    print(f"[dispatch] Compiling {main_tex}...")
    for i in range(2):
        result = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
            cwd=str(paper_dir), capture_output=True, text=True, timeout=120
        )

    if (paper_dir / "references.bib").exists():
        subprocess.run(
            ["bibtex", "main"], cwd=str(paper_dir),
            capture_output=True, text=True, timeout=60
        )
        for _ in range(2):
            subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
                cwd=str(paper_dir), capture_output=True, text=True, timeout=120
            )

    pdf_path = paper_dir / "main.pdf"
    if pdf_path.exists():
        print(f"[dispatch] PDF ready: {pdf_path} ({pdf_path.stat().st_size // 1024} KB)")
        return pdf_path
    else:
        print(f"[dispatch] Compilation failed", file=sys.stderr)
        return None


def dispatch(task_name: str, prompt_text: str, pdf_path: Path | None = None) -> Path:
    """Write task to oracle/pending/ for the watch process to pick up.

    Returns the expected result path in oracle/done/.
    """
    pending = ORACLE_DIR / "pending"
    done = ORACLE_DIR / "done"
    pending.mkdir(parents=True, exist_ok=True)
    done.mkdir(parents=True, exist_ok=True)

    # Write instruction prompt
    prompt_file = pending / f"{task_name}.md"
    prompt_file.write_text(prompt_text, encoding="utf-8")
    print(f"[dispatch] Prompt written: {prompt_file} ({len(prompt_text)} chars)")

    # Copy PDF if provided
    if pdf_path and pdf_path.exists():
        pdf_dest = pending / f"{task_name}.pdf"
        shutil.copy2(pdf_path, pdf_dest)
        print(f"[dispatch] PDF copied: {pdf_dest} ({pdf_dest.stat().st_size // 1024} KB)")

    return done / f"{task_name}.md"


def wait_for_result(result_path: Path, timeout: int = 900, poll: int = 5) -> str:
    """Poll until the result file appears in oracle/done/."""
    print(f"[dispatch] Waiting for result: {result_path}")
    start = time.time()
    last_msg = start

    while time.time() - start < timeout:
        if result_path.exists():
            content = result_path.read_text(encoding="utf-8")
            if content and "ERROR" not in content[:100]:
                print(f"[dispatch] Result received ({len(content)} chars)")
                return content
            elif "ERROR" in content[:100]:
                print(f"[dispatch] Oracle returned error", file=sys.stderr)
                return content

        now = time.time()
        if now - last_msg >= 30:
            elapsed = int(now - start)
            print(f"[dispatch] Still waiting... ({elapsed}s)")
            last_msg = now

        time.sleep(poll)

    print(f"[dispatch] Timeout after {timeout}s", file=sys.stderr)
    return ""


def main():
    parser = argparse.ArgumentParser(
        description="Oracle dispatch — submit tasks to ChatGPT Pro oracle",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--paper", type=Path,
                        help="Paper directory (will compile main.tex to PDF)")
    parser.add_argument("--task", type=str, choices=list(TASK_TEMPLATES.keys()),
                        help="Task template name")
    parser.add_argument("--prompt", type=Path,
                        help="Custom prompt file (overrides --task)")
    parser.add_argument("--prompt-text", type=str,
                        help="Inline prompt text (overrides --task and --prompt)")
    parser.add_argument("--name", type=str,
                        help="Task name (default: auto-generated from paper + task)")
    parser.add_argument("--wait", action="store_true",
                        help="Wait for result and print it")
    parser.add_argument("--timeout", type=int, default=900,
                        help="Max seconds to wait for result (default: 900)")
    parser.add_argument("--no-compile", action="store_true",
                        help="Skip PDF compilation (use existing main.pdf)")
    args = parser.parse_args()

    # Determine prompt text
    if args.prompt_text:
        prompt_text = args.prompt_text
    elif args.prompt:
        prompt_text = args.prompt.read_text(encoding="utf-8")
    elif args.task:
        prompt_text = TASK_TEMPLATES[args.task]
    else:
        print("Error: need --task, --prompt, or --prompt-text", file=sys.stderr)
        sys.exit(1)

    # Compile PDF if paper directory given
    pdf_path = None
    if args.paper:
        if args.no_compile:
            pdf_path = args.paper / "main.pdf"
            if not pdf_path.exists():
                print(f"Error: {pdf_path} not found (use without --no-compile)", file=sys.stderr)
                sys.exit(1)
        else:
            pdf_path = compile_paper(args.paper)

    # Generate task name
    if args.name:
        task_name = args.name
    else:
        parts = []
        if args.paper:
            parts.append(args.paper.name[:40])
        if args.task:
            parts.append(args.task)
        parts.append(datetime.now().strftime("%H%M%S"))
        task_name = "_".join(parts)

    # Dispatch
    result_path = dispatch(task_name, prompt_text, pdf_path)

    if args.wait:
        result = wait_for_result(result_path, timeout=args.timeout)
        if result:
            print(f"\n{'='*60}")
            print(result)
        else:
            sys.exit(1)
    else:
        print(f"[dispatch] Task dispatched. Result will appear at: {result_path}")
        print(f"[dispatch] Make sure chatgpt_oracle.py --watch is running!")


if __name__ == "__main__":
    main()
