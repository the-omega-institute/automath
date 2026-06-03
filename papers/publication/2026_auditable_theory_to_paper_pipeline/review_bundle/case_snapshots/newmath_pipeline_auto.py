#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Fully automated publication pipeline runner.

Scans all paper directories, determines current stage, and generates
the next action for each paper. Designed to be called by Claude Code
agents for zero-human-intervention pipeline execution.

Usage:
    # Show status of all papers:
    python pipeline_auto.py status

    # Advance a specific paper to next stage:
    python pipeline_auto.py advance <paper_dir>

    # Advance all papers that are ready:
    python pipeline_auto.py advance-all

    # Run quality gate on a paper:
    python pipeline_auto.py check <paper_dir> [--stage P4]

    # Generate agent prompt for next stage:
    python pipeline_auto.py prompt <paper_dir>
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from datetime import datetime

PUB_ROOT = Path(__file__).parent
PAPERS_GLOB = "2026_*"


# ---------------------------------------------------------------------------
# Paper state detection
# ---------------------------------------------------------------------------

def detect_paper_state(paper_dir: Path) -> dict:
    """Detect the current pipeline state of a paper directory."""
    state = {
        "dir": paper_dir.name,
        "path": str(paper_dir),
        "has_main_tex": (paper_dir / "main.tex").exists(),
        "has_pipeline_md": (paper_dir / "PIPELINE.md").exists(),
        "has_bib": (paper_dir / "references.bib").exists(),
        "tex_files": sorted([f.name for f in paper_dir.glob("*.tex")]),
        "tex_lines": 0,
        "current_stage": "UNKNOWN",
        "target_journal": "",
        "blockers": [],
    }

    # Count total .tex lines
    for tex in paper_dir.glob("*.tex"):
        state["tex_lines"] += sum(1 for _ in tex.open(encoding="utf-8", errors="ignore"))

    if not state["has_main_tex"]:
        state["current_stage"] = "NO_MAIN_TEX"
        state["blockers"].append("No main.tex — skeleton only")
        return state

    # Parse PIPELINE.md for current stage
    if state["has_pipeline_md"]:
        pipeline = (paper_dir / "PIPELINE.md").read_text(encoding="utf-8", errors="ignore")
        state["current_stage"] = _parse_stage_from_pipeline(pipeline)
        state["target_journal"] = _parse_journal_from_pipeline(pipeline)
    else:
        state["current_stage"] = "P0_NEEDED"

    # Detect what artifacts exist
    state["has_cover_letter"] = bool(list(paper_dir.glob("cover_letter_*")))
    state["has_checklist"] = (paper_dir / "submission_checklist.md").exists()

    return state


def _parse_stage_from_pipeline(text: str) -> str:
    """Extract current stage from PIPELINE.md content."""
    # Look for stage markers
    stage_patterns = [
        (r"P7.*(?:complete|done|PASS|SUBMISSION.READY)", "P7_DONE"),
        (r"P6.*(?:complete|done)", "P6_DONE"),
        (r"P5.*(?:complete|done)", "P5_DONE"),
        (r"P4G.*ACCEPT", "P4G_ACCEPT"),
        (r"P4G.*(?:MAJOR|REVISE)", "P4G_REVISE"),
        (r"P4G.*(?:complete|done)", "P4G_DONE"),
        (r"P4.*(?:complete|done)", "P4_DONE"),
        (r"P3.*(?:complete|done)", "P3_DONE"),
        (r"P2.*(?:complete|done)", "P2_DONE"),
        (r"P1.*(?:complete|done)", "P1_DONE"),
        (r"P0.*(?:complete|done)", "P0_DONE"),
    ]
    for pattern, stage in stage_patterns:
        if re.search(pattern, text, re.IGNORECASE):
            return stage

    # Look for "Current stage" explicit marker
    m = re.search(r"(?:current|status|stage)\s*[:=]\s*(P\d)", text, re.IGNORECASE)
    if m:
        return m.group(1)

    return "P0_DONE"  # Has PIPELINE.md but no clear stage -> assume P0 done


def _parse_journal_from_pipeline(text: str) -> str:
    """Extract target journal from PIPELINE.md."""
    m = re.search(r"(?:target|journal)\s*[:=|]\s*(.+?)(?:\n|\|)", text, re.IGNORECASE)
    if m:
        return m.group(1).strip().strip("*").strip()
    return ""


def next_stage(current: str) -> str:
    """Determine the next pipeline stage.

    Flow: P0 -> P1 -> P2 -> P3 -> P4 -> P4G -> P5 -> P6 -> P7
    P4G = ChatGPT Pro acceptance gate (hard requirement).
    If P4G returns MAJOR_REVISION: loop back to P5 then P4G again.
    """
    progression = {
        "NO_MAIN_TEX": "SKIP",
        "P0_NEEDED": "P0",
        "P0_DONE": "P1",
        "P0": "P1",
        "P1_DONE": "P2",
        "P1": "P2",
        "P2_DONE": "P3",
        "P2": "P3",
        "P3_DONE": "P4",
        "P3": "P4",
        "P4_DONE": "P4G",
        "P4": "P4G",
        "P4G_DONE": "P5",
        "P4G_ACCEPT": "P5",
        "P4G_REVISE": "P5",  # fix then resubmit to P4G
        "P5_DONE": "P6",
        "P5": "P6",
        "P6_DONE": "P7",
        "P6": "P7",
        "P7_DONE": "COMPLETE",
        "P7": "COMPLETE",
        "UNKNOWN": "P0",
    }
    return progression.get(current, "P0")


# ---------------------------------------------------------------------------
# Quality gate (wraps pub_check.py)
# ---------------------------------------------------------------------------

def run_quality_check(paper_dir: Path, stage: str = "P7") -> dict:
    """Run pub_check.py and return results."""
    pub_check = PUB_ROOT / "pub_check.py"
    if not pub_check.exists():
        return {"error": "pub_check.py not found"}

    result = subprocess.run(
        ["python", str(pub_check), str(paper_dir), "--stage", stage, "--json"],
        capture_output=True, text=True, encoding="utf-8", timeout=60
    )

    try:
        return json.loads(result.stdout)
    except (json.JSONDecodeError, ValueError):
        return {"error": result.stderr or result.stdout, "returncode": result.returncode}


# ---------------------------------------------------------------------------
# Agent prompt generation
# ---------------------------------------------------------------------------

def generate_agent_prompt(paper_dir: Path, stage: str) -> str:
    """Generate a self-contained prompt for a Claude agent to execute a pipeline stage."""

    paper_name = paper_dir.name
    tex_files = sorted(paper_dir.glob("*.tex"))
    tex_list = ", ".join(f.name for f in tex_files)

    prompts = {
        "P0": f"""## P0 Intake: {paper_name}

Read all .tex files in {paper_dir}. Create PIPELINE.md with:
1. Paper title and target journal (infer from content/dirname)
2. Scope statement (1 paragraph)
3. Stage table (P0-P7 with status)
4. MSC codes
5. Initial assessment: is this a complete paper or a skeleton?

Files: {tex_list}""",

        "P1": f"""## P1 Traceability: {paper_name}

Read all .tex files in {paper_dir}. Update PIPELINE.md with:
1. Theorem inventory table: Label | Type | Statement (1-line) | Status (proved/partial/gap)
2. Dependency graph: which theorems depend on which
3. Source map: which results come from the core paper vs. are new

Scan for: \\begin{{theorem}}, \\begin{{proposition}}, \\begin{{lemma}}, \\begin{{corollary}}, \\begin{{definition}}
Every claim must have a \\label. Flag any that don't.

Files: {tex_list}""",

        "P2": f"""## P2 Research Extension: {paper_name}

Read the FULL paper (all .tex files in {paper_dir}).
You are a mathematical research consultant. Your job is to DEEPEN this paper to editor-acceptance quality.

Requirements:
- Find genuinely novel, publishable results that extend the paper's framework
- Do NOT repeat known results — cite them
- Do NOT provide intermediate or trivial conclusions
- Each new result must be a formal theorem/proposition with complete proof
- Use rigorous academic language, no colloquial speech
- As a journal editor, would you accept this paper? If not, what's missing?

Deliverables (write directly into the .tex files):
1. Strengthen weak theorems — sharpen bounds, remove unnecessary hypotheses
2. Fill proof gaps — every "standard argument" or "routine" needs the actual proof or a precise reference
3. Add 1-3 genuinely new results that would make an editor say "this is interesting"
4. Clean bibliography — remove uncited entries, add missing references
5. Update PIPELINE.md: mark P2 complete, list what was added/changed

Do NOT generate change logs or summaries. Just improve the paper directly.

Files: {tex_list}""",

        "P3": f"""## P3 Journal-Fit Rewrite: {paper_name}

Read PIPELINE.md for target journal info, then read all .tex files in {paper_dir}.

Rewrite for journal fit:
1. Abstract: <250 words, state main results precisely, include MSC codes
2. Introduction: clear theorem preview with forward references, motivation, comparison with prior work
3. Style: match target journal conventions (theorem numbering, proof style, citation format)
4. Ensure all files stay under 800 lines
5. No revision-trace language ("we have improved...", "in this version...")

Edit .tex files directly. Update PIPELINE.md: mark P3 complete.

Files: {tex_list}""",

        "P4": f"""## P4 Editorial Review: {paper_name}

Read the FULL paper (all .tex files in {paper_dir}).
Act as a referee for the target journal. Be rigorous and specific.

This is a PRE-REVIEW before the formal ChatGPT Pro acceptance gate.
Your job: find and fix everything BEFORE we submit to ChatGPT for final verdict.

Produce a review in PIPELINE.md with:
1. Decision: ACCEPT / MINOR REVISION / MAJOR REVISION / REJECT
2. Issue table:
   | ID | Section | Severity | Description | Suggested Fix |
   Each issue must reference specific theorem labels, line content, or section numbers.
3. Missing references
4. Strengths (what makes this paper publishable)
5. Overall assessment

Also run: python pub_check.py {paper_dir} --stage P4
Include automated check results in the review.

Mark P4 complete in PIPELINE.md.

Files: {tex_list}""",

        "P4G": f"""## P4G ChatGPT Acceptance Gate: {paper_name}

This paper has passed Claude's internal review (P4).
Now submit to ChatGPT Pro for independent acceptance decision.

Steps:
1. Compile PDF: cd {paper_dir} && pdflatex main.tex (with bibtex if needed)
2. Queue for ChatGPT review:
   python oracle_dispatch.py --paper {paper_dir} --task editorial_review --no-compile --wait
3. Read the ChatGPT response from oracle/done/

Decision logic:
- If ChatGPT says ACCEPT or MINOR REVISION (with only cosmetic issues) -> proceed to P5
- If MAJOR REVISION -> extract issues, run P5 to fix, then resubmit to P4G
- If REJECT -> escalate to user for manual review

Update PIPELINE.md with ChatGPT's verdict and iterate count.

Files: {tex_list}""",

        "P5": f"""## P5 Integration: {paper_name}

Read PIPELINE.md P4 review in {paper_dir}. For EVERY issue listed:
1. If BLOCKER: fix it in the .tex files
2. If MEDIUM: fix it
3. If LOW: fix if straightforward, otherwise note as deferred

After fixing:
- Re-run: python pub_check.py {paper_dir} --stage P5
- Verify all cross-references resolve
- Verify all citations have bib entries and vice versa
- Ensure no file exceeds 800 lines

Edit .tex files directly. Update PIPELINE.md: mark P5 complete, note what was fixed.

Files: {tex_list}""",

        "P6": f"""## P6 Lean Sync: {paper_name}

Check the paper's theorem inventory against the Lean4 formalization.

1. Read PIPELINE.md theorem inventory
2. Search lean4/Omega/ for any matching formalizations
3. Report coverage: which theorems are formalized, which are not
4. Note any mismatches between paper statements and Lean statements

Update PIPELINE.md with Lean sync results. Mark P6 complete.
Note: Low coverage is acceptable — we track it but don't block submission.

Paper dir: {paper_dir}
Lean dir: lean4/Omega/""",

        "P7": f"""## P7 Submission Pack: {paper_name}

Read PIPELINE.md and all .tex files in {paper_dir}.

Generate:
1. cover_letter_<journal>.txt — professional cover letter (adapt to target journal)
2. submission_checklist.md — verify all items:
   - [ ] Title page complete
   - [ ] Abstract <250 words
   - [ ] MSC codes present
   - [ ] All references cited and complete
   - [ ] No TODO/FIXME markers
   - [ ] All proofs complete
   - [ ] Files under 800 lines
   - [ ] No revision-trace language
   - [ ] Figures/tables properly labeled (if any)
   - [ ] Author metadata (placeholder OK)

Mark P7 complete in PIPELINE.md. Set status to SUBMISSION-READY.

Files: {tex_list}""",
    }

    return prompts.get(stage, f"Unknown stage: {stage}")


# ---------------------------------------------------------------------------
# Status display
# ---------------------------------------------------------------------------

def show_status():
    """Display pipeline status for all papers."""
    papers = sorted(PUB_ROOT.glob(PAPERS_GLOB))
    if not papers:
        print("No paper directories found.")
        return

    print(f"{'Paper':<55} {'Stage':<12} {'Next':<6} {'Lines':>6} {'Journal'}")
    print("-" * 110)

    for p in papers:
        if not p.is_dir():
            continue
        state = detect_paper_state(p)
        nxt = next_stage(state["current_stage"])
        journal = state["target_journal"][:25] if state["target_journal"] else "-"
        print(f"{state['dir'][:54]:<55} {state['current_stage']:<12} {nxt:<6} {state['tex_lines']:>6} {journal}")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Fully automated publication pipeline runner",
    )
    sub = parser.add_subparsers(dest="command")

    sub.add_parser("status", help="Show pipeline status for all papers")

    adv = sub.add_parser("advance", help="Show next action for a paper")
    adv.add_argument("paper_dir", type=Path)

    sub.add_parser("advance-all", help="Show next actions for all papers")

    chk = sub.add_parser("check", help="Run quality gate")
    chk.add_argument("paper_dir", type=Path)
    chk.add_argument("--stage", default="P7")

    prm = sub.add_parser("prompt", help="Generate agent prompt for next stage")
    prm.add_argument("paper_dir", type=Path)
    prm.add_argument("--stage", help="Override stage (default: auto-detect next)")

    args = parser.parse_args()

    if args.command == "status":
        show_status()

    elif args.command == "advance":
        state = detect_paper_state(args.paper_dir)
        nxt = next_stage(state["current_stage"])
        print(f"Paper: {state['dir']}")
        print(f"Current: {state['current_stage']}")
        print(f"Next: {nxt}")
        if state["blockers"]:
            print(f"Blockers: {', '.join(state['blockers'])}")

    elif args.command == "advance-all":
        papers = sorted(PUB_ROOT.glob(PAPERS_GLOB))
        actionable = []
        for p in papers:
            if not p.is_dir():
                continue
            state = detect_paper_state(p)
            nxt = next_stage(state["current_stage"])
            if nxt not in ("SKIP", "COMPLETE"):
                actionable.append((state, nxt))

        if not actionable:
            print("All papers are either complete or skipped.")
            return

        print(f"{len(actionable)} papers need advancement:\n")
        for state, nxt in actionable:
            print(f"  {state['dir'][:60]}")
            print(f"    Current: {state['current_stage']} -> Next: {nxt}")
            print()

    elif args.command == "check":
        results = run_quality_check(args.paper_dir, args.stage)
        print(json.dumps(results, indent=2))

    elif args.command == "prompt":
        state = detect_paper_state(args.paper_dir)
        stage = args.stage or next_stage(state["current_stage"])
        prompt = generate_agent_prompt(args.paper_dir, stage)
        print(prompt)

    else:
        parser.print_help()


if __name__ == "__main__":
    main()
