#!/usr/bin/env python3
"""Ask Codex for a STRATEGIC recommendation on a REJECT paper.

Unlike codex_fix.py (which patches), this script has Codex READ the review
and the paper, then write a strategic analysis: venue change, scope split,
claim reduction, or structural rewrite. Claude reviews the output.
"""

import argparse
import subprocess
import sys
import time
from pathlib import Path

PUB_DIR = Path(__file__).parent
STRATEGY_DIR = PUB_DIR / "oracle" / "strategy"
STRATEGY_DIR.mkdir(parents=True, exist_ok=True)

STRATEGY_PROMPT = """You are an experienced journal editor and strategic advisor for a research team.
A paper has received a REJECT recommendation from a referee.

Your task is NOT to rewrite the paper. Your task is to read the referee report
and the paper, then WRITE A STRATEGIC RECOMMENDATION. The recommendation will
be reviewed by the team lead who decides next steps.

Read the following files:
1. The referee report at: {review_path}
2. The paper LaTeX sources in this directory (main.tex, abstract, introduction)

Then write a strategic analysis with these sections:

## 1. Root cause of rejection
One paragraph: what is the REAL problem the referee is identifying?
Do NOT just restate issues. Diagnose the deep structural issue.

## 2. Options
Enumerate at least 3 distinct strategic options with explicit tradeoffs.
Each option should be one of:
- **Deep mathematical rewrite** (fix the missing theorem/proof rigorously)
- **Scope reduction** (drop overstated claims, present as short note)
- **Venue change** (propose specific alternative journal with rationale)
- **Scope split** (divide into 2 papers)
- **Merge** (fold into another paper as section/appendix)
- **Abandon / park** (shelve until new results arrive)

For each option give:
- concrete subtasks required
- estimated effort (hours of focused work)
- probability of acceptance after the change
- downside risk

## 3. Recommendation
ONE option ranked first, with explicit justification for why it beats the others.

## 4. If chosen, the first 3 concrete actions
Specific, testable tasks you would do in the first sprint.

## 5. Red flags
Anything that might make even the recommendation fail.

Be blunt. If the paper is unsalvageable, say so. If the referee is wrong
about something, say so and explain why. If the paper needs to be merged
or abandoned, recommend it.

Do NOT edit any files. Do NOT rewrite the paper. Only write the strategy
document to stdout.
"""


def run_strategy(paper_dir: Path, review_path: Path, timeout: int = 1800,
                 model: str = "gpt-5-codex") -> dict:
    """Run Codex strategy analysis on a paper."""
    import shutil

    codex_bin = shutil.which("codex") or "codex"
    if sys.platform == "win32":
        npm_codex = Path.home() / "AppData" / "Roaming" / "npm" / "codex.cmd"
        if npm_codex.exists():
            codex_bin = str(npm_codex)

    prompt = STRATEGY_PROMPT.format(review_path=review_path)

    cmd = [codex_bin, "exec"]
    cmd += ["-c", f'model="{model}"']
    cmd += ["-c", 'model_reasoning_effort="high"']
    cmd += ["--full-auto", "-"]

    print(f"[strategy] {paper_dir.name}")
    print(f"[strategy] review: {review_path.name}")
    print(f"[strategy] model: {model}")

    start = time.time()
    try:
        result = subprocess.run(
            cmd, cwd=str(paper_dir),
            input=prompt,
            capture_output=True, text=True,
            timeout=timeout,
            encoding="utf-8", errors="replace",
            shell=(sys.platform == "win32" and codex_bin.lower().endswith(".cmd")),
        )
        elapsed = time.time() - start
        return {
            "paper": paper_dir.name,
            "returncode": result.returncode,
            "stdout": result.stdout,
            "stderr": result.stderr,
            "elapsed": elapsed,
            "success": result.returncode == 0,
        }
    except subprocess.TimeoutExpired:
        return {"paper": paper_dir.name, "returncode": -1, "stdout": "",
                "stderr": "Timeout", "elapsed": timeout, "success": False}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--paper", required=True)
    parser.add_argument("--review", required=True)
    parser.add_argument("--out", help="Output file for strategy (default: auto)")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--model", default="gpt-5-codex")
    args = parser.parse_args()

    paper_dir = Path(args.paper).resolve()
    review_path = Path(args.review).resolve()

    if not paper_dir.exists():
        print(f"ERROR: paper dir not found: {paper_dir}")
        sys.exit(2)
    if not review_path.exists():
        print(f"ERROR: review not found: {review_path}")
        sys.exit(2)

    result = run_strategy(paper_dir, review_path, args.timeout, args.model)

    # Save full stdout to strategy dir
    short = paper_dir.name.replace("2026_", "")[:40]
    out_path = Path(args.out) if args.out else STRATEGY_DIR / f"{short}_strategy.md"
    out_path.write_text(
        f"<!-- paper: {paper_dir.name} | review: {review_path.name} | "
        f"elapsed: {result['elapsed']:.0f}s | rc: {result['returncode']} -->\n\n"
        f"{result['stdout']}\n",
        encoding="utf-8",
    )

    print(f"[strategy] {'OK' if result['success'] else 'FAIL'} "
          f"({result['elapsed']:.0f}s) -> {out_path}")

    if not result["success"]:
        print(f"[strategy] stderr: {result['stderr'][:300]}")
        sys.exit(1)


if __name__ == "__main__":
    main()
