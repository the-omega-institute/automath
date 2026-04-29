#!/usr/bin/env python3
"""Ask Codex to EXECUTE a strategic plan: venue change + deep mathematical repair.

Unlike codex_fix.py (surface patching), this script feeds Codex:
1. The referee report
2. The strategic recommendation (from codex_strategy.py)
3. A target venue override

Codex then performs the deep rewrite: retargets the venue in the paper's
metadata/abstract/intro, fixes the mathematical blockers identified in the
review and strategy, and writes changes directly to the paper directory.

Use this only AFTER a strategy document has been reviewed and approved
by the team lead.
"""

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path

PUB_DIR = Path(__file__).parent


EXECUTE_PROMPT = """You are a senior mathematics paper editor executing an approved
strategic rewrite plan. The paper was REJECTED and the team lead has decided to
(a) switch target venue and (b) perform a deep mathematical repair.

PAPER DIRECTORY: {paper_name}
TEX FILES:
{tex_list}

=== REFEREE REPORT ===
{review_text}

=== APPROVED STRATEGY DOCUMENT ===
{strategy_text}

=== TARGET VENUE OVERRIDE ===
New target venue: {venue}

=== INSTRUCTIONS ===

1. **Read** all .tex source files and the bibliography (if present).

2. **Retarget the venue**:
   - Update the journal-targeting comment in main.tex (e.g., "% target: ...") to {venue}.
   - Rewrite the abstract to match the new venue's register (shorter for short-note
     venues, sharper positioning for general venues).
   - Rewrite the introduction's "positioning" paragraph so that the claimed
     contribution matches what the paper actually delivers. Do NOT overclaim.
   - If the paper currently labels results as "classical" or "conditional", make
     that honest labeling consistent throughout.

3. **Deep mathematical repair** — implement the strategy document's Section 4
   ("first 3 concrete actions") and address the blockers identified in Section 1
   ("Root cause of rejection"):
   - Apply the mathematical content upgrade the strategy recommends (new theorem,
     extended class, fixed proof, invariance argument, etc.).
   - Fix every concrete mathematical error flagged by the referee. If the referee
     points to a specific example or lemma, correct it rigorously.
   - Add missing literature citations the referee listed, and position the work
     relative to them.
   - Demote overstated results to propositions/remarks where the referee said
     they do not carry the theorem-level weight.

4. **Constraints**:
   - ONLY edit .tex and .bib files INSIDE {paper_name}/.
   - Do NOT create revision-tracking comments, changelogs, "fixed B1" markers,
     or version annotations. Clean final text only.
   - Do NOT delete entire sections unless the strategy explicitly instructs it.
   - Preserve the paper's voice. Keep cross-references consistent after edits.
   - If a claim cannot be repaired with the available machinery, remove or
     weaken it honestly rather than hand-waving.

5. **After editing**, briefly list (to stdout, not in the paper):
   - Which blockers you repaired and how.
   - Which theorems/sections you added, demoted, or removed.
   - Any blocker you could NOT repair, with reason.

Begin now. Work autonomously; do not ask questions.
"""


def build_prompt(paper_dir: Path, review_text: str, strategy_text: str, venue: str) -> str:
    tex_files = sorted(paper_dir.glob("**/*.tex"))
    tex_list = "\n".join(f"  - {f.relative_to(paper_dir)}" for f in tex_files)
    return EXECUTE_PROMPT.format(
        paper_name=paper_dir.name,
        tex_list=tex_list,
        review_text=review_text,
        strategy_text=strategy_text,
        venue=venue,
    )


def find_codex_binary() -> str:
    codex = shutil.which("codex")
    if codex:
        return codex
    if sys.platform == "win32":
        npm_path = Path.home() / "AppData" / "Roaming" / "npm" / "codex.cmd"
        if npm_path.exists():
            return str(npm_path)
    return "codex"


def run_codex(prompt: str, paper_dir: Path, model: str, timeout: int) -> dict:
    codex_bin = find_codex_binary()
    cmd = [codex_bin, "exec", "--json"]
    cmd += ["-c", f'model="{model}"']
    if "codex" in model.lower():
        cmd += ["-c", 'model_reasoning_effort="high"']
    cmd += ["--full-auto", "-"]

    print(f"[execute] {paper_dir.name}")
    print(f"[execute] prompt: {len(prompt)} chars")
    print(f"[execute] model: {model}")

    use_shell = sys.platform == "win32" and codex_bin.lower().endswith(".cmd")
    try:
        result = subprocess.run(
            cmd, cwd=str(paper_dir), input=prompt,
            capture_output=True, text=True,
            timeout=timeout,
            encoding="utf-8", errors="replace",
            shell=use_shell,
        )
        lines = []
        for line in result.stdout.strip().split("\n"):
            line = line.strip()
            if not line:
                continue
            try:
                lines.append(json.loads(line))
            except json.JSONDecodeError:
                lines.append({"raw": line})
        return {
            "returncode": result.returncode,
            "output": lines,
            "stderr": result.stderr,
            "success": result.returncode == 0,
        }
    except subprocess.TimeoutExpired:
        return {"returncode": -1, "output": [], "stderr": "Timeout", "success": False}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--paper", required=True)
    parser.add_argument("--review", required=True)
    parser.add_argument("--strategy", required=True)
    parser.add_argument("--venue", required=True,
                        help='Target venue name (e.g., "Integral Equations and Operator Theory")')
    parser.add_argument("--model", default="gpt-5-codex")
    parser.add_argument("--timeout", type=int, default=5400)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    paper_dir = Path(args.paper).resolve()
    review_path = Path(args.review).resolve()
    strategy_path = Path(args.strategy).resolve()

    for p, label in [(paper_dir, "paper"), (review_path, "review"),
                     (strategy_path, "strategy")]:
        if not p.exists():
            print(f"[execute] ERROR: {label} not found: {p}")
            sys.exit(2)

    review_text = review_path.read_text(encoding="utf-8", errors="replace")
    if review_text.startswith("<!--"):
        review_text = review_text.split("-->", 1)[-1].strip()

    strategy_text = strategy_path.read_text(encoding="utf-8", errors="replace")
    if strategy_text.startswith("<!--"):
        strategy_text = strategy_text.split("-->", 1)[-1].strip()

    prompt = build_prompt(paper_dir, review_text, strategy_text, args.venue)

    if args.dry_run:
        print("=== PROMPT (first 2000 chars) ===")
        print(prompt[:2000])
        print(f"... ({len(prompt)} chars total)")
        return 0

    result = run_codex(prompt, paper_dir, args.model, args.timeout)

    if result["success"]:
        print("[execute] SUCCESS")
        for item in result["output"][-6:]:
            if isinstance(item, dict):
                for key in ("finalMessage", "message"):
                    if key in item:
                        print(f"  [{key}] {str(item[key])[:500]}")
        return 0
    else:
        print(f"[execute] FAILED (exit {result['returncode']})")
        if result["stderr"]:
            print(f"  stderr: {result['stderr'][:500]}")
        for item in result["output"][-5:]:
            if isinstance(item, dict):
                for key in ("raw", "finalMessage", "error", "message"):
                    if key in item:
                        print(f"  [{key}] {str(item[key])[:300]}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
