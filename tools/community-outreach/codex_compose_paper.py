#!/usr/bin/env python3
"""codex_compose_paper.py — Round 3 codex polish (paper synthesis).

When Oracle has produced multiple substantive deep-reasoning turns but the
WRITE_PAPER_LATEX terminal turn fails to elicit LaTeX (because Oracle decides
its result isn't "complete enough" — common when partial / open frontier
remains), this driver hands the deep-run transcripts to codex CLI and asks
codex to compose the LaTeX paper directly. Codex is the editor agent in the
pipeline; Oracle is the deep reasoner. When the reasoner refuses to author,
the editor still can.

The composed LaTeX is saved at theory/2026_outreach_<slug>/main.tex and is
ready for `oracle_consultant.generate_outreach_paper()` polish + the P0-P7
publication pipeline.

Usage:
    python3 codex_compose_paper.py --conv conv_4b15545d611f46c5 \\
        --target T-20 --slug arxiv_2604_25214 \\
        --venue "Ergodic Theory and Dynamical Systems"
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).parent))

import oracle_consultant as oc  # noqa: E402

SESS_DIR = REPO_ROOT / "tools/community-outreach/outreach_oracle/sessions"


COMPOSER_PROMPT_TEMPLATE = r"""You are codex acting as the paper-composer for the Omega community-outreach
pipeline. The deep oracle (ChatGPT 5.5 Pro) ran several reasoning turns on a
target conjecture and produced substantive theorems plus an open frontier.
Compose the resulting short paper as LaTeX.

# Target
- Repository: the-omega-institute/automath
- Target id: {target}
- Submission target: {venue}

# Oracle deep-run transcripts
The deep run lives at conversation_id = {conv_id}. The relevant turns (raw
oracle output, possibly with markdown formatting noise) are below. Pull out
the proved statements, set them up as numbered theorems, write proofs in
self-contained LaTeX, and frame the open frontier as a final section.

## Turn 1 (Singer-affine all-q obstruction)

{turn_1}

## Turn 2 (multiplier descent, q<41 reduction, q=41 setup)

{turn_2}

# Compose the paper

Write a single self-contained LaTeX document at:

    {target_path}

Requirements:

1. Document class amsart or article with amsmath / amsthm / amssymb preamble.
   No exotic packages. Standard {{document}} body.

2. Sections in order: Abstract, Introduction (motivation + Niu 2604.25214
   context), Preliminaries (Singer construction, Frobenius/multiplier orbits,
   notation), Main results (Theorem 1 = Singer-affine all-q obstruction;
   Theorem 2 = q < 41 reduction to Singer; Lemma 3 = q = 41 forced-core
   reduction to a finite exact-cover problem with explicit equation system),
   Discussion / Open questions (q = 41 MILP frontier, possible non-Singer
   cyclic plane obstructions for q in {{49, 53, 64, 71, ...}}), References.

3. Theorem statements precise. Proofs complete from the oracle's Turn 1
   trace-rank reduction and Turn 2 multiplier-descent argument. Quote the
   classical Huang-Schmidt 2010 multiplier theorem with citation. Include the
   explicit char != 2 vs char = 2 case split for Theorem 1's pattern A; the
   y^3 - 2y^2 + 3y - 1 = (1-y)^3 - (1-y)^2 + (1-y) - y identity for pattern B.

4. Length target 8-15 pages. Self-contained — a referee in arithmetic
   dynamics or symbolic dynamics should be able to verify without consulting
   our internal Lean library.

5. References: include arXiv IDs and venue volumes where known. The Niu paper
   is arXiv:2604.25214 (2026). The Huang-Schmidt reference is the NTU pdf
   `https://personal.ntu.edu.sg/bernhard/Publications/pub/Singer.pdf`.

6. Write directly to {target_path}. Do not produce any other files. Do not
   modify anything outside that path.

7. Output discipline: no version markers, no "v1.0/draft" labels in the body
   or in commit messages. The paper is presented as current state.

After writing, verify the file compiles with pdflatex (do not commit if it
fails). If pdflatex is unavailable in this environment, just write the LaTeX
and report compilation as untested.
"""


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--conv", required=True, help="conversation_id of the deep run")
    p.add_argument("--target", required=True, help="TODO id (e.g. T-20)")
    p.add_argument("--slug", required=True, help="paper slug, used for output path")
    p.add_argument("--venue", default="Ergodic Theory and Dynamical Systems",
                   help="target submission venue (default ETDS)")
    p.add_argument("--codex-bin", default=str(oc.CODEX_BIN))
    p.add_argument("--timeout", type=int, default=3600)
    args = p.parse_args()

    sess_path = SESS_DIR / f"{args.conv}.json"
    if not sess_path.exists():
        print(f"ERR: session {sess_path} not found", file=sys.stderr)
        return 1
    sess = json.loads(sess_path.read_text())
    turns = sess.get("turns", []) or []
    if len(turns) < 2:
        print(f"ERR: need at least 2 turns; have {len(turns)}", file=sys.stderr)
        return 1

    target_path = REPO_ROOT / "theory" / f"2026_outreach_{args.slug}" / "main.tex"
    target_path.parent.mkdir(parents=True, exist_ok=True)

    prompt = COMPOSER_PROMPT_TEMPLATE.format(
        target=args.target,
        venue=args.venue,
        conv_id=args.conv,
        turn_1=turns[0].get("response","").strip(),
        turn_2=turns[1].get("response","").strip(),
        target_path=str(target_path),
    )

    log_dir = REPO_ROOT / "tools/community-outreach/logs/oracle"
    log_dir.mkdir(parents=True, exist_ok=True)
    prompt_log = log_dir / f"codex_compose_{args.target}_{int(time.time())}.txt"
    prompt_log.write_text(f"=== prompt ===\n{prompt}\n", encoding="utf-8")
    print(f"[compose] prompt logged → {prompt_log}")

    # Note: distill.codex_exec uses --sandbox read-only by default which prevents
    # file writes — wrong for paper composition. We invoke codex directly with
    # --dangerously-bypass-approvals-and-sandbox so codex can create the LaTeX
    # file at target_path. Mirrors generate_outreach_paper's invocation.
    codex = Path(args.codex_bin)
    if not codex.exists():
        print(f"ERR: codex CLI not found at {codex}", file=sys.stderr)
        return 2

    print(f"[compose] dispatching codex (timeout {args.timeout}s)...")
    print(f"[compose] target: {target_path}")
    try:
        result = subprocess.run(
            [
                str(codex),
                "exec",
                "--dangerously-bypass-approvals-and-sandbox",
                "-C",
                str(REPO_ROOT),
                prompt,
            ],
            capture_output=True,
            text=True,
            timeout=args.timeout,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
    except subprocess.TimeoutExpired:
        print(f"[compose] codex timed out after {args.timeout}s", file=sys.stderr)
        return 3
    except Exception as exc:
        print(f"[compose] codex failed: {exc}", file=sys.stderr)
        return 3

    output = (result.stdout or "")
    err = (result.stderr or "").strip()
    print(f"[compose] codex rc={result.returncode}, stdout={len(output)} chars, stderr={len(err)} chars")
    if err:
        print(f"[compose] stderr (first 500): {err[:500]}", file=sys.stderr)
    # Save codex stdout for traceability
    stdout_log = log_dir / f"codex_compose_{args.target}_{int(time.time())}.stdout.txt"
    stdout_log.write_text(output, encoding="utf-8")
    print(f"[compose] codex stdout → {stdout_log}")

    if target_path.exists():
        size = target_path.stat().st_size
        has_documentclass = r"\documentclass" in target_path.read_text(encoding="utf-8", errors="replace")
        print(f"[compose] {target_path} exists: {size} bytes, has \\documentclass: {has_documentclass}")
        return 0 if has_documentclass else 4
    else:
        print(f"[compose] WARN: codex did not create {target_path}", file=sys.stderr)
        # Save codex stdout in case the LaTeX is in there
        fallback = target_path.parent / "codex_output.txt"
        fallback.write_text(output or "", encoding="utf-8")
        print(f"[compose] codex output saved to {fallback}")
        return 5


if __name__ == "__main__":
    sys.exit(main())
