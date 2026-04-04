"""Codex agent mode for autoresearch.

Runs OpenAI Codex CLI as a full autonomous agent that searches the codebase,
writes Lean4 code, compiles, and fixes errors — all by itself.
"""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent


def run_codex_agent(target: dict) -> tuple[bool, str]:
    """Run Codex as a full agent: it searches, writes, compiles, fixes.

    Returns (success, output_text).
    """
    label = target.get("label", "")
    body = target.get("body", "")
    tex_file = target.get("tex_file", "")
    target_module = target.get("target_module", "")

    prompt = (
        f"You are formalizing a theorem from a math paper into Lean4.\n\n"
        f"Label: {label}\nSource: {tex_file}\nTarget module: lean4/{target_module}/\n\n"
        f"LaTeX (with proof if available):\n{body}\n\n"
        f"Instructions:\n"
        f"1. Read existing code in lean4/{target_module}/ to understand types and naming.\n"
        f"2. Search lean4/Omega/ for related definitions and lemmas.\n"
        f"3. Write the Lean4 formalization (statement + proof), append to appropriate .lean file.\n"
        f"4. Compile with: cd lean4 && timeout 300 lake build\n"
        f"5. If errors, fix and retry until it compiles.\n"
        f"6. Zero sorry/admit/axiom. No trivial statements like exists x, True.\n"
        f"7. Do NOT modify existing code, only append.\n\n"
        f"When done, print SUCCESS: <description> or FAILURE: <reason>"
    )

    try:
        result = subprocess.run(
            ["codex", "exec", prompt, "-C", str(REPO_ROOT), "--full-auto"],
            capture_output=True, text=True, timeout=600,
        )
        output = result.stdout.strip()

        # Check if codex actually modified .lean files (more reliable than parsing output)
        diff = subprocess.run(
            ["git", "diff", "--name-only"],
            cwd=str(REPO_ROOT), capture_output=True, text=True,
        )
        has_lean_changes = any(
            f.endswith(".lean") for f in diff.stdout.strip().split("\n") if f
        )
        untracked = subprocess.run(
            ["git", "ls-files", "--others", "--exclude-standard", "lean4/"],
            cwd=str(REPO_ROOT), capture_output=True, text=True,
        )
        has_new_files = any(
            f.endswith(".lean") for f in untracked.stdout.strip().split("\n") if f
        )

        success = (has_lean_changes or has_new_files) and "FAILURE:" not in output
        return success, output
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT: codex exceeded 10 minute limit"
    except Exception as e:
        return False, f"ERROR: {e}"
