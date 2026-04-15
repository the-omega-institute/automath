#!/usr/bin/env python3
"""Lean4 Codex-First formalization automation with git-worktree parallelism.

Architecture:
  - Base branch: lean4-codex-auto-dev (created from current HEAD if missing)
  - Each round runs in an isolated git worktree with its own branch
  - Multiple rounds execute in parallel via ThreadPoolExecutor
  - Successful rounds merge back to base branch, then push

Phases per round (each in its own worktree):
  Phase B: codex exec picks 3 formalization targets
  Gate:    validates target quality (count, difficulty, chapter diversity)
  Phase C: codex exec implements + compiles + commits + registers
  Phase D: verifies new commits, merges to base branch, pushes

Usage:
  python3 lean4/scripts/codex_formalize.py                          # 1 round, serial
  python3 lean4/scripts/codex_formalize.py --parallel 3             # 3 rounds in parallel
  python3 lean4/scripts/codex_formalize.py --parallel 3 --continuous  # continuous parallel
  python3 lean4/scripts/codex_formalize.py --dry-run --parallel 2   # preview only
  python3 lean4/scripts/codex_formalize.py --status                 # show state
  python3 lean4/scripts/codex_formalize.py --cleanup                # remove stale worktrees
"""

from __future__ import annotations

import argparse
import json
import logging
import os
import re
import shutil
import subprocess
import sys
import tempfile
import textwrap
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed, Future
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional

# ---------------------------------------------------------------------------
# Paths & constants
# ---------------------------------------------------------------------------

SCRIPT_DIR = Path(__file__).resolve().parent
LEAN_ROOT = SCRIPT_DIR.parent                        # lean4/
REPO_ROOT = LEAN_ROOT.parent                         # automath/
IMPL_PLAN = LEAN_ROOT / "IMPLEMENTATION_PLAN.md"
OMEGA_ROOT = LEAN_ROOT / "Omega"

LOG_DIR = LEAN_ROOT / "scripts" / "logs"
WORKTREE_DIR = REPO_ROOT / ".worktrees"

BASE_BRANCH = "lean4-codex-auto-dev"
CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"

# Thread-safe lock for git operations on the main repo
_git_lock = threading.Lock()
# Lock for round number allocation
_round_lock = threading.Lock()

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------

LOG_DIR.mkdir(parents=True, exist_ok=True)

_log_file = LOG_DIR / f"codex_formalize_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] [%(threadName)s] %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler(str(_log_file), encoding="utf-8"),
    ],
)
logger = logging.getLogger("codex-formalize")


# ---------------------------------------------------------------------------
# Data
# ---------------------------------------------------------------------------

@dataclass
class RoundState:
    round_number: int = 0
    coverage_pct: float = 0.0
    total_theorems: int = 0
    recent_commits: list[str] = field(default_factory=list)
    consecutive_failures: int = 0


@dataclass
class PhaseBResult:
    raw_output: str = ""
    targets: list[dict] = field(default_factory=list)
    success: bool = False


@dataclass
class PhaseCResult:
    raw_output: str = ""
    new_commits: list[str] = field(default_factory=list)
    success: bool = False


@dataclass
class WorktreeInfo:
    path: Path
    branch: str
    round_number: int


# ---------------------------------------------------------------------------
# Shell helpers
# ---------------------------------------------------------------------------

def run_cmd(
    cmd: list[str],
    *,
    cwd: Optional[Path] = None,
    timeout: int = 120,
    check: bool = False,
) -> subprocess.CompletedProcess:
    logger.debug(f"Running: {' '.join(cmd)}")
    return subprocess.run(
        cmd,
        cwd=str(cwd or REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=timeout,
        stdin=subprocess.DEVNULL,
        check=check,
    )


def git_log_oneline(n: int = 5, *, cwd: Optional[Path] = None) -> list[str]:
    result = run_cmd(["git", "log", "--oneline", f"-{n}"], cwd=cwd or REPO_ROOT)
    return [l.strip() for l in result.stdout.strip().splitlines() if l.strip()]


def read_impl_plan_header(lines: int = 30, *, repo: Optional[Path] = None) -> str:
    plan = (repo or REPO_ROOT) / "lean4" / "IMPLEMENTATION_PLAN.md"
    if not plan.exists():
        return "(IMPLEMENTATION_PLAN.md not found)"
    with open(plan, "r", encoding="utf-8") as f:
        return "".join(f.readline() for _ in range(lines))


def parse_round_from_plan(text: str) -> int:
    m = re.search(r"round_count\s*=\s*R?(\d+)", text)
    if m:
        return int(m.group(1))
    m = re.search(r"轮次\s*\|\s*R(\d+)", text)
    if m:
        return int(m.group(1))
    return 0


def count_lean_theorems(omega_root: Optional[Path] = None) -> int:
    root = omega_root or OMEGA_ROOT
    if not root.exists():
        return 0
    count = 0
    for path in root.rglob("*.lean"):
        text = path.read_text(encoding="utf-8", errors="replace")
        count += len(re.findall(r"^\s*(?:theorem|lemma)\s+", text, re.MULTILINE))
    return count


# ---------------------------------------------------------------------------
# Git worktree management
# ---------------------------------------------------------------------------

def ensure_base_branch() -> None:
    """Create BASE_BRANCH from current HEAD if it doesn't exist."""
    with _git_lock:
        result = run_cmd(["git", "branch", "--list", BASE_BRANCH], cwd=REPO_ROOT)
        if BASE_BRANCH not in result.stdout:
            logger.info(f"Creating base branch {BASE_BRANCH} from current HEAD")
            run_cmd(["git", "branch", BASE_BRANCH], cwd=REPO_ROOT, check=True)
            run_cmd(["git", "push", "-u", "origin", BASE_BRANCH], cwd=REPO_ROOT)
            logger.info(f"Base branch {BASE_BRANCH} created and pushed")
        else:
            logger.info(f"Base branch {BASE_BRANCH} exists")


def _clone_lake_cache(wt_path: Path) -> None:
    """Copy the .lake build cache into a new worktree using APFS clonefile.

    On macOS APFS, ``cp -Rc`` creates copy-on-write clones — near-instant and
    zero extra disk until files diverge.  Falls back to a regular copy on
    non-APFS volumes (slower but still correct).
    """
    src = LEAN_ROOT / ".lake"
    dst = wt_path / "lean4" / ".lake"
    if not src.exists():
        logger.info("No .lake cache to clone (main repo has none)")
        return
    if dst.exists():
        return  # already present (shouldn't happen for a fresh worktree)

    start = time.monotonic()
    # Try APFS clone first (macOS)
    result = run_cmd(
        ["cp", "-Rc", str(src), str(dst)],
        timeout=300,
    )
    if result.returncode != 0:
        # Fallback: regular copy
        logger.warning("APFS clone failed, falling back to regular copy")
        shutil.copytree(str(src), str(dst), symlinks=True)

    elapsed = time.monotonic() - start
    logger.info(f"Cloned .lake cache into worktree ({elapsed:.1f}s)")


def create_worktree(round_num: int) -> WorktreeInfo:
    """Create an isolated worktree for a round, with warm .lake cache."""
    WORKTREE_DIR.mkdir(parents=True, exist_ok=True)
    branch = f"codex-R{round_num}"
    wt_path = WORKTREE_DIR / f"round_R{round_num}"

    with _git_lock:
        # Clean up stale worktree at this path if it exists
        if wt_path.exists():
            logger.warning(f"Removing stale worktree at {wt_path}")
            run_cmd(["git", "worktree", "remove", "--force", str(wt_path)], cwd=REPO_ROOT)
            if wt_path.exists():
                shutil.rmtree(wt_path, ignore_errors=True)

        # Delete stale branch if it exists
        run_cmd(["git", "branch", "-D", branch], cwd=REPO_ROOT)

        # Create worktree from base branch
        logger.info(f"Creating worktree: {wt_path} on branch {branch}")
        result = run_cmd(
            ["git", "worktree", "add", "-b", branch, str(wt_path), BASE_BRANCH],
            cwd=REPO_ROOT,
        )
        if result.returncode != 0:
            raise RuntimeError(
                f"Failed to create worktree: {result.stderr.strip()}"
            )

    # Clone .lake cache outside the git lock (can run in parallel)
    _clone_lake_cache(wt_path)

    return WorktreeInfo(path=wt_path, branch=branch, round_number=round_num)


def remove_worktree(wt: WorktreeInfo) -> None:
    """Remove a worktree and its branch."""
    with _git_lock:
        logger.info(f"Removing worktree: {wt.path}")
        run_cmd(["git", "worktree", "remove", "--force", str(wt.path)], cwd=REPO_ROOT)
        if wt.path.exists():
            shutil.rmtree(wt.path, ignore_errors=True)
        # Delete the branch (already merged)
        run_cmd(["git", "branch", "-d", wt.branch], cwd=REPO_ROOT)


def _codex_resolve_conflicts(
    wt_path: Path,
    *,
    model: Optional[str] = None,
    timeout: int = 300,
) -> bool:
    """Use codex exec to resolve rebase conflicts in a worktree.

    Typical conflicts: parallel worktrees both appending imports to Omega.lean,
    both updating IMPLEMENTATION_PLAN.md header, or both adding \\leanverified
    annotations to .tex files.  These are additive/append conflicts that codex
    can resolve by keeping both sides' additions.
    """
    # List conflicted files
    status = run_cmd(["git", "diff", "--name-only", "--diff-filter=U"], cwd=wt_path)
    conflicted = [f.strip() for f in status.stdout.splitlines() if f.strip()]
    if not conflicted:
        return True  # no conflicts

    logger.info(f"Codex conflict resolution: {len(conflicted)} file(s): {conflicted}")

    prompt = textwrap.dedent(f"""\
        You are resolving git rebase conflicts in a Lean4 formalization project.

        The following files have merge conflicts (with <<<<<<< / ======= / >>>>>>> markers):
        {', '.join(conflicted)}

        ## Context
        Two parallel formalization rounds modified shared files:
        - lean4/Omega.lean: both rounds added `import` lines — keep ALL imports from both sides
        - lean4/IMPLEMENTATION_PLAN.md: both rounds updated the header — keep the incoming
          (HEAD/ours) version as base, then ADD the new round info from the other side
        - theory/*.tex: both rounds added \\leanverified annotations — keep ALL annotations

        ## Instructions
        1. For each conflicted file, read it and resolve the conflict markers
        2. The resolution strategy is ALWAYS "keep both sides' additions"
        3. For Omega.lean: merge all import lines (union, no duplicates)
        4. For IMPLEMENTATION_PLAN.md: keep both rounds' Phase entries
        5. For .tex files: keep all \\leanverified lines
        6. After resolving, run: git add <file> for each resolved file
        7. Then run: git rebase --continue
        8. Do NOT run git push

        Resolve ALL conflicts and complete the rebase.
    """)

    output = codex_exec(
        prompt,
        work_dir=wt_path,
        timeout_seconds=timeout,
    )

    # Check if rebase completed
    rebase_status = run_cmd(["git", "status", "--short"], cwd=wt_path)
    in_rebase = run_cmd(
        ["git", "rev-parse", "--git-path", "rebase-merge"], cwd=wt_path
    )
    rebase_dir = wt_path / ".git" if (wt_path / ".git").is_file() else wt_path / ".git"

    # Check if still in rebase state
    still_rebasing = run_cmd(
        ["git", "status"], cwd=wt_path
    )
    if "rebase in progress" in still_rebasing.stdout.lower():
        logger.warning("Codex did not complete rebase, aborting")
        run_cmd(["git", "rebase", "--abort"], cwd=wt_path)
        return False

    # Check for remaining conflicts
    remaining = run_cmd(["git", "diff", "--name-only", "--diff-filter=U"], cwd=wt_path)
    if remaining.stdout.strip():
        logger.warning(f"Codex left unresolved conflicts: {remaining.stdout.strip()}")
        run_cmd(["git", "rebase", "--abort"], cwd=wt_path)
        return False

    logger.info("Codex resolved all conflicts successfully")
    return True


def merge_worktree_to_base(wt: WorktreeInfo, *, model: Optional[str] = None) -> bool:
    """Merge the worktree branch into BASE_BRANCH and push.

    Strategy: rebase the worktree branch onto the latest BASE_BRANCH *inside
    the worktree itself*, then fast-forward the local BASE_BRANCH ref via
    ``git update-ref``.  This never checks out BASE_BRANCH in the main repo,
    so it works even when the main working tree is dirty.

    On rebase conflict, delegates to codex exec for automatic resolution
    (typical: parallel import additions to Omega.lean, IMPLEMENTATION_PLAN
    header updates, .tex annotation appends).
    """
    with _git_lock:
        logger.info(f"Merging {wt.branch} into {BASE_BRANCH}...")

        # 1. Fetch latest base branch
        run_cmd(["git", "fetch", "origin", BASE_BRANCH], cwd=REPO_ROOT)

        # 2. Rebase the worktree branch onto latest base (inside the worktree)
        rebase = run_cmd(
            ["git", "rebase", f"origin/{BASE_BRANCH}"],
            cwd=wt.path,
            timeout=120,
        )
        if rebase.returncode != 0:
            logger.warning(f"Rebase conflict for {wt.branch}, invoking codex to resolve...")
            resolved = _codex_resolve_conflicts(wt.path, model=model)
            if not resolved:
                logger.error(f"Codex could not resolve conflicts for {wt.branch}")
                run_cmd(["git", "rebase", "--abort"], cwd=wt.path)
                return False

        # 3. Fast-forward BASE_BRANCH ref to the rebased worktree tip
        wt_tip = run_cmd(
            ["git", "rev-parse", "HEAD"], cwd=wt.path
        ).stdout.strip()

        update = run_cmd(
            ["git", "update-ref", f"refs/heads/{BASE_BRANCH}", wt_tip],
            cwd=REPO_ROOT,
        )
        if update.returncode != 0:
            logger.error(f"update-ref failed: {update.stderr[:300]}")
            return False

        # Align main working tree index + files with the new HEAD so that
        # `git status` stays clean after the fast-forward.
        run_cmd(["git", "reset", "--hard", "HEAD"], cwd=REPO_ROOT)

        # 4. Push BASE_BRANCH
        push = run_cmd(
            ["git", "push", "origin", BASE_BRANCH],
            cwd=REPO_ROOT,
        )
        if push.returncode != 0:
            # Retry: fetch + rebase again (someone else pushed meanwhile)
            logger.warning("Push rejected, retrying after fetch + rebase...")
            run_cmd(["git", "fetch", "origin", BASE_BRANCH], cwd=REPO_ROOT)
            rebase2 = run_cmd(
                ["git", "rebase", f"origin/{BASE_BRANCH}"], cwd=wt.path,
                timeout=120,
            )
            if rebase2.returncode != 0:
                resolved2 = _codex_resolve_conflicts(wt.path, model=model)
                if not resolved2:
                    run_cmd(["git", "rebase", "--abort"], cwd=wt.path)
                    return False
            wt_tip2 = run_cmd(
                ["git", "rev-parse", "HEAD"], cwd=wt.path
            ).stdout.strip()
            run_cmd(
                ["git", "update-ref", f"refs/heads/{BASE_BRANCH}", wt_tip2],
                cwd=REPO_ROOT,
            )
            run_cmd(["git", "reset", "--hard", "HEAD"], cwd=REPO_ROOT)
            push2 = run_cmd(
                ["git", "push", "origin", BASE_BRANCH], cwd=REPO_ROOT,
            )
            if push2.returncode != 0:
                logger.error(f"Push retry failed: {push2.stderr[:300]}")
                return False

        logger.info(f"Merged and pushed {wt.branch} to {BASE_BRANCH}")
        return True


def cleanup_all_worktrees() -> int:
    """Remove all formalization worktrees."""
    if not WORKTREE_DIR.exists():
        return 0
    count = 0
    for entry in WORKTREE_DIR.iterdir():
        if entry.is_dir() and entry.name.startswith("round_R"):
            logger.info(f"Cleaning up {entry}")
            run_cmd(["git", "worktree", "remove", "--force", str(entry)], cwd=REPO_ROOT)
            if entry.exists():
                shutil.rmtree(entry, ignore_errors=True)
            # Try to delete branch
            m = re.match(r"round_R(\d+)", entry.name)
            if m:
                run_cmd(["git", "branch", "-D", f"codex-R{m.group(1)}"], cwd=REPO_ROOT)
            count += 1
    # Prune worktree list
    run_cmd(["git", "worktree", "prune"], cwd=REPO_ROOT)
    return count


# ---------------------------------------------------------------------------
# Codex CLI invocation
# ---------------------------------------------------------------------------

def codex_exec(
    prompt: str,
    *,
    work_dir: Optional[Path] = None,
    timeout_seconds: int = 1800,
    output_file: Optional[Path] = None,
    model: Optional[str] = None,
    dry_run: bool = False,
) -> str:
    """Call `codex exec` with the given prompt, targeting work_dir."""
    if dry_run:
        logger.info(f"[DRY RUN] codex exec (cwd={work_dir}):\n"
                     f"{prompt[:400]}{'...' if len(prompt) > 400 else ''}")
        return "(dry run -- no output)"

    codex_bin = CODEX_PATH if Path(CODEX_PATH).exists() else shutil.which("codex")
    if not codex_bin:
        raise FileNotFoundError("Codex CLI not found")

    target_dir = str(work_dir or REPO_ROOT)

    # Write prompt to temp file
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".txt", prefix="codex_prompt_",
        delete=False, encoding="utf-8",
    ) as f:
        f.write(prompt)
        prompt_file = f.name

    out_file = str(output_file) if output_file else None
    if out_file is None:
        out_fd, out_file = tempfile.mkstemp(suffix=".txt", prefix="codex_out_")
        os.close(out_fd)

    cmd = [
        "timeout", str(timeout_seconds),
        codex_bin, "exec",
        "--dangerously-bypass-approvals-and-sandbox",
        "-C", target_dir,
        "-o", out_file,
    ]
    if model:
        cmd.extend(["-m", model])
    cmd.append("-")

    logger.info(f"Calling codex exec (cwd={target_dir}, timeout={timeout_seconds}s)...")
    start = time.monotonic()
    result = None

    try:
        with open(prompt_file, "r", encoding="utf-8") as pf:
            result = subprocess.run(
                cmd, stdin=pf, capture_output=True, text=True,
                timeout=timeout_seconds + 30, cwd=target_dir,
            )
    except subprocess.TimeoutExpired:
        logger.warning(f"Codex exec timed out after {timeout_seconds}s")
        return "(timeout)"
    finally:
        elapsed = time.monotonic() - start
        rc = result.returncode if result else "?"
        logger.info(f"Codex exec completed in {elapsed:.1f}s (rc={rc})")
        os.unlink(prompt_file)

    # Read output
    output = ""
    try:
        if os.path.exists(out_file) and os.path.getsize(out_file) > 0:
            with open(out_file, "r", encoding="utf-8") as f:
                output = f.read()
        else:
            output = result.stdout or ""
    finally:
        if output_file is None:
            os.unlink(out_file)

    return output


# ---------------------------------------------------------------------------
# Phase B: Target Selection
# ---------------------------------------------------------------------------

def build_phase_b_prompt(round_num: int, total_theorems: int, recent: str) -> str:
    return textwrap.dedent(f"""\
        You are the target-selection phase for Lean4 formalization round R{round_num}.

        ## Project Layout
        - lean4/Omega/ — Lean4 code (Omega library, depends on mathlib)
        - theory/ — papers in LaTeX
        - lean4/IMPLEMENTATION_PLAN.md — tracking file
        - Current round: R{round_num}
        - Current theorem count: ~{total_theorems}
        - Recent commits:
        {recent}

        ## Task
        Select 3 formalization targets for R{round_num}.

        Steps:
        1. Read lean4/IMPLEMENTATION_PLAN.md (first 120 lines) to identify the latest phase
           and queued candidates.
        2. Scan theory/ to find theorem environments without \\leanverified.
        3. grep lean4/Omega/ to confirm these theorems are NOT already implemented.
        4. Pick 3 targets:
           - At least 1 must be medium difficulty (induction/construction, >=15 lines)
           - Not all from the same chapter
           - Prioritize different chapters for diversity

        ## Output Format (MUST follow exactly)
        Output a single JSON block:

        ```json
        {{
          "targets": [
            {{
              "paper_label": "thm:xxx or prop:xxx or cor:xxx",
              "lean_name": "paper_xxx_yyy",
              "lean_signature": "theorem paper_xxx_yyy : ... := by sorry",
              "target_file": "lean4/Omega/Module/File.lean",
              "strategy": "Brief proof strategy",
              "difficulty": "low/medium/high",
              "chapter": "Folding/SPG/Zeta/etc",
              "grep_confirmed_missing": true
            }}
          ]
        }}
        ```

        You MUST grep to confirm each target does not already exist.
        Do NOT guess mathlib API names.
    """)


def parse_phase_b_output(raw: str) -> PhaseBResult:
    result = PhaseBResult(raw_output=raw)

    # Try fenced JSON block
    json_match = re.search(r"```json\s*(\{.*?\})\s*```", raw, re.DOTALL)
    if json_match:
        try:
            data = json.loads(json_match.group(1))
            result.targets = data.get("targets", [])
        except json.JSONDecodeError:
            pass

    # Fallback: bare JSON
    if not result.targets:
        for m in re.finditer(r'\{[^{}]*"targets"\s*:\s*\[.*?\]\s*\}', raw, re.DOTALL):
            try:
                data = json.loads(m.group(0))
                result.targets = data.get("targets", [])
                if result.targets:
                    break
            except json.JSONDecodeError:
                continue

    result.success = len(result.targets) >= 1
    return result


def gate_check(targets: list[dict]) -> tuple[bool, str]:
    if len(targets) < 1:
        return False, "No targets found"
    difficulties = [t.get("difficulty", "low") for t in targets]
    chapters = set(t.get("chapter", "unknown") for t in targets)
    issues = []
    if len(targets) < 3:
        issues.append(f"Only {len(targets)} targets (want 3)")
    if not any(d in ("medium", "high") for d in difficulties):
        issues.append("No medium/high difficulty target")
    if len(targets) >= 3 and len(chapters) <= 1:
        issues.append(f"All targets from same chapter: {chapters}")
    if issues:
        return False, "; ".join(issues)
    return True, "Gate passed"


# ---------------------------------------------------------------------------
# Phase C: Implementation (runs inside worktree)
# ---------------------------------------------------------------------------

def build_phase_c_prompt(round_num: int, targets: list[dict]) -> str:
    targets_text = ""
    for i, t in enumerate(targets, 1):
        targets_text += textwrap.dedent(f"""\
            ### Target {i}
            - Paper label: {t.get('paper_label', 'unknown')}
            - Lean name: {t.get('lean_name', 'unknown')}
            - File: {t.get('target_file', 'unknown')}
            - Strategy: {t.get('strategy', 'unknown')}
            - Difficulty: {t.get('difficulty', 'unknown')}
            - Lean signature:
            ```lean
            {t.get('lean_signature', '-- unknown')}
            ```

        """)

    return textwrap.dedent(f"""\
        Implement Lean4 theorems + compile + commit (do NOT push). Complete in one pass.

        ## Round R{round_num}

        ## Targets to Implement
        {targets_text}

        ## Step 1: Implement proofs
        For each target:
        1. Create or edit the target file in lean4/Omega/
        2. Write the theorem with a complete proof (NO sorry, NO admit, NO axiom)
        3. Use lean_goal / lean_local_search / lean_multi_attempt / lean_diagnostic_messages
           if available via MCP
        4. If a type doesn't exist, create a minimal seed definition
        5. native_decide ONLY for base cases (m<=2) or pure arithmetic (3+5=8)
        6. Do NOT use maxHeartbeats > 400000

        ## Step 2: Full compilation
        ```bash
        cd lean4 && timeout 300 lake build
        ```
        If errors, fix them (up to 3 attempts per theorem).
        If a theorem is stuck, skip it and continue with the others.

        ## Step 3: Git commit the proofs
        ```bash
        git add lean4/Omega/ lean4/Omega.lean
        git commit -m "R{round_num}: [brief description of what was proved]

        Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>"
        ```

        ## Step 4: Update tracking + annotate
        - Update lean4/IMPLEMENTATION_PLAN.md with new round info
        - Add \\leanverified{{theorem_name}} to the corresponding .tex files
          (find them via the paper_label, escape underscores as \\_)

        ## Step 5: Git commit registration
        ```bash
        git add lean4/IMPLEMENTATION_PLAN.md theory/
        git commit -m "Register R{round_num}: [brief description]

        Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>"
        ```

        ## IMPORTANT: Do NOT git push. The merge and push will be handled externally.

        ## Completion Contract
        - No sorry / admit / axiom; lake build must pass with zero errors
        - Must complete all 5 steps; if a theorem is stuck, skip it and continue
        - Tactic failure: auto-try next; compile error: auto-fix up to 3 rounds
        - Implementation changes: only in lean4/Omega/
        - Registration changes: only in IMPLEMENTATION_PLAN.md and theory/
        - Do NOT refactor or delete existing code
        - Do NOT git push
    """)


def parse_phase_c_output(raw: str) -> PhaseCResult:
    result = PhaseCResult(raw_output=raw)
    commit_hashes = re.findall(r"[0-9a-f]{7,40}", raw)
    result.new_commits = list(dict.fromkeys(
        h for h in commit_hashes if 7 <= len(h) <= 12
    ))[:10]
    success_indicators = ["lake build", "commit", f"Register R"]
    result.success = any(ind.lower() in raw.lower() for ind in success_indicators)
    return result


# ---------------------------------------------------------------------------
# Worktree-based round execution
# ---------------------------------------------------------------------------

def verify_worktree_commits(wt: WorktreeInfo, pre_commits: list[str]) -> tuple[bool, list[str]]:
    """Check for new commits in the worktree."""
    post = git_log_oneline(10, cwd=wt.path)
    new = [c for c in post if c not in pre_commits]
    if new:
        logger.info(f"[R{wt.round_number}] Phase D: {len(new)} new commit(s):")
        for c in new:
            logger.info(f"  {c}")
        return True, new
    logger.warning(f"[R{wt.round_number}] Phase D: No new commits")
    return False, []


def run_round_in_worktree(
    round_num: int,
    total_theorems: int,
    recent_commits: list[str],
    *,
    dry_run: bool = False,
    model: Optional[str] = None,
    phase_b_timeout: int = 1800,
    phase_c_timeout: int = 3600,
) -> tuple[bool, int, list[str]]:
    """
    Execute one formalization round inside an isolated git worktree.
    Returns (success, round_number, new_commit_lines).
    """
    tag = f"R{round_num}"
    logger.info(f"{'='*60}")
    logger.info(f"[{tag}] Starting round (worktree mode, {total_theorems} theorems)")
    logger.info(f"{'='*60}")

    wt: Optional[WorktreeInfo] = None
    try:
        # ── Create worktree ───────────────────────────────────────
        if not dry_run:
            wt = create_worktree(round_num)
            wt_cwd = wt.path
        else:
            wt_cwd = REPO_ROOT

        pre_commits = git_log_oneline(10, cwd=wt_cwd)
        recent_text = "\n".join(recent_commits[:5]) if recent_commits else "(none)"

        # ── Phase B ───────────────────────────────────────────────
        logger.info(f"[{tag}] Phase B: Target selection...")
        phase_b_prompt = build_phase_b_prompt(round_num, total_theorems, recent_text)
        phase_b_raw = codex_exec(
            phase_b_prompt,
            work_dir=wt_cwd,
            timeout_seconds=phase_b_timeout,
            model=model,
            dry_run=dry_run,
        )
        phase_b = parse_phase_b_output(phase_b_raw)

        if not phase_b.success:
            logger.error(f"[{tag}] Phase B failed: no targets extracted "
                         f"({len(phase_b.raw_output)} chars)")
            _save_round_log(round_num, phase_b, PhaseCResult(), [], False)
            return False, round_num, []

        logger.info(f"[{tag}] Phase B: {len(phase_b.targets)} target(s) extracted")
        for i, t in enumerate(phase_b.targets, 1):
            logger.info(f"  Target {i}: {t.get('lean_name', '?')} "
                         f"({t.get('difficulty', '?')}, {t.get('chapter', '?')})")

        # ── Gate ──────────────────────────────────────────────────
        gate_ok, gate_msg = gate_check(phase_b.targets)
        if not gate_ok:
            logger.warning(f"[{tag}] Gate: {gate_msg} (proceeding anyway)")
        else:
            logger.info(f"[{tag}] Gate: {gate_msg}")

        # ── Phase C ───────────────────────────────────────────────
        logger.info(f"[{tag}] Phase C: Implementation (in worktree)...")
        phase_c_prompt = build_phase_c_prompt(round_num, phase_b.targets)
        phase_c_raw = codex_exec(
            phase_c_prompt,
            work_dir=wt_cwd,
            timeout_seconds=phase_c_timeout,
            model=model,
            dry_run=dry_run,
        )
        phase_c = parse_phase_c_output(phase_c_raw)

        # ── Phase D: Verify ───────────────────────────────────────
        logger.info(f"[{tag}] Phase D: Verification...")
        if dry_run:
            new_commits: list[str] = []
            success = True
        else:
            assert wt is not None
            success, new_commits = verify_worktree_commits(wt, pre_commits)

        # ── Merge back ────────────────────────────────────────────
        if success and new_commits and wt and not dry_run:
            logger.info(f"[{tag}] Merging to {BASE_BRANCH}...")
            merged = merge_worktree_to_base(wt, model=model)
            if not merged:
                logger.error(f"[{tag}] Merge failed — keeping worktree for manual resolution")
                _save_round_log(round_num, phase_b, phase_c, new_commits, False)
                return False, round_num, new_commits
            logger.info(f"[{tag}] SUCCESS: merged {len(new_commits)} commit(s) to {BASE_BRANCH}")
        elif success and dry_run:
            logger.info(f"[{tag}] [DRY RUN] Would merge to {BASE_BRANCH}")

        _save_round_log(round_num, phase_b, phase_c, new_commits, success)

        if success and new_commits:
            logger.info(f"[{tag}] Round SUCCESS: {len(new_commits)} commit(s)")
        else:
            logger.warning(f"[{tag}] Round FAILED")

        return success and bool(new_commits or dry_run), round_num, new_commits

    except Exception as exc:
        logger.error(f"[{tag}] Exception: {exc}", exc_info=True)
        return False, round_num, []

    finally:
        # Cleanup worktree on success or non-merge-conflict failure
        if wt and not dry_run:
            try:
                # Only remove if we successfully merged or had no commits
                if not new_commits or (success and new_commits):
                    remove_worktree(wt)
            except Exception:
                logger.warning(f"[{tag}] Failed to clean up worktree {wt.path}")


# ---------------------------------------------------------------------------
# State & logging persistence
# ---------------------------------------------------------------------------

STATE_FILE = LOG_DIR / "formalize_state.json"


def load_state() -> RoundState:
    if STATE_FILE.exists():
        try:
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            return RoundState(**data)
        except Exception:
            logger.warning("Failed to load state, rebuilding from IMPLEMENTATION_PLAN")
    plan_text = read_impl_plan_header(30)
    return RoundState(
        round_number=parse_round_from_plan(plan_text),
        total_theorems=count_lean_theorems(),
        recent_commits=git_log_oneline(5),
    )


def save_state(state: RoundState) -> None:
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump({
            "round_number": state.round_number,
            "coverage_pct": state.coverage_pct,
            "total_theorems": state.total_theorems,
            "recent_commits": state.recent_commits[:10],
            "consecutive_failures": state.consecutive_failures,
        }, f, indent=2)


def _save_round_log(
    round_num: int,
    phase_b: PhaseBResult,
    phase_c: PhaseCResult,
    new_commits: list[str],
    success: bool,
) -> Path:
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_path = LOG_DIR / f"round_R{round_num}_{ts}.json"
    with open(log_path, "w", encoding="utf-8") as f:
        json.dump({
            "round": round_num,
            "timestamp": ts,
            "success": success,
            "targets": phase_b.targets,
            "phase_b_success": phase_b.success,
            "phase_c_success": phase_c.success,
            "new_commits": new_commits,
            "phase_b_output_length": len(phase_b.raw_output),
            "phase_c_output_length": len(phase_c.raw_output),
        }, f, indent=2, ensure_ascii=False)
    return log_path


# ---------------------------------------------------------------------------
# Parallel dispatcher
# ---------------------------------------------------------------------------

def allocate_round_numbers(state: RoundState, count: int) -> list[int]:
    """Thread-safe allocation of consecutive round numbers."""
    with _round_lock:
        base = state.round_number + 1
        nums = list(range(base, base + count))
        state.round_number = base + count - 1  # reserve them
        save_state(state)
        return nums


def run_parallel_batch(
    state: RoundState,
    *,
    parallel: int,
    dry_run: bool = False,
    model: Optional[str] = None,
    phase_b_timeout: int = 1800,
    phase_c_timeout: int = 3600,
) -> tuple[int, int]:
    """
    Dispatch `parallel` rounds concurrently using worktrees.
    Returns (succeeded_count, failed_count).
    """
    round_nums = allocate_round_numbers(state, parallel)
    total_theorems = state.total_theorems
    recent = state.recent_commits

    logger.info(f"Dispatching parallel batch: R{round_nums[0]}..R{round_nums[-1]} "
                f"({parallel} workers)")

    succeeded = 0
    failed = 0

    with ThreadPoolExecutor(max_workers=parallel, thread_name_prefix="worker") as pool:
        futures: dict[Future, int] = {}
        for rn in round_nums:
            fut = pool.submit(
                run_round_in_worktree,
                rn, total_theorems, recent,
                dry_run=dry_run,
                model=model,
                phase_b_timeout=phase_b_timeout,
                phase_c_timeout=phase_c_timeout,
            )
            futures[fut] = rn

        for fut in as_completed(futures):
            rn = futures[fut]
            try:
                ok, _, commits = fut.result()
                if ok:
                    succeeded += 1
                    logger.info(f"[R{rn}] Batch result: SUCCESS ({len(commits)} commits)")
                else:
                    failed += 1
                    logger.warning(f"[R{rn}] Batch result: FAILED")
            except Exception as exc:
                failed += 1
                logger.error(f"[R{rn}] Batch result: EXCEPTION: {exc}")

    # Update state after batch
    state.total_theorems = count_lean_theorems()
    state.recent_commits = git_log_oneline(5)
    if failed == parallel:
        state.consecutive_failures += 1
    else:
        state.consecutive_failures = 0
    save_state(state)

    return succeeded, failed


# ---------------------------------------------------------------------------
# Serial fallback (single-threaded, no worktree — backward compatible)
# ---------------------------------------------------------------------------

def run_round_serial(
    state: RoundState,
    *,
    dry_run: bool = False,
    model: Optional[str] = None,
    phase_b_timeout: int = 1800,
    phase_c_timeout: int = 3600,
) -> bool:
    """Single-round execution using worktree (parallel=1)."""
    s, f = run_parallel_batch(
        state,
        parallel=1,
        dry_run=dry_run,
        model=model,
        phase_b_timeout=phase_b_timeout,
        phase_c_timeout=phase_c_timeout,
    )
    return s > 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> int:
    global BASE_BRANCH

    parser = argparse.ArgumentParser(
        description="Lean4 Codex-First formalization with worktree parallelism",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
            Examples:
              python3 lean4/scripts/codex_formalize.py                          # 1 round
              python3 lean4/scripts/codex_formalize.py --parallel 3             # 3 parallel
              python3 lean4/scripts/codex_formalize.py --parallel 3 --continuous  # continuous
              python3 lean4/scripts/codex_formalize.py --dry-run --parallel 2   # preview
              python3 lean4/scripts/codex_formalize.py --status                 # state
              python3 lean4/scripts/codex_formalize.py --cleanup                # remove worktrees
        """),
    )
    parser.add_argument(
        "--rounds", "-n", type=int, default=1,
        help="Number of batch iterations (default: 1)",
    )
    parser.add_argument(
        "--parallel", "-p", type=int, default=1,
        help="Number of parallel workers per batch (default: 1 = serial)",
    )
    parser.add_argument(
        "--continuous", action="store_true",
        help="Run continuously until stopped or max consecutive failures",
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument(
        "--model", "-m", type=str, default=None,
        help="Model override for codex exec",
    )
    parser.add_argument("--phase-b-timeout", type=int, default=1800)
    parser.add_argument("--phase-c-timeout", type=int, default=3600)
    parser.add_argument(
        "--max-consecutive-failures", type=int, default=3,
        help="Stop after N consecutive all-fail batches (default: 3)",
    )
    parser.add_argument("--reset-state", action="store_true")
    parser.add_argument("--status", action="store_true")
    parser.add_argument(
        "--cleanup", action="store_true",
        help="Remove all stale formalization worktrees and exit",
    )
    parser.add_argument(
        "--base-branch", type=str, default=BASE_BRANCH,
        help=f"Base branch name (default: {BASE_BRANCH})",
    )
    args = parser.parse_args()

    BASE_BRANCH = args.base_branch

    # ── Cleanup ────────────────────────────────────────────────────
    if args.cleanup:
        n = cleanup_all_worktrees()
        print(f"Cleaned up {n} worktree(s)")
        return 0

    # ── Status ─────────────────────────────────────────────────────
    if args.status:
        state = load_state()
        # List active worktrees
        wt_result = run_cmd(["git", "worktree", "list"], cwd=REPO_ROOT)
        active_wts = [
            l for l in wt_result.stdout.splitlines()
            if "round_R" in l
        ]
        print(f"Round:                 R{state.round_number}")
        print(f"Total theorems:        ~{state.total_theorems}")
        print(f"Consecutive failures:  {state.consecutive_failures}")
        print(f"Base branch:           {BASE_BRANCH}")
        print(f"Active worktrees:      {len(active_wts)}")
        for wt in active_wts:
            print(f"  {wt.strip()}")
        print(f"Recent commits:")
        for c in state.recent_commits[:5]:
            print(f"  {c}")
        print(f"Codex CLI:             {CODEX_PATH}")
        print(f"Log dir:               {LOG_DIR}")
        return 0

    # ── Reset ──────────────────────────────────────────────────────
    if args.reset_state and STATE_FILE.exists():
        STATE_FILE.unlink()
        logger.info("State reset")

    # ── Preflight ──────────────────────────────────────────────────
    codex_bin = CODEX_PATH if Path(CODEX_PATH).exists() else shutil.which("codex")
    if not codex_bin and not args.dry_run:
        logger.error("Codex CLI not found")
        return 1
    logger.info(f"Codex CLI: {codex_bin}")
    logger.info(f"Base branch: {BASE_BRANCH}")
    logger.info(f"Parallelism: {args.parallel}")

    # Ensure base branch
    if not args.dry_run:
        ensure_base_branch()

    state = load_state()
    logger.info(f"Starting: R{state.round_number}, ~{state.total_theorems} theorems")

    # ── Run ────────────────────────────────────────────────────────
    max_batches = 999999 if args.continuous else args.rounds
    total_succeeded = 0
    total_failed = 0

    for batch_idx in range(max_batches):
        if state.consecutive_failures >= args.max_consecutive_failures:
            logger.error(
                f"Stopping: {state.consecutive_failures} consecutive all-fail batches "
                f"(limit: {args.max_consecutive_failures})"
            )
            break

        logger.info(f"{'='*60}")
        logger.info(f"Batch {batch_idx + 1}: dispatching {args.parallel} worker(s)")
        logger.info(f"{'='*60}")

        s, f = run_parallel_batch(
            state,
            parallel=args.parallel,
            dry_run=args.dry_run,
            model=args.model,
            phase_b_timeout=args.phase_b_timeout,
            phase_c_timeout=args.phase_c_timeout,
        )
        total_succeeded += s
        total_failed += f

        logger.info(f"Batch {batch_idx + 1} done: {s} succeeded, {f} failed")

        if batch_idx < max_batches - 1 and not args.dry_run:
            logger.info("Waiting 5s before next batch...")
            time.sleep(5)

    # ── Summary ────────────────────────────────────────────────────
    logger.info(f"{'='*60}")
    logger.info(f"Session complete: {total_succeeded} succeeded, {total_failed} failed")
    logger.info(f"Final: R{state.round_number}, ~{state.total_theorems} theorems")
    logger.info(f"{'='*60}")

    return 0 if total_succeeded > 0 or args.dry_run else 1


if __name__ == "__main__":
    raise SystemExit(main())
