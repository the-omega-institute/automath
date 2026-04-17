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
from concurrent.futures import ThreadPoolExecutor, as_completed, wait, FIRST_COMPLETED, Future
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
PROMPTS_DIR = SCRIPT_DIR / "prompts"

LOG_DIR = LEAN_ROOT / "scripts" / "logs"
WORKTREE_DIR = REPO_ROOT / ".worktrees"

BASE_BRANCH = "lean4-codex-auto-dev"
CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"
# Graceful stop: create this file to prevent new rounds from being dispatched.
# Current rounds finish normally; the process exits once the pool drains.
STOP_FILE = REPO_ROOT / ".pipeline.stop"


def _load_prompt(name: str) -> str:
    """Load a prompt template from lean4/scripts/prompts/<name>.txt.

    Templates use <PLACEHOLDER> syntax; callers substitute values with .replace().
    Editing prompts only requires changing the .txt files, not this script.
    """
    return (PROMPTS_DIR / f"{name}.txt").read_text(encoding="utf-8")

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


# ---------------------------------------------------------------------------
# Memory-pressure guard (macOS)
#
# Motivation: parallel `codex exec` + `lake build` can saturate the unified
# memory on M-series Macs. If WindowServer is starved for >168s the kernel
# watchdog panics (AppleARMWatchdogTimer → userspace watchdog timeout). We
# gate each worker dispatch on macOS memory-pressure indicators so the
# pipeline backs off before the system does.
# ---------------------------------------------------------------------------

# kern.memorystatus_vm_pressure_level mapping (XNU):
#   1 = NORMAL, 2 = WARN, 4 = URGENT, 8 = CRITICAL
_MEM_LEVEL_BY_NAME = {"normal": 1, "warn": 2, "urgent": 4, "critical": 8}

# Populated by main() from CLI flags.
_MEM_GUARD_CFG: dict = {
    "enabled": sys.platform == "darwin",
    "level_threshold": 2,      # block when kern.memorystatus_vm_pressure_level >= this
    "swap_ceiling_gb": 16.0,   # block when used swap exceeds this
    "poll_seconds": 30,
    "max_wait_seconds": 1800,
}
_mem_guard_lock = threading.Lock()  # serialize waits so we don't spam logs


def _macos_pressure_level() -> int:
    if sys.platform != "darwin":
        return 0
    try:
        r = subprocess.run(
            ["sysctl", "-n", "kern.memorystatus_vm_pressure_level"],
            capture_output=True, text=True, timeout=5,
            stdin=subprocess.DEVNULL,
        )
        return int((r.stdout or "0").strip() or "0")
    except Exception:
        return 0


_SWAP_RE = re.compile(r"used\s*=\s*([\d.]+)([MG])", re.IGNORECASE)


def _macos_swap_used_gb() -> float:
    if sys.platform != "darwin":
        return 0.0
    try:
        r = subprocess.run(
            ["sysctl", "-n", "vm.swapusage"],
            capture_output=True, text=True, timeout=5,
            stdin=subprocess.DEVNULL,
        )
        m = _SWAP_RE.search(r.stdout or "")
        if not m:
            return 0.0
        val = float(m.group(1))
        return val / 1024.0 if m.group(2).upper() == "M" else val
    except Exception:
        return 0.0


def memory_pressure_snapshot() -> tuple[int, float]:
    """Return (pressure_level, swap_used_gb). level=0 if unsupported."""
    return _macos_pressure_level(), _macos_swap_used_gb()


def memory_pressure_wait(context: str = "") -> bool:
    """Block until macOS memory pressure is below the configured threshold.

    Returns True if pressure is OK (or guard is disabled / unsupported).
    Returns False if max_wait timed out — caller should proceed with a warning
    rather than deadlock the pipeline.
    """
    cfg = _MEM_GUARD_CFG
    if not cfg["enabled"]:
        return True

    lvl_thresh = int(cfg["level_threshold"])
    swap_cap = float(cfg["swap_ceiling_gb"])
    poll = int(cfg["poll_seconds"])
    max_wait = int(cfg["max_wait_seconds"])

    # Fast path: no pressure, no waiting.
    lvl, swap = memory_pressure_snapshot()
    if (lvl == 0 or lvl < lvl_thresh) and swap < swap_cap:
        return True

    # Serialize the wait so parallel callers don't spam identical log lines.
    with _mem_guard_lock:
        start = time.time()
        warned = False
        while True:
            lvl, swap = memory_pressure_snapshot()
            under_level = lvl == 0 or lvl < lvl_thresh
            under_swap = swap < swap_cap
            if under_level and under_swap:
                if warned:
                    logger.info(
                        f"[mem-guard] pressure cleared (level={lvl}, swap={swap:.1f}GB)"
                        + (f" — resuming {context}" if context else "")
                    )
                return True
            elapsed = int(time.time() - start)
            if elapsed >= max_wait:
                logger.warning(
                    f"[mem-guard] timeout after {elapsed}s "
                    f"(level={lvl}, swap={swap:.1f}GB) — proceeding anyway"
                    + (f" with {context}" if context else "")
                )
                return False
            logger.warning(
                f"[mem-guard] pressure elevated (level={lvl}, swap={swap:.1f}GB) — "
                f"pausing {context or 'dispatch'}, retry in {poll}s (waited {elapsed}s)"
            )
            warned = True
            time.sleep(poll)


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
    """Set up the .lake directory in a new worktree.

    Strategy:
    - ``packages/`` is symlinked to the main repo's copy.  External deps never
      change between rounds, so sharing them is safe.  More importantly, lake
      resolves artifact paths from ``Omega.setup.json`` which embeds absolute
      paths like ``/…/lean4/.lake/packages/…``; those paths remain valid when
      packages live at the *same* location as in the main repo.  A full copy
      causes lake to regenerate ``Omega.setup.json`` with the new worktree
      paths, invalidating all cached .olean references and forcing a full
      rebuild (~30-60 min per round instead of ~5 min).
    - ``build/`` (Omega's compiled artifacts) is APFS-cloned (copy-on-write)
      so each worktree starts with the full incremental cache and lake only
      recompiles the 2-3 new files added in the round.
    - ``config/`` is APFS-cloned as well (small, round-specific lake config).
    """
    src = LEAN_ROOT / ".lake"
    dst = wt_path / "lean4" / ".lake"
    if not src.exists():
        logger.info("No .lake cache to clone (main repo has none)")
        return
    if dst.exists():
        return  # already present (shouldn't happen for a fresh worktree)

    start = time.monotonic()
    dst.mkdir(parents=True, exist_ok=True)

    # 1. Symlink packages/ → main repo's packages (preserves absolute paths in
    #    Omega.setup.json, prevents lake from invalidating the .olean cache).
    src_pkg = src / "packages"
    if src_pkg.exists():
        (dst / "packages").symlink_to(src_pkg)

    # 2. APFS-clone build/ and config/ (round-local, writable copies).
    for sub in ("build", "config"):
        src_sub = src / sub
        dst_sub = dst / sub
        if not src_sub.exists():
            continue
        result = run_cmd(["cp", "-Rc", str(src_sub), str(dst_sub)], timeout=600)
        if result.returncode != 0:
            logger.warning(f"APFS clone of .lake/{sub} failed, retrying...")
            if dst_sub.exists():
                shutil.rmtree(dst_sub, ignore_errors=True)
            time.sleep(2)
            result = run_cmd(["cp", "-Rc", str(src_sub), str(dst_sub)], timeout=600)
        if result.returncode != 0:
            logger.warning(f"APFS clone retry failed for .lake/{sub}, falling back to regular copy")
            if dst_sub.exists():
                shutil.rmtree(dst_sub, ignore_errors=True)
            shutil.copytree(str(src_sub), str(dst_sub), symlinks=True)

    elapsed = time.monotonic() - start
    logger.info(f"Set up .lake in worktree ({elapsed:.1f}s): "
                f"packages=symlink, build/config=COW-clone")


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
            # Remove symlinks first (shutil.rmtree doesn't follow them, but the
            # packages/ symlink target must not be deleted — only the link itself).
            lake_dir = wt.path / "lean4" / ".lake"
            pkg_link = lake_dir / "packages"
            if pkg_link.is_symlink():
                pkg_link.unlink()
            shutil.rmtree(wt.path, ignore_errors=True)
        # Use -D (force-delete) so unmerged branches are cleaned up too.
        run_cmd(["git", "branch", "-D", wt.branch], cwd=REPO_ROOT)


def _codex_resolve_conflicts(
    wt_path: Path,
    *,
    model: Optional[str] = None,
    timeout: int = 1200,
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

    # Check if still in rebase state
    still_rebasing = run_cmd(["git", "status"], cwd=wt_path)
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

    Strategy:
    1. Fetch origin so we have the latest remote state.
    2. Fast-forward LOCAL BASE_BRANCH from origin (if origin is ahead).
       Uses ``git fetch . origin/BASE:BASE`` which is ff-only and safe —
       it never overwrites local-only commits that haven't been pushed yet.
    3. Rebase the worktree branch onto the LOCAL BASE_BRANCH (not origin/).
       This ensures any local-only commits (e.g. prompt/script edits made
       directly on the branch without pushing first) are included in the
       rebase base and are not lost.
    4. Fast-forward LOCAL BASE_BRANCH to the rebased worktree tip via
       ``git fetch . wt_tip:BASE_BRANCH`` (ff-only, never force-moves the
       ref past local-only commits, never touches the working tree).
    5. Push to origin.

    The old ``git update-ref + git reset --hard HEAD`` pattern was unsafe:
    it unconditionally moved the branch pointer to the worktree tip (which
    was rebased on origin/, not on local commits) and then discarded any
    local-only working-tree changes.
    """
    with _git_lock:
        logger.info(f"Merging {wt.branch} into {BASE_BRANCH}...")

        def _do_rebase_and_ff(attempt: int) -> bool:
            # 1. Fetch latest remote state
            run_cmd(["git", "fetch", "origin", BASE_BRANCH], cwd=REPO_ROOT, timeout=300)

            # 2. Fast-forward local BASE_BRANCH from origin if origin is ahead.
            #    git merge --ff-only works on a checked-out branch (unlike git fetch .).
            #    Silently no-ops if local is already at or ahead of origin.
            run_cmd(
                ["git", "merge", "--ff-only", f"origin/{BASE_BRANCH}"],
                cwd=REPO_ROOT, timeout=30,
            )

            # 3. Rebase worktree onto LOCAL BASE_BRANCH (includes local-only commits)
            rebase = run_cmd(
                ["git", "rebase", BASE_BRANCH],
                cwd=wt.path,
                timeout=180,
            )
            if rebase.returncode != 0:
                logger.warning(
                    f"Rebase conflict for {wt.branch} (attempt {attempt}), "
                    "invoking codex to resolve..."
                )
                resolved = _codex_resolve_conflicts(wt.path, model=model)
                if not resolved:
                    logger.error(f"Codex could not resolve conflicts for {wt.branch}")
                    run_cmd(["git", "rebase", "--abort"], cwd=wt.path)
                    return False

            # 4. Fast-forward local BASE_BRANCH to rebased worktree tip.
            #    git merge --ff-only works on checked-out branches; git fetch . does not.
            wt_tip = run_cmd(["git", "rev-parse", "HEAD"], cwd=wt.path).stdout.strip()
            ff = run_cmd(
                ["git", "merge", "--ff-only", wt_tip],
                cwd=REPO_ROOT, timeout=30,
            )
            if ff.returncode != 0:
                logger.error(f"ff update of {BASE_BRANCH} failed: {ff.stderr[:300]}")
                return False

            # 5. Push to origin
            push = run_cmd(
                ["git", "push", "origin", BASE_BRANCH],
                cwd=REPO_ROOT, timeout=300,
            )
            if push.returncode == 0:
                return True

            if attempt == 1:
                logger.warning("Push rejected, retrying after fetch + rebase...")
                return False  # caller will retry

            logger.error(f"Push retry failed: {push.stderr[:300]}")
            return False

        if _do_rebase_and_ff(attempt=1):
            logger.info(f"Merged and pushed {wt.branch} to {BASE_BRANCH}")
            return True

        # Retry once (someone else pushed between our rebase and push)
        if _do_rebase_and_ff(attempt=2):
            logger.info(f"Merged and pushed {wt.branch} to {BASE_BRANCH}")
            return True

        return False


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
                pkg_link = entry / "lean4" / ".lake" / "packages"
                if pkg_link.is_symlink():
                    pkg_link.unlink()
                shutil.rmtree(entry, ignore_errors=True)
            # Force-delete branch (may have unmerged commits)
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
    return (
        _load_prompt("phase_b")
        .replace("<ROUND_NUM>", str(round_num))
        .replace("<TOTAL_THEOREMS>", str(total_theorems))
        .replace("<RECENT>", recent)
    )


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
        targets_text += (
            f"### Target {i}\n"
            f"- Paper label: {t.get('paper_label', 'unknown')}\n"
            f"- Lean name: {t.get('lean_name', 'unknown')}\n"
            f"- File: {t.get('target_file', 'unknown')}\n"
            f"- Strategy: {t.get('strategy', 'unknown')}\n"
            f"- Difficulty: {t.get('difficulty', 'unknown')}\n"
            f"- Lean signature:\n"
            f"```lean\n"
            f"{t.get('lean_signature', '-- unknown')}\n"
            f"```\n\n"
        )
    return (
        _load_prompt("phase_c")
        .replace("<ROUND_NUM>", str(round_num))
        .replace("<TARGETS>", targets_text)
    )


def parse_phase_c_output(raw: str) -> PhaseCResult:
    result = PhaseCResult(raw_output=raw)
    # Extract short commit hashes (7-12 hex chars) that look like git output,
    # e.g. lines starting with a hash: "abc1234 commit message"
    commit_hashes = re.findall(r"(?:^|\s)([0-9a-f]{7,12})(?:\s+\w)", raw, re.MULTILINE)
    result.new_commits = list(dict.fromkeys(commit_hashes))[:10]
    # success = codex produced non-empty output and mentioned key actions
    success_indicators = ["lake build", "git commit", "git add", "autostash"]
    result.success = bool(raw) and any(ind.lower() in raw.lower() for ind in success_indicators)
    return result


# ---------------------------------------------------------------------------
# Worktree-based round execution
# ---------------------------------------------------------------------------

def detect_signature_degradation(wt: WorktreeInfo) -> list[str]:
    """Detect theorems whose signatures were degraded to trivial Prop stubs.

    Returns a list of violation descriptions. An empty list means no degradation.

    Detection heuristic: scan git diff against base for `theorem paper_` blocks
    where the new version has ONLY `Prop` parameters and a conclusion that is a
    conjunction of those same propositions (pattern: `: P₁ ∧ P₂ ∧ ...`).
    """
    violations = []
    try:
        result = run_cmd(
            ["git", "diff", f"origin/{BASE_BRANCH}...HEAD", "--", "lean4/Omega/"],
            cwd=wt.path,
        )
        diff_out = result.stdout or ""
    except Exception:
        return violations  # can't check, allow through

    if not diff_out:
        return violations  # empty diff → nothing to check

    # Split diff into per-file chunks and scan only replaced (not new) theorems.
    chunks = re.split(r'^diff --git ', diff_out, flags=re.MULTILINE)
    for chunk in chunks:
        lines = chunk.splitlines()
        added_lines   = [l[1:] for l in lines if l.startswith('+') and not l.startswith('+++')]
        removed_lines = [l[1:] for l in lines if l.startswith('-') and not l.startswith('---')]
        added_text   = '\n'.join(added_lines)
        removed_text = '\n'.join(removed_lines)

        # Find paper_ theorems that appear in both added and removed sections
        # (i.e. replacements of existing theorems, not brand-new ones).
        added_thms = re.findall(
            r'theorem (paper_\w+)\s+(.*?)(?=\ntheorem |\nend |\Z)',
            added_text, re.DOTALL,
        )
        for thm_name, thm_body in added_thms:
            if thm_name not in removed_text:
                continue  # purely new theorem — not a degradation candidate

            # Extract parameter list (before := or by)
            param_match = re.match(r'(.*?)(?::=\s|:= by\b|\n\s*by\b)', thm_body, re.DOTALL)
            if not param_match:
                continue
            params = param_match.group(1)

            # Degrade pattern: parameters contain ONLY abstract Prop types and
            # the conclusion is a trivial conjunction of those same props.
            # Require BOTH conditions to minimise false positives.
            concrete_types = r':\s*(ℕ|ℝ|ℤ|ℚ|ℂ|ℕ\s*→|ℝ\s*→|Fin\b|List\b|Finset\b|Matrix\b|Set\b|Multiset\b|Nat\b|Int\b|Real\b|Float\b|Array\b)'
            has_concrete  = bool(re.search(concrete_types, params))
            has_only_prop = bool(re.search(r':\s*Prop\b', params)) and not has_concrete

            # Extract conclusion (after the last `:`)
            conclusion_match = re.search(r':\s*([^:=]+?)\s*(?::=|$)', thm_body, re.DOTALL)
            conclusion = conclusion_match.group(1) if conclusion_match else ""
            # Trivial conclusion: only conjunctions/implications of plain identifiers
            is_trivial_conclusion = bool(
                re.fullmatch(r'[\w\s∧→¬∨⟨⟩(),\.]+', conclusion.strip())
            ) and not re.search(r'[=≠<>≤≥∈∉]', conclusion)

            if has_only_prop and is_trivial_conclusion:
                violations.append(
                    f"{thm_name}: signature replaced with trivial Prop stub "
                    f"(all concrete types removed, conclusion is a trivial conjunction)"
                )
    return violations


# ---------------------------------------------------------------------------
# Abstract-Prop shell pattern detector
#
# Detects the R1100+ codex-first anti-pattern of producing fake formalizations
# by wrapping the paper claim in a `structure …Data where` with abstract Prop
# fields, then "proving" `paper_*` theorems as tautologies on those fields.
# See phase_c.txt HARD PROHIBITION for the full forbidden pattern.
# ---------------------------------------------------------------------------

_STRUCT_DATA_RE = re.compile(r"^structure\s+(\w+Data)\s+where\s*$", re.MULTILINE)
_SHELL_THM_RE = re.compile(
    r"^theorem\s+(paper_\w+)\s*((?:\([^)]*\)\s*)*)\s*:",
    re.MULTILINE,
)


def _file_is_shell_new(text: str) -> Optional[str]:
    """Return a violation description if `text` (a .lean file) contains the
    abstract-Prop-Data shell anti-pattern; otherwise None."""
    # 1. Find at least one `structure …Data where` with bare `Prop` fields.
    for sm in _STRUCT_DATA_RE.finditer(text):
        struct_name = sm.group(1)
        body_start = sm.end()
        tail = re.search(r"^\S", text[body_start:], re.MULTILINE)
        body = text[body_start:body_start + tail.start()] if tail else text[body_start:]
        prop_fields: set[str] = set()
        has_hyp_or_derive = False
        has_concrete_field = False
        for ln in body.splitlines():
            if not ln.strip():
                continue
            m_prop = re.match(r"^  (\w+)\s*:\s*Prop\s*$", ln)
            if m_prop:
                prop_fields.add(m_prop.group(1))
                continue
            m_any = re.match(r"^  (\w+)\s*:\s*(.+)$", ln)
            if m_any:
                fname, ftype = m_any.group(1), m_any.group(2).strip()
                if fname.endswith("_h") and ftype in prop_fields:
                    has_hyp_or_derive = True
                elif fname.startswith("derive") and "→" in ftype:
                    has_hyp_or_derive = True
                else:
                    has_concrete_field = True
        # Pure shell: ≥2 bare Prop fields, at least one hyp/derive, no concrete field
        if len(prop_fields) >= 2 and has_hyp_or_derive and not has_concrete_field:
            # 2. Find a paper_* theorem that takes (D : struct_name) as parameter.
            for tm in _SHELL_THM_RE.finditer(text):
                header = tm.group(2) or ""
                if re.search(rf"\(\s*\w+\s*:\s*{re.escape(struct_name)}\s*\)", header):
                    return (
                        f"structure {struct_name} has {len(prop_fields)} abstract Prop fields "
                        f"wrapped by theorem {tm.group(1)}; see phase_c.txt HARD PROHIBITION"
                    )
    return None


def detect_shell_pattern(wt: WorktreeInfo) -> list[str]:
    """Scan .lean files NEWLY added in this round for the abstract-Prop shell pattern."""
    violations: list[str] = []
    try:
        # Get newly-added files in this round vs. base branch.
        result = run_cmd(
            ["git", "diff", "--name-status", f"origin/{BASE_BRANCH}...HEAD"],
            cwd=wt.path,
        )
        lines = (result.stdout or "").splitlines()
    except Exception:
        return violations  # can't check, allow through

    new_files: list[str] = []
    for ln in lines:
        parts = ln.split("\t")
        if len(parts) < 2:
            continue
        status, path = parts[0], parts[-1]
        if status.startswith("A") and path.startswith("lean4/Omega/") and path.endswith(".lean"):
            new_files.append(path)

    for rel in new_files:
        p = wt.path / rel
        try:
            text = p.read_text(encoding="utf-8")
        except Exception:
            continue
        v = _file_is_shell_new(text)
        if v:
            violations.append(f"{rel}: {v}")
    return violations


def verify_worktree_commits(wt: WorktreeInfo, pre_commits: list[str]) -> tuple[bool, list[str]]:
    """Check for new commits in the worktree. Also rejects signature degradation
    and new abstract-Prop shell files."""
    post = git_log_oneline(20, cwd=wt.path)
    new = [c for c in post if c not in pre_commits]
    if new:
        logger.info(f"[R{wt.round_number}] Phase D: {len(new)} new commit(s):")
        for c in new:
            logger.info(f"  {c}")
        # Gate 1: signature degradation on existing theorems
        violations = detect_signature_degradation(wt)
        if violations:
            for v in violations:
                logger.error(f"[R{wt.round_number}] SIGNATURE DEGRADATION: {v}")
            logger.error(
                f"[R{wt.round_number}] Rejecting round: {len(violations)} theorem(s) had "
                f"signatures replaced with trivial Prop stubs. "
                f"Fix: keep original signature and leave proof as-is if stuck."
            )
            return False, new
        # Gate 2: new abstract-Prop shell files
        shell_violations = detect_shell_pattern(wt)
        if shell_violations:
            for v in shell_violations:
                logger.error(f"[R{wt.round_number}] SHELL PATTERN: {v}")
            logger.error(
                f"[R{wt.round_number}] Rejecting round: {len(shell_violations)} new file(s) "
                f"introduced the abstract-Prop Data shell anti-pattern. "
                f"Fix: state paper_* theorems about concrete objects; use sorry + "
                f"\\leanpartial{{…}}{{reason}} if proof is incomplete."
            )
            return False, new
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
    new_commits: list[str] = []
    success: bool = False
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
            memory_pressure_wait(context=f"dispatch R{rn}")
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
        "--stop", action="store_true",
        help=f"Create {STOP_FILE.name} to signal the running pipeline to drain and exit",
    )
    parser.add_argument(
        "--resume", action="store_true",
        help=f"Remove {STOP_FILE.name} so the pipeline resumes dispatching new rounds",
    )
    parser.add_argument(
        "--base-branch", type=str, default=BASE_BRANCH,
        help=f"Base branch name (default: {BASE_BRANCH})",
    )
    parser.add_argument(
        "--mem-guard", dest="mem_guard", action="store_true", default=None,
        help="Enable macOS memory-pressure guard (default: on for darwin)",
    )
    parser.add_argument(
        "--no-mem-guard", dest="mem_guard", action="store_false",
        help="Disable macOS memory-pressure guard",
    )
    parser.add_argument(
        "--mem-threshold", type=str, default="warn",
        choices=list(_MEM_LEVEL_BY_NAME.keys()),
        help="Pause dispatch when kern.memorystatus_vm_pressure_level >= this "
             "(default: warn)",
    )
    parser.add_argument(
        "--mem-swap-ceiling-gb", type=float, default=16.0,
        help="Pause dispatch when used swap exceeds this many GB (default: 16)",
    )
    parser.add_argument(
        "--mem-poll", type=int, default=30,
        help="Memory-guard poll interval in seconds (default: 30)",
    )
    parser.add_argument(
        "--mem-max-wait", type=int, default=1800,
        help="Memory-guard max wait before proceeding anyway, in seconds (default: 1800)",
    )
    args = parser.parse_args()

    BASE_BRANCH = args.base_branch

    # ── Memory-pressure guard config ──────────────────────────────
    _MEM_GUARD_CFG["enabled"] = (
        sys.platform == "darwin" if args.mem_guard is None else bool(args.mem_guard)
    )
    _MEM_GUARD_CFG["level_threshold"] = _MEM_LEVEL_BY_NAME[args.mem_threshold]
    _MEM_GUARD_CFG["swap_ceiling_gb"] = float(args.mem_swap_ceiling_gb)
    _MEM_GUARD_CFG["poll_seconds"] = int(args.mem_poll)
    _MEM_GUARD_CFG["max_wait_seconds"] = int(args.mem_max_wait)
    if _MEM_GUARD_CFG["enabled"]:
        lvl, swap = memory_pressure_snapshot()
        logger.info(
            f"Memory guard: ON (threshold={args.mem_threshold} "
            f"[level≥{_MEM_GUARD_CFG['level_threshold']}], "
            f"swap≤{_MEM_GUARD_CFG['swap_ceiling_gb']:.1f}GB, "
            f"poll={_MEM_GUARD_CFG['poll_seconds']}s, "
            f"max_wait={_MEM_GUARD_CFG['max_wait_seconds']}s) | "
            f"current: level={lvl}, swap={swap:.1f}GB"
        )
    else:
        logger.info("Memory guard: OFF")

    # ── Cleanup ────────────────────────────────────────────────────
    if args.cleanup:
        n = cleanup_all_worktrees()
        print(f"Cleaned up {n} worktree(s)")
        return 0

    # ── Graceful stop / resume ─────────────────────────────────────
    if args.stop:
        STOP_FILE.touch()
        print(f"Created {STOP_FILE} — running pipeline will drain and exit after current rounds finish.")
        return 0
    if args.resume:
        if STOP_FILE.exists():
            STOP_FILE.unlink()
            print(f"Removed {STOP_FILE} — pipeline will resume dispatching new rounds.")
        else:
            print(f"{STOP_FILE} did not exist (pipeline was not stopped).")
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

    # Prune stale worktree registrations and remove orphaned physical dirs from
    # previous sessions (rounds that were killed before cleanup ran).
    if not args.dry_run:
        run_cmd(["git", "worktree", "prune"], cwd=REPO_ROOT)
        if WORKTREE_DIR.exists():
            for entry in WORKTREE_DIR.iterdir():
                if entry.is_dir() and entry.name.startswith("round_R"):
                    # Only remove dirs not registered as active worktrees
                    wt_result = run_cmd(["git", "worktree", "list", "--porcelain"], cwd=REPO_ROOT)
                    if str(entry) not in wt_result.stdout:
                        logger.info(f"Removing orphaned worktree dir: {entry}")
                        pkg_link = entry / "lean4" / ".lake" / "packages"
                        if pkg_link.is_symlink():
                            pkg_link.unlink()
                        shutil.rmtree(entry, ignore_errors=True)

    state = load_state()
    logger.info(f"Starting: R{state.round_number}, ~{state.total_theorems} theorems")

    total_succeeded = 0
    total_failed = 0

    if args.continuous:
        # ── True rolling pipeline: as soon as one worker finishes, start the next ──
        logger.info(f"{'='*60}")
        logger.info(f"Rolling pipeline: {args.parallel} concurrent workers, running until stopped")
        logger.info(f"{'='*60}")

        with ThreadPoolExecutor(max_workers=args.parallel, thread_name_prefix="worker") as pool:
            futures: dict[Future, int] = {}

            def _submit_next() -> None:
                if STOP_FILE.exists():
                    logger.info(f"Stop file detected ({STOP_FILE}), not dispatching new rounds")
                    return
                if state.consecutive_failures >= args.max_consecutive_failures:
                    return
                with _round_lock:
                    rn = state.round_number
                    state.round_number += 1
                memory_pressure_wait(context=f"dispatch R{rn}")
                fut = pool.submit(
                    run_round_in_worktree,
                    rn, state.total_theorems, state.recent_commits,
                    dry_run=args.dry_run,
                    model=args.model,
                    phase_b_timeout=args.phase_b_timeout,
                    phase_c_timeout=args.phase_c_timeout,
                )
                futures[fut] = rn
                logger.info(f"Dispatching R{rn} (rolling)")

            # Fill the pool initially
            for _ in range(args.parallel):
                _submit_next()

            while futures:
                if state.consecutive_failures >= args.max_consecutive_failures:
                    logger.error(
                        f"Stopping: {state.consecutive_failures} consecutive failures"
                    )
                    break
                done, _ = wait(futures, return_when=FIRST_COMPLETED)
                for fut in done:
                    rn = futures.pop(fut)
                    try:
                        ok, _, commits = fut.result()
                        if ok:
                            total_succeeded += 1
                            state.consecutive_failures = 0
                            logger.info(f"[R{rn}] SUCCESS ({len(commits)} commits)")
                        else:
                            total_failed += 1
                            state.consecutive_failures += 1
                            logger.warning(f"[R{rn}] FAILED")
                    except Exception as exc:
                        total_failed += 1
                        state.consecutive_failures += 1
                        logger.error(f"[R{rn}] EXCEPTION: {exc}")
                    state.total_theorems = count_lean_theorems()
                    state.recent_commits = git_log_oneline(5)
                    save_state(state)
                    # Immediately launch a replacement worker
                    _submit_next()

    else:
        # ── Batch mode (non-continuous) ────────────────────────────────────────────
        max_batches = args.rounds
        for batch_idx in range(max_batches):
            if state.consecutive_failures >= args.max_consecutive_failures:
                logger.error(
                    f"Stopping: {state.consecutive_failures} consecutive all-fail batches"
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
                time.sleep(5)

    # ── Summary ────────────────────────────────────────────────────
    logger.info(f"{'='*60}")
    logger.info(f"Session complete: {total_succeeded} succeeded, {total_failed} failed")
    logger.info(f"Final: R{state.round_number}, ~{state.total_theorems} theorems")
    logger.info(f"{'='*60}")

    return 0 if total_succeeded > 0 or args.dry_run else 1


if __name__ == "__main__":
    raise SystemExit(main())
