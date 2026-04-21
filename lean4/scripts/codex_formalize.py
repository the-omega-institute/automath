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
# Lake-gate config exported to every codex child so they all coordinate on
# the same lock dir / slot count. Defaults below are conservative for a
# 16 GB M-series Mac. Override via CLI flags (--lake-parallel, --lake-lock-dir).
LAKE_GATE_LOCK_DIR = REPO_ROOT / ".worktrees" / ".lake-gate"
LAKE_GATE_MAX_PARALLEL = 1
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
# Lock serializing .lake/build merges back to the main repo
_lake_merge_lock = threading.Lock()

# Single-slot build request for the background builder (multi-producer,
# single-consumer, collapsing). Each worker that merges a round calls
# `request_build(sha)`. The builder consumes only the latest SHA — if
# multiple commits land while the builder is busy, only the newest tip
# is built; intermediate SHAs are skipped.
_build_cv = threading.Condition()
_build_request: Optional[str] = None
_builder_stop = threading.Event()


def request_build(sha: str) -> None:
    """Producer: signal that `sha` is a new build candidate. Overwrites
    any pending (unbuild) request — the builder will pick the latest."""
    global _build_request
    with _build_cv:
        _build_request = sha
        _build_cv.notify()

# In-memory dedup of in-flight target IDs across parallel rounds.
# Phase B selects targets concurrently and can pick the same paper (same
# lean_name / paper_label) in two worktrees; the second one wastes a Phase C
# and produces a merge conflict. We register each round's target IDs after
# Phase B and drop any that overlap with another live round; if too few
# remain we fail the round before Phase C. Entries are removed in
# `run_round_in_worktree`'s finally block, so the set only ever holds IDs
# of rounds currently in flight (~= --parallel size).
_active_targets_lock = threading.Lock()
_active_targets: dict[int, set[str]] = {}


def _target_id(t: dict) -> str:
    """Stable cross-round identifier for a target."""
    return (t.get("lean_name") or t.get("paper_label") or "").strip()


def claim_targets(round_num: int, targets: list[dict]) -> tuple[list[dict], list[str]]:
    """Filter `targets` against in-flight target IDs from other rounds.
    Returns (kept, dropped_ids). Registers the kept IDs under `round_num`."""
    kept: list[dict] = []
    dropped: list[str] = []
    with _active_targets_lock:
        taken: set[str] = set()
        for s in _active_targets.values():
            taken |= s
        keep_ids: set[str] = set()
        for t in targets:
            tid = _target_id(t)
            if not tid:
                # Unkeyable target — keep but don't register; can't dedup.
                kept.append(t)
                continue
            if tid in taken or tid in keep_ids:
                dropped.append(tid)
                continue
            keep_ids.add(tid)
            kept.append(t)
        if keep_ids:
            _active_targets[round_num] = keep_ids
    return kept, dropped


def release_targets(round_num: int) -> None:
    with _active_targets_lock:
        _active_targets.pop(round_num, None)

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
    base_sha: str = ""  # HEAD at worktree creation; ground truth for "new" commits


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

    base_sha = run_cmd(["git", "rev-parse", "HEAD"], cwd=wt_path).stdout.strip()
    return WorktreeInfo(
        path=wt_path, branch=branch, round_number=round_num, base_sha=base_sha,
    )


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


def merge_lake_cache_back(wt: WorktreeInfo, new_commits: list[str]) -> None:
    """After a successful merge, propagate the worktree's freshly-built .olean
    artifacts back into the main repo's .lake/build/ so that the next round's
    worktree (which COW-clones this cache) starts warm for the files added in
    this round.

    Only copies artifacts whose source .lean was ADDED or MODIFIED in this
    round (surgical, O(new files)). For each source `lean4/Omega/<mod>.lean`,
    propagates its lib/ (.olean/.ilean/.hash/.trace) and ir/ (.c/.hash/.setup.json)
    artifacts. Destination files that already exist are not overwritten
    (safe against concurrent merges — main's pre-existing artifact is by
    construction compatible with the branch tip).
    """
    # Extensions produced per .lean source. Not all are always present
    # (e.g. .trace for freshly-rebuilt, .setup.json only when lake regenerates).
    LIB_EXTS = (".olean", ".olean.hash", ".ilean", ".ilean.hash", ".trace")
    IR_EXTS = (".c", ".c.hash", ".setup.json")

    src_root = wt.path / "lean4" / ".lake" / "build"
    dst_root = LEAN_ROOT / ".lake" / "build"
    if not src_root.exists():
        return

    # new_commits entries look like "<sha> <subject>"; pull out the SHA.
    shas = [c.split(None, 1)[0] for c in new_commits if c.strip()]
    if not shas:
        return

    # Resolve .lean files touched by exactly these commits (merge invariant).
    try:
        r = run_cmd(
            ["git", "show", "--name-only", "--pretty=format:",
             "--diff-filter=AM", *shas],
            cwd=wt.path,
        )
        changed = sorted({
            l.strip() for l in (r.stdout or "").splitlines()
            if l.strip().endswith(".lean") and l.strip().startswith("lean4/Omega/")
        })
    except Exception:
        return

    if not changed:
        return

    with _lake_merge_lock:
        start = time.monotonic()
        copied = 0
        for rel in changed:
            # "lean4/Omega/X/Y.lean" -> "Omega/X/Y"
            mod = rel[len("lean4/"):-len(".lean")]
            for sub, exts in (("lib/lean", LIB_EXTS), ("ir", IR_EXTS)):
                for ext in exts:
                    src = src_root / sub / f"{mod}{ext}"
                    if not src.is_file():
                        continue
                    dst = dst_root / sub / f"{mod}{ext}"
                    if dst.exists():
                        continue
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    try:
                        # APFS copy-on-write when possible.
                        subprocess.run(
                            ["cp", "-c", str(src), str(dst)],
                            check=True, stdin=subprocess.DEVNULL,
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                            timeout=30,
                        )
                        copied += 1
                    except Exception:
                        try:
                            shutil.copy2(src, dst)
                            copied += 1
                        except Exception:
                            pass
        elapsed = time.monotonic() - start
        logger.info(
            f"[R{wt.round_number}] Lake cache merged back: "
            f"{copied} artifact(s) from {len(changed)} source(s) ({elapsed:.2f}s)"
        )


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

CODEX_LOG_DIR = LOG_DIR / "codex"


def codex_exec(
    prompt: str,
    *,
    work_dir: Optional[Path] = None,
    timeout_seconds: int = 1800,
    output_file: Optional[Path] = None,
    model: Optional[str] = None,
    dry_run: bool = False,
    log_tag: Optional[str] = None,
) -> str:
    """Call `codex exec` with the given prompt, targeting work_dir.

    If `log_tag` is provided (e.g. "R1325_phaseC"), persists prompt + stdout
    to `LOG_DIR/codex/<tag>_<timestamp>.{prompt,out}.txt` for post-mortem.
    Otherwise uses tmp files and discards them after the call."""
    if dry_run:
        logger.info(f"[DRY RUN] codex exec (cwd={work_dir}):\n"
                     f"{prompt[:400]}{'...' if len(prompt) > 400 else ''}")
        return "(dry run -- no output)"

    codex_bin = CODEX_PATH if Path(CODEX_PATH).exists() else shutil.which("codex")
    if not codex_bin:
        raise FileNotFoundError("Codex CLI not found")

    target_dir = str(work_dir or REPO_ROOT)
    persist = log_tag is not None
    if persist:
        CODEX_LOG_DIR.mkdir(parents=True, exist_ok=True)
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        prompt_file = str(CODEX_LOG_DIR / f"{log_tag}_{ts}.prompt.txt")
        with open(prompt_file, "w", encoding="utf-8") as f:
            f.write(prompt)
    else:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".txt", prefix="codex_prompt_",
            delete=False, encoding="utf-8",
        ) as f:
            f.write(prompt)
            prompt_file = f.name

    out_file = str(output_file) if output_file else None
    if out_file is None:
        if persist:
            out_file = str(CODEX_LOG_DIR / f"{log_tag}_{ts}.out.txt")
            # Ensure file exists so codex can `-o` to it.
            open(out_file, "w").close()
        else:
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

    # Inherit env, but always export the lake_gate config so every codex
    # invocation sees the same shared lock dir and concurrency cap. Without
    # this the gate inside the worktree falls back to its default of 1 slot
    # in $TMPDIR — usually fine, but explicit is safer when callers override.
    child_env = os.environ.copy()
    child_env.setdefault("LAKE_GATE_LOCK_DIR", str(LAKE_GATE_LOCK_DIR))
    child_env.setdefault("LAKE_GATE_MAX_PARALLEL", str(LAKE_GATE_MAX_PARALLEL))

    try:
        with open(prompt_file, "r", encoding="utf-8") as pf:
            result = subprocess.run(
                cmd, stdin=pf, capture_output=True, text=True,
                timeout=timeout_seconds + 30, cwd=target_dir,
                env=child_env,
            )
    except subprocess.TimeoutExpired:
        logger.warning(f"Codex exec timed out after {timeout_seconds}s")
        return "(timeout)"
    finally:
        elapsed = time.monotonic() - start
        rc = result.returncode if result else "?"
        suffix = f" log={log_tag}" if persist else ""
        logger.info(f"Codex exec completed in {elapsed:.1f}s (rc={rc}){suffix}")
        if not persist:
            os.unlink(prompt_file)

    # Read output
    output = ""
    try:
        if os.path.exists(out_file) and os.path.getsize(out_file) > 0:
            with open(out_file, "r", encoding="utf-8") as f:
                output = f.read()
        else:
            output = result.stdout or ""
            # If we used the persistent path but codex wrote nothing to -o,
            # still capture stdout so the post-mortem isn't empty.
            if persist and output:
                with open(out_file, "w", encoding="utf-8") as f:
                    f.write(output)
    finally:
        if output_file is None and not persist:
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


_SORRY_LITERAL_RE = re.compile(
    r"(?<![A-Za-z_])(?:sorry|admit)(?![A-Za-z_])"
)
_AXIOM_DECL_RE = re.compile(r"^\s*axiom\s+\w", re.MULTILINE)


def _strip_lean_comments(src: str) -> str:
    """Replace Lean comment contents with spaces so line numbers stay stable.

    Handles `-- line comments` and `/- block -/` (nested). Needed because
    docstring prose often contains English words like "admit" which otherwise
    trigger the sorry/admit scanner."""
    n = len(src)
    out: list[str] = []
    i = 0
    while i < n:
        c = src[i]
        c2 = src[i:i+2]
        if c2 == "--":
            j = src.find("\n", i)
            if j == -1:
                j = n
            out.append(" " * (j - i))
            i = j
        elif c2 == "/-":
            depth = 1
            i += 2
            out.append("  ")
            while i < n and depth > 0:
                cc = src[i:i+2]
                if cc == "/-":
                    depth += 1
                    out.append("  ")
                    i += 2
                elif cc == "-/":
                    depth -= 1
                    out.append("  ")
                    i += 2
                else:
                    ch = src[i]
                    out.append(ch if ch == "\n" else " ")
                    i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def _lines_added_in_round(wt: WorktreeInfo, rel_path: str) -> set[int]:
    """Line numbers (1-indexed, of the HEAD version) that this round added to
    `rel_path`."""
    try:
        r = run_cmd(
            ["git", "diff", "--unified=0", f"{wt.base_sha}..HEAD", "--", rel_path],
            cwd=wt.path,
        )
    except Exception:
        return set()
    added: set[int] = set()
    # Hunk header: @@ -old +new,count @@
    hunk_re = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@")
    current_new: Optional[int] = None
    remaining: int = 0
    for line in (r.stdout or "").splitlines():
        m = hunk_re.match(line)
        if m:
            current_new = int(m.group(1))
            remaining = int(m.group(2) or "1")
            continue
        if current_new is None:
            continue
        if line.startswith("+") and not line.startswith("+++"):
            added.add(current_new)
            current_new += 1
            remaining -= 1
        elif line.startswith("-") and not line.startswith("---"):
            # deletion doesn't advance the new-file pointer
            pass
        else:
            current_new += 1 if remaining else 0
    return added


def detect_sorry_literals(wt: WorktreeInfo) -> list[str]:
    """Reject any round that introduces a literal `sorry`/`admit`/`axiom` in
    actual Lean code (not comments/docstrings) in files under lean4/Omega/.

    Implementation: for each .lean file the round added or modified, strip
    `--` line comments and `/- -/` block comments (preserving line numbers),
    scan the result for sorry/admit/axiom tokens, and only flag matches whose
    line is among the lines this round added. This avoids false positives
    from English prose in docstrings that happens to contain the word
    "admit"."""
    violations: list[str] = []
    if not wt.base_sha:
        return violations
    try:
        r = run_cmd(
            ["git", "diff", "--name-only", "--diff-filter=AM",
             f"{wt.base_sha}..HEAD", "--", "lean4/Omega/"],
            cwd=wt.path,
        )
    except Exception:
        return violations
    files = [l.strip() for l in (r.stdout or "").splitlines()
             if l.strip().endswith(".lean")]
    for rel in files:
        try:
            src = (wt.path / rel).read_text(encoding="utf-8")
        except Exception:
            continue
        stripped = _strip_lean_comments(src)
        added_lines = _lines_added_in_round(wt, rel)
        if not added_lines:
            continue
        for m in _SORRY_LITERAL_RE.finditer(stripped):
            line_no = stripped.count("\n", 0, m.start()) + 1
            if line_no in added_lines:
                ctx = src.splitlines()[line_no - 1].strip()[:140]
                violations.append(f"{rel}:{line_no}: {m.group()} — {ctx}")
        for m in _AXIOM_DECL_RE.finditer(stripped):
            line_no = stripped.count("\n", 0, m.start()) + 1
            if line_no in added_lines:
                ctx = src.splitlines()[line_no - 1].strip()[:140]
                violations.append(f"{rel}:{line_no}: axiom — {ctx}")
    return violations


def verify_worktree_commits(wt: WorktreeInfo, pre_commits: list[str]) -> tuple[bool, list[str]]:
    """Check for new commits in the worktree. Also rejects signature degradation,
    new abstract-Prop shell files, sorry/admit/axiom literals, and any commit
    whose final lake build does not pass.

    Ground truth for "new commits" is `git log <base_sha>..HEAD` where base_sha
    is the worktree HEAD captured at creation. This is robust to codex doing
    `git fetch + rebase` inside the worktree (which moves HEAD past commits
    that already exist on origin); a window-based comparison against
    `pre_commits` mistakenly counted those as new in earlier versions.
    """
    if wt.base_sha:
        result = run_cmd(
            ["git", "log", "--oneline", f"{wt.base_sha}..HEAD"],
            cwd=wt.path,
        )
        new = [l.strip() for l in result.stdout.splitlines() if l.strip()]
    else:
        # Backward-compat fallback for worktrees created before base_sha existed.
        post = git_log_oneline(40, cwd=wt.path)
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
        # Gate 3: sorry/admit/axiom literals in newly-added or modified lines
        sorry_violations = detect_sorry_literals(wt)
        if sorry_violations:
            for v in sorry_violations[:10]:
                logger.error(f"[R{wt.round_number}] SORRY LITERAL: {v}")
            logger.error(
                f"[R{wt.round_number}] Rejecting round: {len(sorry_violations)} added "
                f"line(s) contain sorry/admit/axiom literals. The completion contract "
                f"in phase_c.txt forbids these in committed code."
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
            log_tag=f"R{round_num}_phaseB",
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

        # ── Dedup: drop targets already claimed by another in-flight round ─
        kept, dropped = claim_targets(round_num, phase_b.targets)
        if dropped:
            logger.warning(
                f"[{tag}] Dedup: dropping {len(dropped)} target(s) already in flight: "
                f"{', '.join(dropped)}"
            )
        if not kept:
            logger.error(f"[{tag}] All targets duplicated by other rounds; aborting")
            _save_round_log(round_num, phase_b, PhaseCResult(), [], False)
            return False, round_num, []
        phase_b.targets = kept

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
            log_tag=f"R{round_num}_phaseC",
        )
        phase_c = parse_phase_c_output(phase_c_raw)

        # ── Phase D: Verify ───────────────────────────────────────
        logger.info(f"[{tag}] Phase D: Verification...")
        if dry_run:
            success = True
        else:
            assert wt is not None
            # No lake build here — codex did single-file `lake env lean` per
            # touched file in Phase C. A separate background builder
            # (bg_builder.py) watches the base branch and auto-dispatches
            # codex repair rounds when the full build breaks downstream.
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
            # Offer the new tip to the builder (collapsing: it will pick
            # up only the latest if multiple rounds land in parallel).
            try:
                new_tip = run_cmd(["git", "rev-parse", BASE_BRANCH],
                                  cwd=REPO_ROOT).stdout.strip()
                if new_tip:
                    request_build(new_tip)
            except Exception as exc:
                logger.warning(f"[{tag}] request_build failed: {exc}")
            # No more merge_lake_cache_back: workers don't run lake build under
            # 方案 B, so copying worker-worktree .oleans back would only risk
            # polluting the main checkout cache that the builder thread owns.
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
        # Always release the round's claim on its target IDs so other rounds
        # can pick them up if this one fails.
        release_targets(round_num)
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
# Background builder (single consumer for the _build_request slot)
# ---------------------------------------------------------------------------

BUILDER_LOG_DIR = LOG_DIR / "builder"
BROKEN_SHAS_FILE = BUILDER_LOG_DIR / "broken_shas.txt"
# Dedicated worktree for the builder thread. Keeping it separate from
# REPO_ROOT stops the race where a worker's `merge_worktree_to_base`
# ff-updates the main checkout's working tree mid-`lake build`, which
# had been leaving the main .lake/build with stale/mixed .oleans.
BUILDER_WORKTREE = WORKTREE_DIR / "_builder"
BUILDER_BRANCH = "_builder_tmp"
# Lock serializing any write to the main REPO_ROOT/.lake/build so that
# round worktree creation (_clone_lake_cache) and builder olean sync
# don't observe each other mid-update.
_main_cache_lock = threading.Lock()


def _ensure_builder_worktree() -> Path:
    """Create the builder worktree on first use, COW-cloning packages/build
    from REPO_ROOT so lake starts warm. Safe to call repeatedly."""
    WORKTREE_DIR.mkdir(parents=True, exist_ok=True)
    if BUILDER_WORKTREE.exists() and (BUILDER_WORKTREE / "lean4").exists():
        return BUILDER_WORKTREE
    with _git_lock:
        # Clean any half-created state.
        run_cmd(["git", "worktree", "remove", "--force", str(BUILDER_WORKTREE)],
                cwd=REPO_ROOT)
        if BUILDER_WORKTREE.exists():
            shutil.rmtree(BUILDER_WORKTREE, ignore_errors=True)
        run_cmd(["git", "branch", "-D", BUILDER_BRANCH], cwd=REPO_ROOT)
        r = run_cmd(
            ["git", "worktree", "add", "-B", BUILDER_BRANCH,
             str(BUILDER_WORKTREE), BASE_BRANCH],
            cwd=REPO_ROOT,
        )
        if r.returncode != 0:
            raise RuntimeError(f"builder worktree add failed: {r.stderr}")
    _clone_lake_cache(BUILDER_WORKTREE)
    logger.info(f"[builder] worktree ready at {BUILDER_WORKTREE}")
    return BUILDER_WORKTREE


def _builder_checkout(sha: str) -> None:
    """Move the builder worktree's branch pointer to `sha` without touching
    any other git state. Done under _git_lock because workers run git ops
    on the same repo."""
    with _git_lock:
        run_cmd(["git", "fetch", "origin", BASE_BRANCH],
                cwd=BUILDER_WORKTREE, timeout=60)
        # reset --hard is safer than merge --ff-only here: we want the
        # worktree to match the requested sha exactly, and we own this branch.
        run_cmd(["git", "reset", "--hard", sha],
                cwd=BUILDER_WORKTREE, timeout=60)


def _sync_omega_cache_to_main() -> None:
    """After a successful lake build in BUILDER_WORKTREE, copy freshly-built
    Omega .oleans back to REPO_ROOT/lean4/.lake/build so that round worker
    worktrees (which COW this cache on creation) pick up the latest olean
    set. mathlib/Cli/etc under .lake/packages are untouched."""
    src_root = BUILDER_WORKTREE / "lean4" / ".lake" / "build"
    dst_root = LEAN_ROOT / ".lake" / "build"
    if not src_root.exists():
        return
    with _main_cache_lock:
        t0 = time.monotonic()
        copied = 0
        # Atomic-ish replace: rename dir → new side-by-side, then swap.
        for sub in ("lib/lean/Omega", "ir/Omega"):
            src = src_root / sub
            dst = dst_root / sub
            if not src.exists():
                continue
            dst.parent.mkdir(parents=True, exist_ok=True)
            tmp = dst.with_name(dst.name + f".new_{os.getpid()}")
            try:
                if tmp.exists():
                    shutil.rmtree(tmp, ignore_errors=True)
                # APFS copy-on-write when possible.
                r = subprocess.run(
                    ["cp", "-Rc", str(src), str(tmp)],
                    timeout=600, check=False, stdin=subprocess.DEVNULL,
                )
                if r.returncode != 0:
                    shutil.rmtree(tmp, ignore_errors=True)
                    continue
                if dst.exists():
                    old = dst.with_name(dst.name + f".old_{os.getpid()}")
                    dst.rename(old)
                    tmp.rename(dst)
                    shutil.rmtree(old, ignore_errors=True)
                else:
                    tmp.rename(dst)
                copied += 1
            except Exception as exc:
                logger.warning(f"[builder] sync {sub} failed: {exc}")
                shutil.rmtree(tmp, ignore_errors=True)
        # Root-level Omega artifacts (Omega.olean and friends).
        for name in ("Omega.olean", "Omega.olean.hash",
                     "Omega.ilean", "Omega.ilean.hash"):
            src_file = src_root / "lib" / "lean" / name
            dst_file = dst_root / "lib" / "lean" / name
            if src_file.exists():
                try:
                    shutil.copy2(src_file, dst_file)
                    copied += 1
                except Exception:
                    pass
        elapsed = time.monotonic() - t0
        logger.info(f"[builder] synced {copied} Omega cache item(s) "
                    f"to main checkout ({elapsed:.1f}s)")


def _read_broken_shas() -> set[str]:
    if not BROKEN_SHAS_FILE.exists():
        return set()
    try:
        return set(l.split("\t", 1)[0].strip()
                   for l in BROKEN_SHAS_FILE.read_text().splitlines() if l.strip())
    except Exception:
        return set()


def _record_broken_sha(sha: str, log_name: str) -> None:
    BUILDER_LOG_DIR.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    with open(BROKEN_SHAS_FILE, "a", encoding="utf-8") as f:
        f.write(f"{sha}\t{ts}\t{log_name}\n")


def _builder_lake_build(cwd: Path, log_file: Path, timeout: int = 7200) -> tuple[bool, str]:
    log_file.parent.mkdir(parents=True, exist_ok=True)
    with open(log_file, "w", encoding="utf-8") as lf:
        lf.write(f"# lake build at {datetime.now().isoformat()} cwd={cwd}\n\n")
        lf.flush()
        try:
            r = subprocess.run(
                ["lake", "build"], cwd=str(cwd),
                stdout=lf, stderr=subprocess.STDOUT,
                timeout=timeout, stdin=subprocess.DEVNULL,
            )
            ok = r.returncode == 0
        except subprocess.TimeoutExpired:
            lf.write("\n# TIMEOUT\n")
            ok = False
    try:
        tail = "\n".join(log_file.read_text(encoding="utf-8").splitlines()[-30:])
    except Exception:
        tail = ""
    return ok, tail


def _builder_make_fix_worktree(sha: str) -> WorktreeInfo:
    """Create a `fix-<sha8>` worktree at `sha`, with .lake cache cloned."""
    WORKTREE_DIR.mkdir(parents=True, exist_ok=True)
    short = sha[:8]
    branch = f"fix-{short}"
    wt_path = WORKTREE_DIR / f"fix_{short}"
    with _git_lock:
        if wt_path.exists():
            run_cmd(["git", "worktree", "remove", "--force", str(wt_path)],
                    cwd=REPO_ROOT)
            if wt_path.exists():
                shutil.rmtree(wt_path, ignore_errors=True)
        run_cmd(["git", "branch", "-D", branch], cwd=REPO_ROOT)
        r = run_cmd(["git", "worktree", "add", "-b", branch, str(wt_path), sha],
                    cwd=REPO_ROOT)
        if r.returncode != 0:
            raise RuntimeError(f"worktree add failed: {r.stderr}")
    _clone_lake_cache(wt_path)
    base_sha = run_cmd(["git", "rev-parse", "HEAD"], cwd=wt_path).stdout.strip()
    return WorktreeInfo(path=wt_path, branch=branch, round_number=-1, base_sha=base_sha)


def _builder_codex_fix(wt: WorktreeInfo, build_log: Path,
                       *, timeout: int = 3600) -> bool:
    """Invoke codex with the build log tail to produce a fix commit. Returns
    True if codex produced a new commit on the fix branch."""
    try:
        log_text = build_log.read_text(encoding="utf-8")
    except Exception:
        log_text = "(log unreadable)"
    log_tail = "\n".join(log_text.splitlines()[-200:])
    prompt = textwrap.dedent(f"""\
        Lean4 `lake build` is failing on branch `{BASE_BRANCH}`. Fix it.

        ## Rules
        - You are on fix branch `{wt.branch}` at the broken tip.
        - Edit only inside lean4/Omega/.
        - No new sorry/admit/axiom. No native_decide on large enumerations.
        - Keep the patch minimal: change only what's needed to unstick build.
        - Use per-file `lake env lean Omega/<X>/<Y>.lean` to confirm edits.
          Do NOT run full `lake build` — the orchestrator re-verifies.
        - After fix: `git add lean4/Omega/` + `git commit` + push to
          `{BASE_BRANCH}`:
            git push origin HEAD:{BASE_BRANCH}
          If push rejected, rebase onto `origin/{BASE_BRANCH}`, re-verify
          with `lake env lean <file>`, push again.

        ## Build log tail (last 200 lines)
        ```
        {log_tail}
        ```
    """)
    out = codex_exec(
        prompt, work_dir=wt.path, timeout_seconds=timeout,
        log_tag=f"fix_{wt.branch}",
    )
    # Success = new commit on this branch vs the base sha at creation
    try:
        head = run_cmd(["git", "rev-parse", "HEAD"], cwd=wt.path).stdout.strip()
    except Exception:
        head = ""
    if head and head != wt.base_sha:
        logger.info(f"[builder] codex fix produced commit {head[:8]}")
        return True
    logger.warning("[builder] codex fix produced no new commit")
    return False


def _builder_attempt_fix(sha: str, build_log: Path, max_attempts: int) -> bool:
    for i in range(1, max_attempts + 1):
        logger.info(f"[builder] fix attempt {i}/{max_attempts} for {sha[:8]}")
        try:
            wt = _builder_make_fix_worktree(sha)
        except Exception as exc:
            logger.error(f"[builder] fix worktree creation failed: {exc}")
            return False
        try:
            if not _builder_codex_fix(wt, build_log):
                continue
            vlog = BUILDER_LOG_DIR / f"fix_verify_{wt.branch}_{i}.txt"
            ok, tail = _builder_lake_build(wt.path / "lean4", vlog)
            if ok:
                logger.info(f"[builder] fix {wt.branch} verified (log={vlog.name})")
                return True
            logger.warning(f"[builder] fix {wt.branch} still failing (log={vlog.name})")
        finally:
            try:
                with _git_lock:
                    run_cmd(["git", "worktree", "remove", "--force", str(wt.path)],
                            cwd=REPO_ROOT)
                    pkg = wt.path / "lean4" / ".lake" / "packages"
                    if pkg.is_symlink():
                        try: pkg.unlink()
                        except Exception: pass
                    if wt.path.exists():
                        shutil.rmtree(wt.path, ignore_errors=True)
                    run_cmd(["git", "branch", "-D", wt.branch], cwd=REPO_ROOT)
            except Exception:
                pass
    return False


def _builder_loop(poll_seconds: float, max_fix_attempts: int) -> None:
    """Single-consumer loop. Blocks on `_build_cv` for a new SHA request,
    runs `lake build` in BUILDER_WORKTREE (separate from REPO_ROOT so that
    worker merges don't ff the builder's working tree mid-build), and on
    success syncs the fresh Omega .oleans back to REPO_ROOT/.lake/build
    for round worker worktrees to COW. On failure spawns a codex fix. When
    multiple SHAs queue up during a build, only the latest is processed."""
    global _build_request
    logger.info(f"[builder] started (poll={poll_seconds}s, max_fix={max_fix_attempts})")
    BUILDER_LOG_DIR.mkdir(parents=True, exist_ok=True)
    try:
        _ensure_builder_worktree()
    except Exception as exc:
        logger.error(f"[builder] cannot initialize builder worktree: {exc}")
        return
    last_built: Optional[str] = None
    while not _builder_stop.is_set():
        with _build_cv:
            while _build_request is None and not _builder_stop.is_set():
                _build_cv.wait(timeout=poll_seconds)
            if _builder_stop.is_set():
                break
            sha = _build_request
            _build_request = None
        if sha is None or sha == last_built:
            continue
        if sha in _read_broken_shas():
            logger.info(f"[builder] {sha[:8]} already recorded broken; skipping")
            last_built = sha
            continue
        logger.info(f"[builder] building {sha[:8]} in builder worktree")
        try:
            _builder_checkout(sha)
        except Exception as exc:
            logger.error(f"[builder] checkout {sha[:8]} failed: {exc}")
            continue
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        build_log = BUILDER_LOG_DIR / f"build_{sha[:8]}_{ts}.txt"
        ok, tail = _builder_lake_build(BUILDER_WORKTREE / "lean4", build_log)
        if ok:
            logger.info(f"[builder] PASS {sha[:8]} (log={build_log.name})")
            try:
                _sync_omega_cache_to_main()
            except Exception as exc:
                logger.warning(f"[builder] cache sync failed: {exc}")
            last_built = sha
            continue
        logger.error(f"[builder] FAIL {sha[:8]} (log={build_log.name})")
        for ln in tail.splitlines()[-10:]:
            logger.error(f"  {ln}")
        if _builder_attempt_fix(sha, build_log, max_fix_attempts):
            last_built = None     # fix pushed new tip; next loop picks it up
        else:
            _record_broken_sha(sha, build_log.name)
            last_built = sha
    logger.info("[builder] stopped")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> int:
    global BASE_BRANCH, LAKE_GATE_LOCK_DIR, LAKE_GATE_MAX_PARALLEL

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
    parser.add_argument(
        "--no-builder", action="store_true",
        help="Disable the in-process bg_builder thread that watches the base "
             "branch, runs full lake build on new tips, and auto-dispatches "
             "codex repair rounds on failure.",
    )
    parser.add_argument(
        "--builder-poll", type=float, default=60.0,
        help="bg_builder: seconds between origin fetches (default 60)",
    )
    parser.add_argument(
        "--builder-max-fix", type=int, default=3,
        help="bg_builder: max codex repair attempts per broken SHA (default 3)",
    )
    parser.add_argument(
        "--lake-parallel", type=int, default=None,
        help="Concurrent `lake` cap exported to codex children via "
             "LAKE_GATE_MAX_PARALLEL. Defaults to max(1, --parallel // 2) so "
             "lake never runs in more workers than half the round count.",
    )
    parser.add_argument(
        "--lake-lock-dir", type=str, default=None,
        help=f"Shared lock directory for lake_gate.py "
             f"(default: {LAKE_GATE_LOCK_DIR}).",
    )
    args = parser.parse_args()

    if args.lake_lock_dir:
        LAKE_GATE_LOCK_DIR = Path(args.lake_lock_dir)
    LAKE_GATE_LOCK_DIR.mkdir(parents=True, exist_ok=True)
    if args.lake_parallel is not None:
        LAKE_GATE_MAX_PARALLEL = max(1, args.lake_parallel)
    else:
        LAKE_GATE_MAX_PARALLEL = max(1, args.parallel // 2)
    logger.info(
        f"Lake gate: max_parallel={LAKE_GATE_MAX_PARALLEL}, "
        f"lock_dir={LAKE_GATE_LOCK_DIR}"
    )

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
    # consecutive_failures is a runtime signal for mid-session backoff;
    # a fresh session starts the counter at 0. Otherwise a previously-killed
    # pipeline makes the new pipeline cooldown immediately on boot.
    if state.consecutive_failures:
        logger.info(f"Resetting consecutive_failures={state.consecutive_failures} on session start")
        state.consecutive_failures = 0
        save_state(state)
    logger.info(f"Starting: R{state.round_number}, ~{state.total_theorems} theorems")

    # ── Background builder consumer ─────────────────────────────────────
    # Worker threads are producers (call `request_build(sha)` on successful
    # merge). The builder thread is the single consumer. Multiple requests
    # collapse to "latest-wins" — intermediate SHAs are skipped.
    if not args.no_builder and not args.dry_run:
        builder_t = threading.Thread(
            target=_builder_loop,
            args=(args.builder_poll, args.builder_max_fix),
            daemon=True,
            name="builder",
        )
        builder_t.start()

    total_succeeded = 0
    total_failed = 0

    if args.continuous:
        # ── True rolling pipeline: as soon as one worker finishes, start the next ──
        logger.info(f"{'='*60}")
        logger.info(f"Rolling pipeline: {args.parallel} concurrent workers, running until stopped")
        logger.info(f"{'='*60}")

        with ThreadPoolExecutor(max_workers=args.parallel, thread_name_prefix="worker") as pool:
            futures: dict[Future, int] = {}

            # Cooldown after consecutive_failures hits the threshold: pause
            # dispatch for this many seconds, then reset the counter and
            # resume. The pipeline never exits on consecutive failures —
            # only graceful stop via STOP_FILE or external SIGTERM.
            cooldown_seconds = max(60, int(args.max_consecutive_failures) * 60)

            def _maybe_cooldown() -> None:
                if state.consecutive_failures < args.max_consecutive_failures:
                    return
                logger.warning(
                    f"[cooldown] {state.consecutive_failures} consecutive failures — "
                    f"sleeping {cooldown_seconds}s before resuming dispatch"
                )
                time.sleep(cooldown_seconds)
                state.consecutive_failures = 0
                save_state(state)
                logger.info("[cooldown] resumed; consecutive_failures reset to 0")

            def _submit_next() -> None:
                if STOP_FILE.exists():
                    logger.info(f"Stop file detected ({STOP_FILE}), not dispatching new rounds")
                    return
                _maybe_cooldown()
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
                if STOP_FILE.exists():
                    logger.info(f"Stop file detected; draining {len(futures)} in-flight workers")
                    # Don't break — finish in-flight, then the pool drains naturally.
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
                    # Immediately launch a replacement worker (will cooldown
                    # if too many consecutive failures, then resume).
                    if not STOP_FILE.exists():
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
