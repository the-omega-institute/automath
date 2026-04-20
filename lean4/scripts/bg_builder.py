#!/usr/bin/env python3
"""Background full-build watcher for lean4-codex-auto-dev.

Design (方案 B):
  - The formalization pipeline (codex_formalize.py) commits rounds based
    on codex's per-file `lake env lean <file>` checks only. It does NOT
    run a full `lake build`.
  - This watcher loops: fetch origin; if base branch tip changed, run
    `lake build` once on that tip. If multiple commits accumulated during
    a build, the next loop skips straight to the latest — never builds
    stale intermediates.
  - On build failure, spawn a codex `fix` round in a worktree at the
    broken tip, feed it the build log, let codex commit + push the fix.
    Repeat up to --max-fix-attempts. If all attempts fail, record the
    broken SHA and move on (the watcher will re-attempt when a new
    commit lands).

Not a pipeline orchestrator — it's a single-process cleanup loop that
runs alongside codex_formalize.py.

Usage:
    python3 lean4/scripts/bg_builder.py                 # run indefinitely
    python3 lean4/scripts/bg_builder.py --once          # one iteration
    python3 lean4/scripts/bg_builder.py --poll 30       # fetch every 30s
    python3 lean4/scripts/bg_builder.py --max-fix-attempts 3
"""

from __future__ import annotations

import argparse
import logging
import os
import shutil
import subprocess
import sys
import tempfile
import textwrap
import time
from datetime import datetime
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
LEAN_ROOT = SCRIPT_DIR.parent                 # lean4/
REPO_ROOT = LEAN_ROOT.parent                  # automath/
LOG_DIR = LEAN_ROOT / "scripts" / "logs"
BUILDER_LOG_DIR = LOG_DIR / "bg_builder"
WORKTREE_DIR = REPO_ROOT / ".worktrees"
BASE_BRANCH = "lean4-codex-auto-dev"
CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"
BROKEN_SHA_FILE = BUILDER_LOG_DIR / "broken_shas.txt"
STOP_FILE = REPO_ROOT / ".bg_builder.stop"


BUILDER_LOG_DIR.mkdir(parents=True, exist_ok=True)

_log_path = BUILDER_LOG_DIR / f"bg_builder_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler(str(_log_path), encoding="utf-8"),
    ],
)
logger = logging.getLogger("bg-builder")


def run(cmd: list[str], *, cwd: Path | None = None, timeout: int = 120,
        capture: bool = True) -> subprocess.CompletedProcess:
    kw: dict = {"cwd": str(cwd or REPO_ROOT), "timeout": timeout,
                "stdin": subprocess.DEVNULL}
    if capture:
        kw["capture_output"] = True
        kw["text"] = True
    return subprocess.run(cmd, **kw)


def git_origin_tip() -> str:
    run(["git", "fetch", "origin", BASE_BRANCH], timeout=60)
    r = run(["git", "rev-parse", f"origin/{BASE_BRANCH}"])
    return r.stdout.strip()


def read_broken_shas() -> set[str]:
    if not BROKEN_SHA_FILE.exists():
        return set()
    try:
        return set(l.strip() for l in BROKEN_SHA_FILE.read_text().splitlines() if l.strip())
    except Exception:
        return set()


def record_broken_sha(sha: str, reason: str) -> None:
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    with open(BROKEN_SHA_FILE, "a", encoding="utf-8") as f:
        f.write(f"{sha}\t{ts}\t{reason}\n")


def lake_build(worktree: Path, log_file: Path, timeout: int = 7200) -> tuple[bool, str]:
    """Run `lake build` in `worktree`, streaming output to `log_file`.
    Returns (ok, tail_lines)."""
    with open(log_file, "w", encoding="utf-8") as lf:
        lf.write(f"# lake build at {datetime.now().isoformat()}\n")
        lf.write(f"# worktree: {worktree}\n\n")
        lf.flush()
        try:
            r = subprocess.run(
                ["lake", "build"],
                cwd=str(worktree / "lean4"),
                stdout=lf, stderr=subprocess.STDOUT,
                timeout=timeout, stdin=subprocess.DEVNULL,
            )
            ok = r.returncode == 0
        except subprocess.TimeoutExpired:
            lf.write("\n# TIMEOUT\n")
            ok = False
    # Extract tail for quick logging
    try:
        lines = log_file.read_text(encoding="utf-8").splitlines()
    except Exception:
        lines = []
    tail = "\n".join(lines[-40:])
    return ok, tail


def ensure_main_worktree_tip() -> Path:
    """Make sure the local checkout is on BASE_BRANCH and up to date with
    origin. Returns REPO_ROOT (the main checkout, used as the build root)."""
    run(["git", "checkout", BASE_BRANCH], timeout=60)
    run(["git", "merge", "--ff-only", f"origin/{BASE_BRANCH}"], timeout=60)
    return REPO_ROOT


def make_fix_worktree(sha: str) -> Path:
    """Create a temporary worktree at `sha` on a `fix-<sha8>` branch."""
    WORKTREE_DIR.mkdir(parents=True, exist_ok=True)
    branch = f"fix-{sha[:8]}"
    wt_path = WORKTREE_DIR / f"fix_{sha[:8]}"
    # Clean any stale copy.
    if wt_path.exists():
        run(["git", "worktree", "remove", "--force", str(wt_path)], timeout=60)
        if wt_path.exists():
            shutil.rmtree(wt_path, ignore_errors=True)
    run(["git", "branch", "-D", branch], timeout=30)
    r = run(["git", "worktree", "add", "-b", branch, str(wt_path), sha], timeout=120)
    if r.returncode != 0:
        raise RuntimeError(f"worktree add failed: {r.stderr}")
    # Symlink packages for shared mathlib cache; APFS-COW build/config.
    src = LEAN_ROOT / ".lake"
    dst = wt_path / "lean4" / ".lake"
    dst.mkdir(parents=True, exist_ok=True)
    if (src / "packages").exists():
        try:
            (dst / "packages").symlink_to(src / "packages")
        except FileExistsError:
            pass
    for sub in ("build", "config"):
        s = src / sub
        d = dst / sub
        if s.exists() and not d.exists():
            subprocess.run(["cp", "-Rc", str(s), str(d)],
                           timeout=600, check=False, stdin=subprocess.DEVNULL)
    return wt_path


def remove_fix_worktree(wt: Path) -> None:
    branch = f"fix-{wt.name.split('_',1)[1]}"
    run(["git", "worktree", "remove", "--force", str(wt)], timeout=60)
    pkg = wt / "lean4" / ".lake" / "packages"
    if pkg.is_symlink():
        try:
            pkg.unlink()
        except Exception:
            pass
    if wt.exists():
        shutil.rmtree(wt, ignore_errors=True)
    run(["git", "branch", "-D", branch], timeout=30)


def codex_fix(worktree: Path, build_log: Path, *, timeout: int = 3600) -> bool:
    """Ask codex to fix the broken build in `worktree`. Success means
    codex produced a commit on the fix branch that we were able to push.
    Does NOT re-run lake build here — the main loop will re-verify."""
    codex_bin = CODEX_PATH if Path(CODEX_PATH).exists() else shutil.which("codex")
    if not codex_bin:
        logger.error("codex CLI not found")
        return False
    # Tail the log so the prompt stays small.
    try:
        log_text = build_log.read_text(encoding="utf-8")
    except Exception:
        log_text = "(build log unreadable)"
    log_tail = "\n".join(log_text.splitlines()[-200:])

    prompt = textwrap.dedent(f"""\
        The full `lake build` is failing on branch `lean4-codex-auto-dev`.
        Fix the compilation errors so `cd lean4 && lake build` passes clean.

        ## Constraints
        - You are on a `fix-*` branch at the broken tip.
        - Work only inside lean4/Omega/. Do NOT touch code outside that.
        - No `sorry`, no `admit`, no new `axiom`.
        - Do NOT use `native_decide` on large enumerations (m ≥ 9).
        - Keep changes minimal: edit only what's needed to unstuck build.
        - After the edit loop, commit the fix and push to origin:
            git add lean4/Omega/
            git commit -m "fix: repair lake build after <brief>"
            git push origin HEAD:lean4-codex-auto-dev
          (Push may be rejected if origin moved — rebase onto
           origin/lean4-codex-auto-dev, re-verify with
           `lake env lean <file>.lean`, then push again.)

        ## Build log tail (last 200 lines)
        ```
        {log_tail}
        ```

        ## Your job
        1. Read the errors
        2. Identify the offending file(s) and root cause
        3. Patch them (respect signature integrity; if an existing theorem
           broke because its signature is wrong, prefer reverting the
           signature change rather than weakening the theorem)
        4. Commit + push
        Do NOT run a full `lake build` — use per-file `lake env lean <file>`
        to confirm the patched file elaborates.
    """)

    tmp = tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False,
                                     encoding="utf-8")
    try:
        tmp.write(prompt)
        tmp.close()
        logger.info(f"codex fix: invoking codex exec (worktree={worktree.name})")
        with open(tmp.name, "r") as pf:
            r = subprocess.run(
                ["timeout", str(timeout), codex_bin, "exec",
                 "--dangerously-bypass-approvals-and-sandbox",
                 "-C", str(worktree)],
                stdin=pf, capture_output=True, text=True,
                timeout=timeout + 30, cwd=str(worktree),
            )
        logger.info(f"codex fix: exit rc={r.returncode}")
        # Save full codex output for debugging.
        fix_log = BUILDER_LOG_DIR / f"fix_{worktree.name}_{datetime.now().strftime('%H%M%S')}.out.txt"
        with open(fix_log, "w", encoding="utf-8") as f:
            f.write(r.stdout or "")
            f.write("\n--- stderr ---\n")
            f.write(r.stderr or "")
        # Success = new commit on branch
        head = run(["git", "rev-parse", "HEAD"], cwd=worktree).stdout.strip()
        base = run(["git", "rev-parse", f"origin/{BASE_BRANCH}"], cwd=worktree).stdout.strip()
        if head != base:
            logger.info(f"codex fix: produced new commit {head[:8]}")
            return True
        logger.warning("codex fix: no new commit produced")
        return False
    finally:
        try:
            os.unlink(tmp.name)
        except Exception:
            pass


def attempt_fix(sha: str, build_log: Path, max_attempts: int) -> bool:
    for attempt in range(1, max_attempts + 1):
        logger.info(f"fix attempt {attempt}/{max_attempts} for {sha[:8]}")
        try:
            wt = make_fix_worktree(sha)
        except Exception as exc:
            logger.error(f"fix worktree creation failed: {exc}")
            return False
        try:
            fixed = codex_fix(wt, build_log)
            if not fixed:
                continue
            # Verify the fix by building inside the worktree.
            vbuild_log = BUILDER_LOG_DIR / f"fix_verify_{wt.name}_{attempt}.txt"
            ok, tail = lake_build(wt, vbuild_log)
            if not ok:
                logger.warning(f"fix attempt {attempt}: build still failing (log={vbuild_log.name})")
                continue
            # Build passed; codex's push in the prompt may already have
            # landed. Re-check origin to confirm.
            new_tip = git_origin_tip()
            logger.info(f"fix attempt {attempt}: verified build OK; origin tip now {new_tip[:8]}")
            return True
        finally:
            try:
                remove_fix_worktree(wt)
            except Exception:
                pass
    return False


def loop(poll_seconds: float, max_fix_attempts: int) -> None:
    last_built = None
    while not STOP_FILE.exists():
        try:
            tip = git_origin_tip()
        except Exception as exc:
            logger.warning(f"fetch failed: {exc}; sleeping {poll_seconds}s")
            time.sleep(poll_seconds)
            continue

        if tip == last_built:
            time.sleep(poll_seconds)
            continue

        broken = read_broken_shas()
        if tip in broken:
            logger.info(f"{tip[:8]} already recorded as broken; skipping")
            time.sleep(poll_seconds)
            continue

        logger.info(f"building {tip[:8]} (was {str(last_built)[:8] if last_built else 'none'})")
        try:
            ensure_main_worktree_tip()
        except Exception as exc:
            logger.error(f"ff main checkout failed: {exc}")
            time.sleep(poll_seconds)
            continue

        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        build_log = BUILDER_LOG_DIR / f"build_{tip[:8]}_{ts}.txt"
        ok, tail = lake_build(REPO_ROOT, build_log)

        if ok:
            logger.info(f"build PASS for {tip[:8]} (log={build_log.name})")
            last_built = tip
            continue

        logger.error(f"build FAIL for {tip[:8]} (log={build_log.name}); tail:")
        for line in tail.splitlines()[-10:]:
            logger.error(f"  {line}")

        fixed = attempt_fix(tip, build_log, max_fix_attempts)
        if fixed:
            # Skip ahead — next iteration will re-fetch and pick up the fix.
            last_built = None
        else:
            record_broken_sha(tip, f"build_log={build_log.name}")
            last_built = tip   # don't retry until a new commit lands


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--once", action="store_true",
                    help="Run a single iteration and exit")
    ap.add_argument("--poll", type=float, default=60.0,
                    help="Seconds between fetches when idle (default 60)")
    ap.add_argument("--max-fix-attempts", type=int, default=3,
                    help="Max codex fix attempts per broken SHA (default 3)")
    ap.add_argument("--stop", action="store_true",
                    help=f"Create {STOP_FILE.name} to signal the running loop to stop")
    ap.add_argument("--resume", action="store_true",
                    help=f"Remove {STOP_FILE.name}")
    args = ap.parse_args()

    if args.stop:
        STOP_FILE.touch()
        print(f"Created {STOP_FILE}")
        return 0
    if args.resume:
        if STOP_FILE.exists():
            STOP_FILE.unlink()
        print(f"Removed {STOP_FILE}" if not STOP_FILE.exists() else f"{STOP_FILE} still exists")
        return 0

    if args.once:
        try:
            tip = git_origin_tip()
        except Exception as exc:
            logger.error(f"fetch failed: {exc}")
            return 2
        ensure_main_worktree_tip()
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        build_log = BUILDER_LOG_DIR / f"build_{tip[:8]}_{ts}.txt"
        ok, _ = lake_build(REPO_ROOT, build_log)
        if ok:
            logger.info(f"build PASS for {tip[:8]}")
            return 0
        logger.error(f"build FAIL for {tip[:8]}; log={build_log}")
        ok2 = attempt_fix(tip, build_log, args.max_fix_attempts)
        return 0 if ok2 else 1

    logger.info(f"starting bg_builder: poll={args.poll}s, max_fix={args.max_fix_attempts}")
    loop(args.poll, args.max_fix_attempts)
    logger.info("bg_builder stopped")
    return 0


if __name__ == "__main__":
    sys.exit(main())
