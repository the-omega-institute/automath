#!/usr/bin/env python3
"""Lean4 Codex-First formalization automation.

Replicates the lean4-codex-formalize.md workflow as a standalone Python script:
  Phase B: codex exec picks 3 formalization targets
  Gate:    validates target quality (count, difficulty, chapter diversity)
  Phase C: codex exec implements + compiles + commits + registers + pushes
  Phase D: verifies new commits via git log, then loops

Usage:
  python3 lean4/scripts/codex_formalize.py                  # run one round
  python3 lean4/scripts/codex_formalize.py --rounds 5       # run 5 rounds
  python3 lean4/scripts/codex_formalize.py --continuous      # run until stopped
  python3 lean4/scripts/codex_formalize.py --dry-run         # show prompts, don't call codex
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
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

SCRIPT_DIR = Path(__file__).resolve().parent
LEAN_ROOT = SCRIPT_DIR.parent                        # lean4/
REPO_ROOT = LEAN_ROOT.parent                         # automath/
IMPL_PLAN = LEAN_ROOT / "IMPLEMENTATION_PLAN.md"
OMEGA_ROOT = LEAN_ROOT / "Omega"
OMEGA_LEAN = LEAN_ROOT / "Omega.lean"

LOG_DIR = LEAN_ROOT / "scripts" / "logs"

# Codex CLI discovery
CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------

LOG_DIR.mkdir(parents=True, exist_ok=True)

log_file = LOG_DIR / f"codex_formalize_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler(str(log_file), encoding="utf-8"),
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
class PhaseB_Result:
    raw_output: str = ""
    targets: list[dict] = field(default_factory=list)
    success: bool = False


@dataclass
class PhaseC_Result:
    raw_output: str = ""
    new_commits: list[str] = field(default_factory=list)
    success: bool = False


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def run_cmd(
    cmd: list[str],
    *,
    cwd: Optional[Path] = None,
    timeout: int = 120,
    check: bool = False,
) -> subprocess.CompletedProcess:
    """Run a shell command and return the result."""
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


def git_log_oneline(n: int = 5) -> list[str]:
    """Return the last n commit one-liners."""
    result = run_cmd(["git", "log", f"--oneline", f"-{n}"], cwd=REPO_ROOT)
    return [line.strip() for line in result.stdout.strip().splitlines() if line.strip()]


def git_log_last_timestamp() -> Optional[str]:
    """Return ISO timestamp of the most recent commit."""
    result = run_cmd(
        ["git", "log", "--oneline", "-1", "--format=%ci"],
        cwd=REPO_ROOT,
    )
    return result.stdout.strip() or None


def read_impl_plan_header(lines: int = 30) -> str:
    """Read the first N lines of IMPLEMENTATION_PLAN.md."""
    if not IMPL_PLAN.exists():
        return "(IMPLEMENTATION_PLAN.md not found)"
    with open(IMPL_PLAN, "r", encoding="utf-8") as f:
        return "".join(f.readline() for _ in range(lines))


def parse_round_from_plan(text: str) -> int:
    """Extract the current round number from IMPLEMENTATION_PLAN header."""
    m = re.search(r"round_count\s*=\s*R?(\d+)", text)
    if m:
        return int(m.group(1))
    m = re.search(r"轮次\s*\|\s*R(\d+)", text)
    if m:
        return int(m.group(1))
    return 0


def parse_coverage_from_plan(text: str) -> float:
    """Extract coverage percentage from IMPLEMENTATION_PLAN header."""
    m = re.search(r"coverage_rate_registry.*?([0-9.]+)%", text, re.IGNORECASE)
    if m:
        return float(m.group(1))
    return 0.0


def count_lean_theorems() -> int:
    """Quick count of theorem/lemma declarations in lean4/Omega/."""
    count = 0
    for path in OMEGA_ROOT.rglob("*.lean"):
        text = path.read_text(encoding="utf-8", errors="replace")
        count += len(re.findall(r"^\s*(?:theorem|lemma)\s+", text, re.MULTILINE))
    return count


# ---------------------------------------------------------------------------
# Codex CLI invocation
# ---------------------------------------------------------------------------

def codex_exec(
    prompt: str,
    *,
    timeout_seconds: int = 1800,
    output_file: Optional[Path] = None,
    model: Optional[str] = None,
    dry_run: bool = False,
) -> str:
    """
    Call `codex exec` with the given prompt.

    The prompt is written to a temp file and piped via stdin to avoid
    shell escaping issues. stdin is redirected from /dev/null after the
    prompt (subprocess.DEVNULL handles this automatically when we pass
    the prompt as the positional argument and use a temp file for long
    prompts).
    """
    if dry_run:
        logger.info("[DRY RUN] Would call codex exec with prompt:\n"
                     f"{prompt[:500]}{'...' if len(prompt) > 500 else ''}")
        return "(dry run -- no output)"

    if not Path(CODEX_PATH).exists() and not shutil.which("codex"):
        raise FileNotFoundError(
            f"Codex CLI not found at {CODEX_PATH} and not in PATH. "
            "Install via: npm install -g @anthropic-ai/codex"
        )

    codex_bin = CODEX_PATH if Path(CODEX_PATH).exists() else shutil.which("codex")

    # Write prompt to temp file
    with tempfile.NamedTemporaryFile(
        mode="w",
        suffix=".txt",
        prefix="codex_prompt_",
        delete=False,
        encoding="utf-8",
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
        "-C", str(REPO_ROOT),
        "-o", out_file,
    ]
    if model:
        cmd.extend(["-m", model])
    # Read prompt from stdin via the temp file
    cmd.append("-")

    logger.info(f"Calling codex exec (timeout={timeout_seconds}s)...")
    start = time.monotonic()

    try:
        with open(prompt_file, "r", encoding="utf-8") as pf:
            result = subprocess.run(
                cmd,
                stdin=pf,
                capture_output=True,
                text=True,
                timeout=timeout_seconds + 30,  # extra buffer
                cwd=str(REPO_ROOT),
            )
    except subprocess.TimeoutExpired:
        logger.warning(f"Codex exec timed out after {timeout_seconds}s")
        return "(timeout)"
    finally:
        elapsed = time.monotonic() - start
        logger.info(f"Codex exec completed in {elapsed:.1f}s (rc={result.returncode if 'result' in dir() else '?'})")
        os.unlink(prompt_file)

    # Read output
    output = ""
    try:
        if os.path.exists(out_file) and os.path.getsize(out_file) > 0:
            with open(out_file, "r", encoding="utf-8") as f:
                output = f.read()
        else:
            # Fallback to stdout
            output = result.stdout or ""
    finally:
        if output_file is None:
            os.unlink(out_file)

    if result.stderr:
        logger.debug(f"Codex stderr: {result.stderr[:500]}")

    return output


# ---------------------------------------------------------------------------
# Phase B: Target Selection
# ---------------------------------------------------------------------------

def build_phase_b_prompt(state: RoundState) -> str:
    """Build the prompt for Phase B (target selection)."""
    recent = "\n".join(state.recent_commits[:5]) if state.recent_commits else "(none)"

    return textwrap.dedent(f"""\
        You are the target-selection phase for Lean4 formalization round R{state.round_number + 1}.

        ## Project Layout
        - lean4/Omega/ — Lean4 code (Omega library, depends on mathlib)
        - theory/ — papers in LaTeX
        - lean4/IMPLEMENTATION_PLAN.md — tracking file
        - Current round: R{state.round_number}, next: R{state.round_number + 1}
        - Current theorem count: ~{state.total_theorems}
        - Recent commits:
        {recent}

        ## Task
        Select 3 formalization targets for R{state.round_number + 1}.

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
        For each target, output a JSON block:

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
            }},
            ...
          ]
        }}
        ```

        You MUST grep to confirm each target does not already exist.
        Do NOT guess mathlib API names.
        Do NOT pick targets that are already implemented.
    """)


def parse_phase_b_output(raw: str) -> PhaseB_Result:
    """Parse the Phase B codex output to extract targets."""
    result = PhaseB_Result(raw_output=raw)

    # Try to find JSON block
    json_match = re.search(r"```json\s*(\{.*?\})\s*```", raw, re.DOTALL)
    if json_match:
        try:
            data = json.loads(json_match.group(1))
            result.targets = data.get("targets", [])
        except json.JSONDecodeError:
            logger.warning("Failed to parse Phase B JSON output")

    # Fallback: try to find any JSON object with "targets" key
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
    """
    Validate Phase B targets against gate criteria:
    - At least 3 targets (or at least 1 if we're being lenient)
    - At least 1 medium difficulty
    - Not all from the same chapter
    """
    if len(targets) < 1:
        return False, "No targets found"

    difficulties = [t.get("difficulty", "low") for t in targets]
    chapters = set(t.get("chapter", "unknown") for t in targets)

    issues = []

    if len(targets) < 3:
        issues.append(f"Only {len(targets)} targets (want 3)")

    has_medium = any(d in ("medium", "high") for d in difficulties)
    if not has_medium:
        issues.append("No medium/high difficulty target")

    if len(targets) >= 3 and len(chapters) <= 1:
        issues.append(f"All targets from same chapter: {chapters}")

    if issues:
        return False, "; ".join(issues)

    return True, "Gate passed"


# ---------------------------------------------------------------------------
# Phase C: Implementation + Compile + Commit + Register + Push
# ---------------------------------------------------------------------------

def build_phase_c_prompt(state: RoundState, targets: list[dict]) -> str:
    """Build the prompt for Phase C (full implementation flow)."""
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
        Implement Lean4 theorems + compile + commit + register + push. Complete in one pass.

        ## Round R{state.round_number + 1}

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
        git commit -m "R{state.round_number + 1}: [brief description of what was proved]

        Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>"
        ```

        ## Step 4: Update tracking + annotate
        - Update lean4/IMPLEMENTATION_PLAN.md with new round info
        - Add \\leanverified{{theorem_name}} to the corresponding .tex files
          (find them via the paper_label, escape underscores as \\_)

        ## Step 5: Git commit registration + push
        ```bash
        git add lean4/IMPLEMENTATION_PLAN.md theory/
        git commit -m "Register R{state.round_number + 1}: [brief description]

        Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>"
        git push
        ```

        ## Completion Contract
        - No sorry / admit / axiom; lake build must pass with zero errors
        - Must complete all 5 steps; if a theorem is stuck, skip it and continue
        - After each theorem, verify with lean_diagnostic_messages
        - Tactic failure: auto-try next; compile error: auto-fix up to 3 rounds
        - Push failure: pull --rebase and retry
        - Implementation changes: only in lean4/Omega/
        - Registration changes: only in IMPLEMENTATION_PLAN.md and theory/
        - Do NOT refactor or delete existing code
    """)


def parse_phase_c_output(raw: str) -> PhaseC_Result:
    """Parse Phase C output to detect new commits."""
    result = PhaseC_Result(raw_output=raw)

    # Look for commit hashes in the output
    commit_hashes = re.findall(r"[0-9a-f]{7,40}", raw)
    # Filter to plausible short hashes
    result.new_commits = list(dict.fromkeys(
        h for h in commit_hashes if 7 <= len(h) <= 12
    ))[:10]

    # Check for success indicators
    success_indicators = [
        "git push",
        "lake build",
        "pushed",
        "commit",
        "Register R",
    ]
    result.success = any(ind.lower() in raw.lower() for ind in success_indicators)

    return result


# ---------------------------------------------------------------------------
# Phase D: Verification
# ---------------------------------------------------------------------------

def verify_round(pre_commits: list[str]) -> tuple[bool, list[str]]:
    """Check if new commits appeared since Phase C started."""
    post_commits = git_log_oneline(5)

    new = []
    for c in post_commits:
        if c not in pre_commits:
            new.append(c)

    if new:
        logger.info(f"Phase D: {len(new)} new commit(s) detected:")
        for c in new:
            logger.info(f"  {c}")
        return True, new
    else:
        logger.warning("Phase D: No new commits detected")
        return False, []


# ---------------------------------------------------------------------------
# State persistence
# ---------------------------------------------------------------------------

STATE_FILE = LOG_DIR / "formalize_state.json"


def load_state() -> RoundState:
    """Load persistent state from disk, or read from IMPLEMENTATION_PLAN."""
    if STATE_FILE.exists():
        try:
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            return RoundState(**data)
        except Exception:
            logger.warning("Failed to load state file, rebuilding from IMPLEMENTATION_PLAN")

    # Bootstrap from IMPLEMENTATION_PLAN
    plan_text = read_impl_plan_header(30)
    return RoundState(
        round_number=parse_round_from_plan(plan_text),
        total_theorems=count_lean_theorems(),
        recent_commits=git_log_oneline(5),
    )


def save_state(state: RoundState) -> None:
    """Persist state to disk."""
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump({
            "round_number": state.round_number,
            "coverage_pct": state.coverage_pct,
            "total_theorems": state.total_theorems,
            "recent_commits": state.recent_commits[:10],
            "consecutive_failures": state.consecutive_failures,
        }, f, indent=2)


# ---------------------------------------------------------------------------
# Round log
# ---------------------------------------------------------------------------

def save_round_log(
    round_num: int,
    phase_b: PhaseB_Result,
    phase_c: PhaseC_Result,
    new_commits: list[str],
    success: bool,
) -> Path:
    """Save detailed round log to disk."""
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
# Main loop
# ---------------------------------------------------------------------------

def run_round(
    state: RoundState,
    *,
    dry_run: bool = False,
    model: Optional[str] = None,
    phase_b_timeout: int = 1800,
    phase_c_timeout: int = 3600,
    gate_retries: int = 1,
) -> bool:
    """
    Execute one formalization round.
    Returns True if the round produced new commits.
    """
    next_round = state.round_number + 1
    logger.info(f"{'='*60}")
    logger.info(f"Starting round R{next_round}")
    logger.info(f"Current state: {state.total_theorems} theorems, "
                f"consecutive_failures={state.consecutive_failures}")
    logger.info(f"{'='*60}")

    # Snapshot pre-round commits
    pre_commits = git_log_oneline(10)

    # ── Phase B: Target Selection ──────────────────────────────────
    logger.info("Phase B: Target selection...")
    phase_b_prompt = build_phase_b_prompt(state)
    phase_b_raw = codex_exec(
        phase_b_prompt,
        timeout_seconds=phase_b_timeout,
        model=model,
        dry_run=dry_run,
    )
    phase_b = parse_phase_b_output(phase_b_raw)

    if not phase_b.success:
        logger.error(f"Phase B failed: no targets extracted from codex output "
                     f"({len(phase_b.raw_output)} chars)")
        logger.debug(f"Phase B raw output: {phase_b.raw_output[:1000]}")
        save_round_log(next_round, phase_b, PhaseC_Result(), [], False)
        return False

    logger.info(f"Phase B: {len(phase_b.targets)} target(s) extracted")
    for i, t in enumerate(phase_b.targets, 1):
        logger.info(f"  Target {i}: {t.get('lean_name', '?')} "
                     f"({t.get('difficulty', '?')}, {t.get('chapter', '?')})")

    # ── Gate Check ─────────────────────────────────────────────────
    gate_ok, gate_msg = gate_check(phase_b.targets)
    if not gate_ok:
        logger.warning(f"Gate check failed: {gate_msg}")
        if gate_retries > 0:
            logger.info("Retrying Phase B with stricter prompt...")
            # Could add retry logic here; for now proceed with what we have
            logger.info("Proceeding with available targets despite gate failure")
        else:
            save_round_log(next_round, phase_b, PhaseC_Result(), [], False)
            return False
    else:
        logger.info(f"Gate check: {gate_msg}")

    # ── Phase C: Implementation ────────────────────────────────────
    logger.info("Phase C: Implementation + compile + commit + register + push...")
    phase_c_prompt = build_phase_c_prompt(state, phase_b.targets)
    phase_c_raw = codex_exec(
        phase_c_prompt,
        timeout_seconds=phase_c_timeout,
        model=model,
        dry_run=dry_run,
    )
    phase_c = parse_phase_c_output(phase_c_raw)

    if not phase_c.success:
        logger.warning(f"Phase C may have failed: no success indicators in output "
                       f"({len(phase_c.raw_output)} chars)")

    # ── Phase D: Verification ──────────────────────────────────────
    logger.info("Phase D: Verification...")
    if dry_run:
        logger.info("[DRY RUN] Skipping verification")
        new_commits = []
        success = True
    else:
        success, new_commits = verify_round(pre_commits)

    # ── Update state ───────────────────────────────────────────────
    if success and new_commits:
        state.round_number = next_round
        state.total_theorems = count_lean_theorems()
        state.recent_commits = git_log_oneline(5)
        state.consecutive_failures = 0
        logger.info(f"Round R{next_round} SUCCESS: {len(new_commits)} new commit(s), "
                     f"total theorems now ~{state.total_theorems}")
    else:
        state.consecutive_failures += 1
        logger.warning(f"Round R{next_round} FAILED: consecutive_failures="
                       f"{state.consecutive_failures}")

        # Cleanup if needed
        if not dry_run:
            result = run_cmd(["git", "status", "--short"], cwd=REPO_ROOT)
            if result.stdout.strip():
                logger.info(f"Dirty working tree:\n{result.stdout[:500]}")

    save_state(state)
    log_path = save_round_log(next_round, phase_b, phase_c, new_commits, success)
    logger.info(f"Round log saved: {log_path}")

    return success and bool(new_commits)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Lean4 Codex-First formalization automation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
            Examples:
              python3 lean4/scripts/codex_formalize.py                    # one round
              python3 lean4/scripts/codex_formalize.py --rounds 5         # five rounds
              python3 lean4/scripts/codex_formalize.py --continuous       # until stopped
              python3 lean4/scripts/codex_formalize.py --dry-run          # preview only
              python3 lean4/scripts/codex_formalize.py --model o3         # use specific model
        """),
    )
    parser.add_argument(
        "--rounds", "-n",
        type=int,
        default=1,
        help="Number of rounds to run (default: 1)",
    )
    parser.add_argument(
        "--continuous",
        action="store_true",
        help="Run continuously until stopped or 3 consecutive failures",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show prompts without calling codex",
    )
    parser.add_argument(
        "--model", "-m",
        type=str,
        default=None,
        help="Model override for codex exec (e.g. o3, o4-mini, claude-sonnet-4-20250514)",
    )
    parser.add_argument(
        "--phase-b-timeout",
        type=int,
        default=1800,
        help="Timeout for Phase B in seconds (default: 1800)",
    )
    parser.add_argument(
        "--phase-c-timeout",
        type=int,
        default=3600,
        help="Timeout for Phase C in seconds (default: 3600)",
    )
    parser.add_argument(
        "--max-consecutive-failures",
        type=int,
        default=3,
        help="Stop after N consecutive failures (default: 3)",
    )
    parser.add_argument(
        "--reset-state",
        action="store_true",
        help="Reset persistent state and re-read from IMPLEMENTATION_PLAN",
    )
    parser.add_argument(
        "--status",
        action="store_true",
        help="Print current state and exit",
    )
    args = parser.parse_args()

    # ── Status ─────────────────────────────────────────────────────
    if args.status:
        state = load_state()
        print(f"Round:                 R{state.round_number}")
        print(f"Total theorems:        ~{state.total_theorems}")
        print(f"Consecutive failures:  {state.consecutive_failures}")
        print(f"Recent commits:")
        for c in state.recent_commits[:5]:
            print(f"  {c}")
        print(f"Codex CLI:             {CODEX_PATH}")
        print(f"Log directory:         {LOG_DIR}")
        print(f"State file:            {STATE_FILE}")
        return 0

    # ── Reset ──────────────────────────────────────────────────────
    if args.reset_state and STATE_FILE.exists():
        STATE_FILE.unlink()
        logger.info("State file deleted, will re-read from IMPLEMENTATION_PLAN")

    # ── Preflight ──────────────────────────────────────────────────
    codex_bin = CODEX_PATH if Path(CODEX_PATH).exists() else shutil.which("codex")
    if not codex_bin and not args.dry_run:
        logger.error(f"Codex CLI not found. Searched: {CODEX_PATH}, PATH")
        return 1
    logger.info(f"Codex CLI: {codex_bin}")

    # Check git status
    result = run_cmd(["git", "status", "--short"], cwd=REPO_ROOT)
    if result.stdout.strip():
        logger.warning(f"Working tree is dirty:\n{result.stdout[:300]}")

    # ── Load state ─────────────────────────────────────────────────
    state = load_state()
    logger.info(f"Starting state: R{state.round_number}, "
                f"~{state.total_theorems} theorems")

    # ── Run ────────────────────────────────────────────────────────
    max_rounds = 999999 if args.continuous else args.rounds
    rounds_completed = 0
    rounds_succeeded = 0

    for i in range(max_rounds):
        if state.consecutive_failures >= args.max_consecutive_failures:
            logger.error(
                f"Stopping: {state.consecutive_failures} consecutive failures "
                f"(limit: {args.max_consecutive_failures})"
            )
            break

        success = run_round(
            state,
            dry_run=args.dry_run,
            model=args.model,
            phase_b_timeout=args.phase_b_timeout,
            phase_c_timeout=args.phase_c_timeout,
        )

        rounds_completed += 1
        if success:
            rounds_succeeded += 1

        # Brief pause between rounds to avoid hammering
        if i < max_rounds - 1 and not args.dry_run:
            logger.info("Waiting 10s before next round...")
            time.sleep(10)

    # ── Summary ────────────────────────────────────────────────────
    logger.info(f"{'='*60}")
    logger.info(f"Session complete: {rounds_completed} round(s), "
                f"{rounds_succeeded} succeeded, "
                f"{rounds_completed - rounds_succeeded} failed")
    logger.info(f"Final state: R{state.round_number}, "
                f"~{state.total_theorems} theorems")
    logger.info(f"Logs: {LOG_DIR}")
    logger.info(f"{'='*60}")

    return 0 if rounds_succeeded > 0 or args.dry_run else 1


if __name__ == "__main__":
    raise SystemExit(main())
