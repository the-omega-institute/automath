#!/usr/bin/env python3
"""Community outreach pipeline for GitHub mathematical contributions.

Workflow:
  Stage A  discovery via gh search repos + Codex/Claude candidate review
  Stage B  deep mathematical research, score-gated (>= 8), max 3 rounds
  Stage C  issue drafting in Tolmeton style + Claude review, max 2 rounds
  Stage D  interactive approval gate + gh issue create

The script is modeled after tools/chatgpt-oracle/oracle_pipeline.py:
  - structured logging to stdout + file
  - dataclass-backed JSON state persistence
  - subprocess wrappers for codex / claude / gh / git
  - dry-run support for end-to-end verification
"""

from __future__ import annotations

import argparse
import contextlib
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
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Optional


# ---------------------------------------------------------------------------
# Paths & constants
# ---------------------------------------------------------------------------

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
LOG_DIR = SCRIPT_DIR / "logs"
STATE_DIR = SCRIPT_DIR / "outreach_state"
CANDIDATES_FILE = STATE_DIR / "candidates.json"
PROCESSED_FILE = STATE_DIR / "processed.json"

AUTOMATH_REPO_URL = "https://github.com/the-omega-institute/automath"
AUTOMATH_TRAILER = "**Repo:** https://github.com/the-omega-institute/automath"

# Priority targets: high-value repos with real communities and explicit needs.
# These are checked FIRST before running discovery queries.
PRIORITY_REPOS = [
    "teorth/equational_theories",       # Tao's project, 512 stars, 30 open issues, CONTRIBUTING.md
    "google-deepmind/formal-conjectures",  # DeepMind, 755 stars, explicit contribution paths
]

DISCOVERY_QUERIES = [
    # Focus on repos with actual community (stars >= 5) and recent activity
    '"Lean 4" fibonacci pushed:>=RECENT stars:>=5 archived:false',
    '"Lean 4" "number theory" pushed:>=RECENT stars:>=5 archived:false',
    '"Lean 4" "symbolic dynamics" pushed:>=RECENT stars:>=3 archived:false',
    '"Lean 4" equational pushed:>=RECENT stars:>=3 archived:false',
    '"Lean 4" "formal verification" "conjecture" pushed:>=RECENT stars:>=10 archived:false',
    'Lean mathlib "open problem" pushed:>=RECENT stars:>=5 archived:false',
]

RESEARCH_STANDARD_ZH = """继续深入研究, 结合项目论文PDF分析, 找一些能够惊艳到你的深刻结论链条(禁止同义表述).
请研究到一些有发表价值的结论再结束, 不要挤牙膏.不要重复之前内容.
不要重复其他人已经发表公开的, 要求发现定理、推论、猜想、命题及证明, 可以使用其他人的结论.
不要中间过程结论.请使用顶级数学期刊学术化语言表达, 禁止口语."""

PASS_SCORE = 8
LOW_SCORE_SKIP = 3  # Bug 6 fix: was 5 (gave up too easily). Only skip if score stays < 3 (genuinely hopeless)
LOW_SCORE_STREAK = 3  # Need 3 consecutive low rounds to skip (was 2)
MAX_RESEARCH_ROUNDS = 5  # Bug 6 fix: was 3 (too few). More rounds for deep-dive research
DEEP_MODE_THRESHOLD = 2  # After N rounds below PASS_SCORE, escalate to deep-research mode
MAX_DRAFT_ROUNDS = 2
DEFAULT_TIMEOUT = 1800

IGNORE_PARTS = {
    ".git",
    ".lake",
    ".venv",
    ".mypy_cache",
    ".pytest_cache",
    "__pycache__",
    "build",
    "dist",
    "target",
    "node_modules",
    "agents",
}

FORBIDDEN_PATH_PATTERNS = (
    "~/.claude/",
    "~/.agents/",
    ".claude/skills/",
    "agents/",
)


def _find_binary(name: str, darwin_paths: tuple[str, ...] = ()) -> str:
    found = shutil.which(name)
    if found:
        return found
    if sys.platform == "darwin":
        for candidate in darwin_paths:
            if Path(candidate).exists():
                return candidate
    if sys.platform == "win32":
        cmd = Path.home() / "AppData" / "Roaming" / "npm" / f"{name}.cmd"
        if cmd.exists():
            return str(cmd)
    return name


CODEX_PATH = _find_binary("codex", ("/opt/homebrew/bin/codex", "/usr/local/bin/codex"))
CLAUDE_PATH = _find_binary("claude", ("/opt/homebrew/bin/claude", "/usr/local/bin/claude"))
GH_PATH = _find_binary("gh", ("/opt/homebrew/bin/gh", "/usr/local/bin/gh"))
IS_WINDOWS = sys.platform == "win32"

_state_lock = threading.Lock()


# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------

LOG_DIR.mkdir(parents=True, exist_ok=True)
STATE_DIR.mkdir(parents=True, exist_ok=True)

_log_file = LOG_DIR / f"outreach_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"


class _Utf8StreamHandler(logging.StreamHandler):
    def emit(self, record):
        try:
            msg = self.format(record)
            sys.stdout.buffer.write((msg + "\n").encode("utf-8", errors="replace"))
            sys.stdout.buffer.flush()
        except Exception:
            self.handleError(record)


logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] [%(threadName)s] %(message)s",
    handlers=[
        _Utf8StreamHandler() if IS_WINDOWS else logging.StreamHandler(sys.stdout),
        logging.FileHandler(str(_log_file), encoding="utf-8"),
    ],
)
logger = logging.getLogger("community-outreach")


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------


@dataclass
class RepoState:
    repo: str
    stage: str = "B"
    round: int = 0
    scores: dict[str, list[int]] = field(
        default_factory=lambda: {"codex": [], "claude": [], "final": []}
    )
    findings: list[Any] = field(default_factory=list)
    draft_title: str = ""
    draft_body: str = ""
    action_history: list[dict[str, Any]] = field(default_factory=list)
    timestamps: dict[str, str] = field(default_factory=dict)
    submission_url: str = ""
    error: str = ""

    def log_event(self, stage: str, action: str, **kwargs: Any) -> None:
        now = iso_now()
        self.timestamps["updated_at"] = now
        entry = {
            "timestamp": now,
            "stage": stage,
            "round": kwargs.get("round", self.round),
            "action": action,
            "score": kwargs.get("score", 0),
            "verdict": kwargs.get("verdict", ""),
            "detail": str(kwargs.get("detail", ""))[:20000],  # Bug 5 fix: was 3000, too short for findings
        }
        self.action_history.append(entry)
        self.action_history = self.action_history[-30:]

    def to_dict(self) -> dict[str, Any]:
        return {
            "repo": self.repo,
            "stage": self.stage,
            "round": self.round,
            "scores": self.scores,
            "findings": self.findings,
            "draft_title": self.draft_title,
            "draft_body": self.draft_body,
            "action_history": self.action_history[-30:],
            "timestamps": self.timestamps,
            "submission_url": self.submission_url,
            "error": self.error,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "RepoState":
        state = cls(repo=data["repo"])
        state.stage = data.get("stage", "B")
        state.round = int(data.get("round", 0) or 0)
        raw_scores = data.get("scores", {})
        state.scores = {
            "codex": [coerce_score(x) for x in raw_scores.get("codex", [])],
            "claude": [coerce_score(x) for x in raw_scores.get("claude", [])],
            "final": [coerce_score(x) for x in raw_scores.get("final", [])],
        }
        state.findings = data.get("findings", [])
        state.draft_title = data.get("draft_title", "")
        state.draft_body = data.get("draft_body", "")
        state.action_history = data.get("action_history", [])
        state.timestamps = data.get("timestamps", {})
        state.submission_url = data.get("submission_url", "")
        state.error = data.get("error", "")
        return state


# ---------------------------------------------------------------------------
# State persistence
# ---------------------------------------------------------------------------


def iso_now() -> str:
    return datetime.now().astimezone().isoformat(timespec="seconds")


def repo_slug(repo: str) -> str:
    return repo.replace("/", "_")


def state_file(repo: str) -> Path:
    owner, name = repo.split("/", 1)
    return STATE_DIR / f"{owner}_{name}.json"


def save_state(state: RepoState) -> None:
    with _state_lock:
        state.timestamps.setdefault("created_at", iso_now())
        state.timestamps["updated_at"] = iso_now()
        path = state_file(state.repo)
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w", encoding="utf-8") as handle:
            json.dump(state.to_dict(), handle, indent=2, ensure_ascii=False)


def load_state(repo: str) -> Optional[RepoState]:
    path = state_file(repo)
    if not path.exists():
        return None
    try:
        with open(path, "r", encoding="utf-8") as handle:
            data = json.load(handle)
        return RepoState.from_dict(data)
    except Exception as exc:
        logger.warning("Failed to load state for %s: %s", repo, exc)
        return None


def load_all_states() -> list[RepoState]:
    states: list[RepoState] = []
    for path in sorted(STATE_DIR.glob("*.json")):
        if path.name in {"processed.json", "candidates.json"}:
            continue
        try:
            with open(path, "r", encoding="utf-8") as handle:
                states.append(RepoState.from_dict(json.load(handle)))
        except Exception:
            continue
    return states


def load_processed_repos() -> set[str]:
    processed: set[str] = set()
    if PROCESSED_FILE.exists():
        try:
            data = json.loads(PROCESSED_FILE.read_text(encoding="utf-8"))
            for repo in data.get("repos", []):
                if valid_repo_slug(repo):
                    processed.add(repo)
        except Exception:
            pass
    for state in load_all_states():
        if state.stage in {"DONE", "SKIPPED"} or state.submission_url:
            processed.add(state.repo)
    return processed


def save_processed_repos(repos: set[str], *, dry_run: bool) -> None:
    if dry_run:
        return
    payload = {"updated_at": iso_now(), "repos": sorted(repos)}
    PROCESSED_FILE.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )


def mark_processed(repo: str, *, dry_run: bool) -> None:
    processed = load_processed_repos()
    processed.add(repo)
    save_processed_repos(processed, dry_run=dry_run)


# ---------------------------------------------------------------------------
# Shell helpers
# ---------------------------------------------------------------------------


def run_cmd(
    cmd: list[str],
    *,
    cwd: Optional[Path] = None,
    input_text: Optional[str] = None,
    timeout: int = DEFAULT_TIMEOUT,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd or REPO_ROOT),
        input=input_text,
        capture_output=True,
        text=True,
        timeout=timeout,
        stdin=subprocess.DEVNULL if input_text is None else subprocess.PIPE,
        encoding="utf-8",
        errors="replace",
    )


def ensure_binary(path_or_name: str, label: str) -> str:
    if Path(path_or_name).exists():
        return path_or_name
    found = shutil.which(path_or_name)
    if found:
        return found
    raise RuntimeError(f"{label} CLI not found: {path_or_name}")


def _kill_process_tree(pid: int) -> None:
    """Bug 3 fix: forcefully kill process and all descendants.
    Codex spawns node + codex binary + children; subprocess.run's kill may miss them."""
    try:
        # Try graceful first
        os.killpg(os.getpgid(pid), 15)  # SIGTERM
        time.sleep(2)
        os.killpg(os.getpgid(pid), 9)  # SIGKILL
    except (ProcessLookupError, OSError):
        pass
    # Also kill any orphaned codex exec children of this pid
    try:
        children = subprocess.run(
            ["pgrep", "-P", str(pid)],
            capture_output=True, text=True, timeout=5,
        ).stdout.split()
        for child_pid in children:
            try:
                os.kill(int(child_pid), 9)
            except (ProcessLookupError, ValueError, OSError):
                pass
    except (subprocess.TimeoutExpired, FileNotFoundError):
        pass


def codex_exec(
    prompt: str,
    work_dir: Path,
    timeout: int = DEFAULT_TIMEOUT,
    model: Optional[str] = None,
    dry_run: bool = False,
) -> str:
    """Borrowed from lean4-codex-auto-dev pipeline (PR #37):
    1. Prompt via temp file + shell arg (not stdin pipe) — prevents Codex hang
    2. Shell `timeout` for reliable kill — rc=124 on timeout
    3. `</dev/null` closes stdin — prevents "Reading additional input..." hang
    """
    if dry_run:
        logger.info("[DRY RUN] codex exec in %s", work_dir)
        logger.info("[DRY RUN] prompt preview: %s", prompt[:220].replace("\n", " "))
        return "(dry run)"

    codex_bin = ensure_binary(CODEX_PATH, "codex")

    out_fd, out_file = tempfile.mkstemp(prefix="codex_out_", suffix=".txt")
    os.close(out_fd)
    prompt_fd, prompt_file = tempfile.mkstemp(prefix="codex_prompt_", suffix=".txt")
    os.close(prompt_fd)
    Path(prompt_file).write_text(prompt, encoding="utf-8")

    model_flag = f" -m {model}" if model else ""
    # macOS has gtimeout (from coreutils), Linux has timeout
    timeout_bin = "gtimeout" if shutil.which("gtimeout") else "timeout"
    # Shell command: timeout + codex reads prompt from $(cat file) + stdin closed
    shell_cmd = (
        f'{timeout_bin} {timeout} "{codex_bin}" exec'
        f" --dangerously-bypass-approvals-and-sandbox"
        f' -C "{work_dir}"'
        f' -o "{out_file}"'
        f"{model_flag}"
        f' "$(cat \'{prompt_file}\')" </dev/null'
    )

    start = time.monotonic()
    try:
        result = subprocess.run(
            ["bash", "-c", shell_cmd],
            capture_output=True,
            text=True,
            timeout=timeout + 60,  # Python backup (shell timeout should fire first)
            encoding="utf-8",
            errors="replace",
        )
        rc = result.returncode
        stdout = result.stdout or ""
        stderr = result.stderr or ""
    except subprocess.TimeoutExpired:
        logger.warning("Codex: Python backup timeout after %ss", timeout + 60)
        rc = -1
        stdout, stderr = "", ""
    finally:
        elapsed = time.monotonic() - start
        if rc == 124:
            logger.warning("Codex: shell timeout after %ss", timeout)
        logger.info("Codex exec: %.1fs (rc=%s)", elapsed, rc if rc != 124 else "timeout")
        with contextlib.suppress(OSError):
            os.unlink(prompt_file)

    if rc == 124 or rc == -1:
        with contextlib.suppress(OSError):
            os.unlink(out_file)
        return "(timeout)"

    try:
        if os.path.exists(out_file) and os.path.getsize(out_file) > 0:
            return Path(out_file).read_text(encoding="utf-8")
        if stdout:
            return stdout
        if stderr:
            logger.warning("Codex stderr: %s", stderr[:400])
            return stderr
        return ""
    finally:
        with contextlib.suppress(OSError):
            os.unlink(out_file)


def claude_exec(
    prompt: str,
    *,
    work_dir: Path,
    timeout: int = 900,
    dry_run: bool = False,
) -> str:
    if dry_run:
        logger.info("[DRY RUN] claude exec in %s", work_dir)
        return "(dry run)"

    try:
        claude_bin = ensure_binary(CLAUDE_PATH, "claude")
    except RuntimeError:
        logger.warning("Claude CLI unavailable; falling back to codex")
        return codex_exec(prompt, work_dir=work_dir, timeout=timeout, dry_run=dry_run)

    use_shell = IS_WINDOWS and str(claude_bin).endswith(".cmd")
    start = time.monotonic()
    result: Optional[subprocess.CompletedProcess[str]] = None
    try:
        result = subprocess.run(
            [claude_bin, "-p", "--dangerously-skip-permissions"],
            input=prompt,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(work_dir),
            shell=use_shell,
            encoding="utf-8",
            errors="replace",
        )
    except subprocess.TimeoutExpired:
        logger.warning("Claude CLI timed out after %ss", timeout)
        return "(timeout)"
    finally:
        elapsed = time.monotonic() - start
        rc = result.returncode if result else "?"
        logger.info("Claude exec: %.1fs (rc=%s)", elapsed, rc)

    output = result.stdout if result else ""
    if result and result.returncode != 0 and not output:
        logger.warning("Claude stderr: %s", (result.stderr or "")[:400])
        return codex_exec(prompt, work_dir=work_dir, timeout=timeout, dry_run=dry_run)
    return output or (result.stderr if result else "")


def gh_json(
    args: list[str],
    *,
    cwd: Optional[Path] = None,
    timeout: int = 300,
    dry_run: bool = False,
) -> Any:
    if dry_run:
        return {}
    gh_bin = ensure_binary(GH_PATH, "gh")
    result = run_cmd([gh_bin, *args], cwd=cwd, timeout=timeout)
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or result.stdout.strip() or "gh failed")
    text = result.stdout.strip()
    return json.loads(text) if text else {}


# ---------------------------------------------------------------------------
# Parsing helpers
# ---------------------------------------------------------------------------


def parse_json_from_output(text: str) -> Any:
    """Extract the first JSON object or array from model output."""
    if not text:
        return {}

    fenced = re.finditer(r"```(?:json)?\s*(.*?)\s*```", text, re.DOTALL | re.IGNORECASE)
    for match in fenced:
        candidate = match.group(1).strip()
        parsed = _try_json(candidate)
        if parsed is not None:
            return parsed

    direct = _try_json(text.strip())
    if direct is not None:
        return direct

    for opener in ("{", "["):
        for start in [i for i, ch in enumerate(text) if ch == opener]:
            candidate = _balanced_json_slice(text, start)
            if candidate is None:
                continue
            parsed = _try_json(candidate)
            if parsed is not None:
                return parsed
    return {}


def _try_json(text: str) -> Any:
    with contextlib.suppress(json.JSONDecodeError):
        return json.loads(text)
    return None


def _balanced_json_slice(text: str, start: int) -> Optional[str]:
    opening = text[start]
    closing = "}" if opening == "{" else "]"
    depth = 0
    in_string = False
    escape = False
    for idx in range(start, len(text)):
        ch = text[idx]
        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
            continue
        if ch == opening:
            depth += 1
        elif ch == closing:
            depth -= 1
            if depth == 0:
                return text[start : idx + 1]
    return None


MAIN_PAPER_DIR = REPO_ROOT / "theory" / "2026_golden_ratio_driven_scan_projection_generation_recursive_emergence"
BACKFLOW_DIR = MAIN_PAPER_DIR / "sections" / "appendix" / "outreach_bridges"
BRIDGES_DIR = REPO_ROOT / "theory" / "bridges"


def build_backflow_placement_prompt(state: "RepoState") -> str:
    """Build prompt for Codex to propose WHERE in the paper this research belongs."""
    slug = repo_slug(state.repo)
    target_dir = SCRIPT_DIR / "targets" / slug

    # Collect research artifacts for Codex to scan
    research_doc = ""
    doc_path = target_dir / "research.md"
    if doc_path.exists():
        research_doc = doc_path.read_text(encoding="utf-8")[:6000]

    scripts_list = ""
    if target_dir.exists():
        scripts = [f.name for f in target_dir.iterdir() if f.suffix == ".py"]
        if scripts:
            scripts_list = "\n".join(f"  - {s}" for s in scripts)

    return textwrap.dedent(
        f"""\
        You are deciding WHERE in the Omega paper this research should be placed.

        RESEARCH SUMMARY (from outreach to {state.repo}):
        {research_doc[:4000]}

        SCRIPTS PRODUCED:
        {scripts_list or "  (none)"}

        FINDINGS:
        {json.dumps(state.findings[:5], indent=2, ensure_ascii=False)}

        ═══════════════════════════════════════════════════════════════
        STEP 1: SCAN THE PAPER STRUCTURE
        ═══════════════════════════════════════════════════════════════

        Read the paper's section structure:
        `ls {MAIN_PAPER_DIR}/sections/body/`
        `ls {MAIN_PAPER_DIR}/sections/appendix/`
        `cat {MAIN_PAPER_DIR}/sections/body/main.tex`
        `cat {MAIN_PAPER_DIR}/sections/appendix/main.tex`

        Skim 2-3 body sections that might be related:
        `head -30 {MAIN_PAPER_DIR}/sections/body/<section>/main.tex`

        ═══════════════════════════════════════════════════════════════
        STEP 2: PROPOSE PLACEMENT
        ═══════════════════════════════════════════════════════════════

        Decide:
        - Is this a BODY section (first-class result) or APPENDIX (supporting)?
        - What should the section directory be named?
        - Where in the section order does it fit (after which existing section)?
        - What is the section title for the .tex?

        Return JSON:
        {{
          "placement": "body|appendix",
          "section_dir": "equational_theory_bridge",
          "section_title": "Linear Magma Anti-Implications and the Golden Mean Shift",
          "insert_after": "name of the section it should follow",
          "rationale": "why this placement (1-2 sentences)",
          "bridge_doc_path": "theory/bridges/<topic>/README.md",
          "bridge_doc_title": "title for the GitHub-readable bridge document"
        }}
        """
    )


def build_backflow_tex_prompt(state: "RepoState", placement: dict[str, Any]) -> str:
    """Build prompt for Codex to generate paper-quality .tex from research findings."""
    slug = repo_slug(state.repo)
    target_dir = SCRIPT_DIR / "targets" / slug

    research_doc = ""
    doc_path = target_dir / "research.md"
    if doc_path.exists():
        research_doc = doc_path.read_text(encoding="utf-8")[:8000]

    # Collect proof documents if any
    proof_docs = ""
    for f in sorted(target_dir.iterdir()) if target_dir.exists() else []:
        if f.is_file() and "proof" in f.name.lower() and f.suffix == ".md":
            proof_docs += f"\n\n--- {f.name} ---\n{f.read_text(encoding='utf-8')[:6000]}"

    section_type = placement.get("placement", "appendix")
    section_dir = placement.get("section_dir", slug)
    section_title = placement.get("section_title", f"Bridge to {state.repo}")
    tex_dir = MAIN_PAPER_DIR / "sections" / section_type / section_dir

    return textwrap.dedent(
        f"""\
        Write a paper-quality LaTeX section for the Omega paper.

        SECTION TYPE: {section_type}
        SECTION TITLE: {section_title}
        OUTPUT PATH: {tex_dir}/main.tex

        ═══════════════════════════════════════════════════════════════
        SOURCE MATERIAL (rewrite as proper LaTeX, not copy-paste)
        ═══════════════════════════════════════════════════════════════

        Research document:
        {research_doc[:5000]}

        Proof documents:
        {proof_docs[:5000] if proof_docs else "(none — construct from findings)"}

        ═══════════════════════════════════════════════════════════════
        STYLE REQUIREMENTS
        ═══════════════════════════════════════════════════════════════

        Read an existing section for style reference:
        `cat {MAIN_PAPER_DIR}/sections/{section_type}/$(ls {MAIN_PAPER_DIR}/sections/{section_type}/ | head -1)/main.tex | head -60`

        Match the style exactly:
        - \\documentclass[../../main.tex]{{subfiles}}
        - Proper theorem/lemma/corollary environments
        - No pipeline notes, no "auto-generated" comments
        - Academic mathematical prose, not bullet points
        - Include \\label{{}} for cross-references
        - Reference verification scripts: "verified computationally (see scripts/equational_theory/)"

        Write the COMPLETE .tex file to: {tex_dir}/main.tex
        Create the directory first: `mkdir -p {tex_dir}`

        ═══════════════════════════════════════════════════════════════
        ALSO: Write a GitHub-readable bridge document
        ═══════════════════════════════════════════════════════════════

        Write a polished markdown version to: {BRIDGES_DIR}/{slug.replace('_', '-')}/README.md
        Create dir: `mkdir -p {BRIDGES_DIR}/{slug.replace('_', '-')}`

        This is what gets linked from GitHub issues. It should be:
        - Self-contained and readable without LaTeX
        - Include the main theorem statements and proof sketches
        - Reference the paper section for the formal version
        - Reference the verification scripts

        Return JSON:
        {{
          "tex_path": "path to the .tex file written",
          "bridge_doc_path": "path to the bridge markdown written",
          "sections_written": ["list of theorem/lemma names included"],
          "scripts_referenced": ["list of scripts mentioned"]
        }}
        """
    )


def backflow_to_main_paper(
    state: "RepoState",
    *,
    model: Optional[str] = None,
    dry_run: bool = False,
) -> dict[str, Any]:
    """Two-step backflow: Codex proposes paper placement, Claude reviews, then
    Codex generates paper-quality .tex + bridge markdown doc.

    Returns placement dict with paths to generated files.
    """
    if dry_run or not state.findings:
        return {}

    slug = repo_slug(state.repo)
    logger.info("[%s] Backflow: starting placement analysis", state.repo)

    # Step 1: Codex proposes WHERE in the paper
    placement_raw = codex_exec(
        build_backflow_placement_prompt(state),
        work_dir=REPO_ROOT,
        timeout=600,
        model=model,
        dry_run=dry_run,
    )
    placement = parse_json_from_output(placement_raw)
    if not isinstance(placement, dict) or "placement" not in placement:
        logger.warning("[%s] Backflow: Codex placement failed, using default (appendix)", state.repo)
        placement = {
            "placement": "appendix",
            "section_dir": slug,
            "section_title": f"Bridge to {state.repo.replace('_', ' ')}",
            "insert_after": "",
            "rationale": "default placement (Codex proposal failed)",
        }

    logger.info("[%s] Backflow: Codex proposes %s/%s", state.repo,
                placement.get("placement"), placement.get("section_dir"))

    # Step 2: Claude reviews the placement
    review_raw = claude_exec(
        f"Review this paper placement proposal for outreach findings from {state.repo}.\n\n"
        f"Proposal: {json.dumps(placement, indent=2, ensure_ascii=False)}\n\n"
        f"Findings summary: {json.dumps(state.findings[:3], indent=2, ensure_ascii=False)}\n\n"
        f"Is this the right placement? Check:\n"
        f"1. Body vs appendix: is this result first-class enough for body?\n"
        f"2. Section naming: does it match the paper's conventions?\n"
        f"3. Insert position: does it flow logically?\n\n"
        f"Return JSON: {{\"approved\": true/false, \"revised_placement\": {{...}} if not approved, \"notes\": \"...\"}}",
        work_dir=REPO_ROOT,
        timeout=600,
        dry_run=dry_run,
    )
    review = parse_json_from_output(review_raw)
    if isinstance(review, dict):
        if not review.get("approved", True) and review.get("revised_placement"):
            placement.update(review["revised_placement"])
            logger.info("[%s] Backflow: Claude revised placement to %s/%s", state.repo,
                        placement.get("placement"), placement.get("section_dir"))

    # Step 3: Codex generates the .tex and bridge doc
    logger.info("[%s] Backflow: generating .tex and bridge doc", state.repo)
    gen_raw = codex_exec(
        build_backflow_tex_prompt(state, placement),
        work_dir=REPO_ROOT,
        timeout=1200,
        model=model,
        dry_run=dry_run,
    )
    gen_result = parse_json_from_output(gen_raw)
    if not isinstance(gen_result, dict):
        gen_result = {}

    # Record backflow
    placement["gen_result"] = gen_result
    state.log_event("B", "backflow completed", detail=json.dumps({
        "placement": placement.get("placement"),
        "section_dir": placement.get("section_dir"),
        "tex_path": gen_result.get("tex_path", ""),
        "bridge_doc_path": gen_result.get("bridge_doc_path", ""),
    }, ensure_ascii=False))

    logger.info("[%s] Backflow done: %s/%s → tex=%s bridge=%s",
                state.repo,
                placement.get("placement"), placement.get("section_dir"),
                gen_result.get("tex_path", "N/A"),
                gen_result.get("bridge_doc_path", "N/A"))
    return placement


def _tex_escape(text: str) -> str:
    """Minimal LaTeX escaping for generated content."""
    if not isinstance(text, str):
        text = str(text)
    for char, repl in [("&", "\\&"), ("%", "\\%"), ("#", "\\#"), ("_", "\\_"), ("{", "\\{"), ("}", "\\}")]:
        text = text.replace(char, repl)
    return text


def auto_commit_push(repo: str, stage: str, round_num: int, score: int, *, dry_run: bool = False) -> None:
    """Auto-commit state files + push after each round.
    Safe in worktree isolation — no branch conflicts.
    Makes progress visible in PR (like lean4-codex-auto-dev PR #37)."""
    if dry_run:
        return
    state_dir = str(STATE_DIR)
    msg = f"outreach {repo}: Stage {stage} R{round_num} (score={score})"
    try:
        subprocess.run(
            ["git", "add", state_dir],
            cwd=str(REPO_ROOT), capture_output=True, timeout=30,
        )
        result = subprocess.run(
            ["git", "commit", "-m", msg, "--allow-empty"],
            cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=30,
        )
        if result.returncode == 0:
            push = subprocess.run(
                ["git", "push", "origin", "HEAD"],
                cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=60,
            )
            if push.returncode == 0:
                logger.info("Auto-committed+pushed: %s", msg)
            else:
                logger.warning("Push failed: %s", push.stderr[:200])
        else:
            logger.debug("Nothing to commit (no state changes)")
    except Exception as exc:
        logger.warning("Auto-commit failed: %s", exc)


def coerce_score(value: Any, default: int = 0) -> int:
    try:
        score = int(round(float(value)))
    except Exception:
        return default
    return max(0, min(10, score))


_AUTOMATH_WHITELIST_CACHE: Optional[list[str]] = None


def load_automath_theorem_whitelist() -> list[str]:
    """Bug 4 fix: load real Automath theorem names from discovery_report.json
    so Codex must reference actual theorems, not fabricate.

    Returns a list of strings like 'Omega.Folding.Entropy:topological_entropy_eq_log_phi'
    covering the most referenced theorems (by module)."""
    global _AUTOMATH_WHITELIST_CACHE
    if _AUTOMATH_WHITELIST_CACHE is not None:
        return _AUTOMATH_WHITELIST_CACHE

    report_path = REPO_ROOT / "discovery" / "discovery_report.json"
    if not report_path.exists():
        logger.warning("discovery_report.json not found at %s", report_path)
        _AUTOMATH_WHITELIST_CACHE = []
        return []

    try:
        with report_path.open(encoding="utf-8") as fh:
            data = json.load(fh)
    except Exception as exc:
        logger.warning("Failed to load discovery_report.json: %s", exc)
        _AUTOMATH_WHITELIST_CACHE = []
        return []

    discoveries = data.get("discoveries", [])
    # Sample by module to get broad coverage (10-15 per module)
    by_module: dict[str, list[str]] = {}
    for d in discoveries:
        mod = d.get("lean_module", "").split(".")
        if len(mod) < 2:
            continue
        module_name = mod[1]  # e.g., "Folding"
        name = d.get("lean_theorem", "")
        if not name:
            continue
        ref = f"{d.get('lean_file', '')}:{d.get('line_number', '')} {name}"
        by_module.setdefault(module_name, []).append(ref)

    # Take top theorems per module (sorted by name for determinism)
    whitelist: list[str] = []
    for module, refs in sorted(by_module.items()):
        refs_sorted = sorted(set(refs))[:10]  # 10 per module max
        whitelist.extend(refs_sorted)

    _AUTOMATH_WHITELIST_CACHE = whitelist
    logger.info("Loaded Automath theorem whitelist: %d refs across %d modules",
                len(whitelist), len(by_module))
    return whitelist


def valid_repo_slug(repo: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repo.strip()))


def sanitize_issue_text(text: str) -> str:
    clean = text.replace("\r\n", "\n").strip()
    if not clean.endswith(AUTOMATH_TRAILER):
        clean = clean.rstrip() + "\n\n" + AUTOMATH_TRAILER
    return clean


def detail_preview(payload: Any, limit: int = 1200) -> str:
    if isinstance(payload, str):
        return payload[:limit]
    try:
        return json.dumps(payload, ensure_ascii=False)[:limit]
    except Exception:
        return str(payload)[:limit]


# ---------------------------------------------------------------------------
# Repo inspection helpers
# ---------------------------------------------------------------------------


def recent_cutoff_date() -> str:
    dt = datetime.now(timezone.utc) - timedelta(days=90)
    return dt.date().isoformat()


@contextlib.contextmanager
def repo_checkout(repo: str, *, dry_run: bool) -> Optional[Path]:
    if dry_run:
        yield None
        return

    temp_dir = Path(tempfile.mkdtemp(prefix=f"outreach_{repo_slug(repo)}_"))
    clone_dir = temp_dir / repo.split("/", 1)[1]
    try:
        result = run_cmd(
            ["git", "clone", "--depth", "1", f"https://github.com/{repo}.git", str(clone_dir)],
            cwd=temp_dir,
            timeout=1200,
        )
        if result.returncode != 0:
            raise RuntimeError(result.stderr.strip() or result.stdout.strip() or "git clone failed")
        yield clone_dir
    finally:
        shutil.rmtree(temp_dir, ignore_errors=True)


def walk_repo_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for path in root.rglob("*"):
        rel_parts = path.relative_to(root).parts
        if any(part in IGNORE_PARTS for part in rel_parts):
            continue
        if ".claude" in rel_parts and "skills" in rel_parts:
            continue
        if path.is_file():
            files.append(path)
    return files


def repo_inventory(repo_path: Optional[Path], repo: str) -> dict[str, Any]:
    if repo_path is None:
        return {
            "repo": repo,
            "root": "",
            "readme_snippet": "dry-run repository summary",
            "lean_files": ["Main.lean"],
            "pdf_files": [],
            "top_level_files": ["README.md", "lakefile.lean"],
        }

    files = walk_repo_files(repo_path)
    readme_path = next(
        (p for p in files if p.name.lower().startswith("readme")),
        None,
    )
    readme_snippet = ""
    if readme_path:
        try:
            readme_snippet = readme_path.read_text(encoding="utf-8", errors="replace")[:5000]
        except Exception:
            readme_snippet = ""

    lean_files = [
        str(p.relative_to(repo_path))
        for p in files
        if p.suffix == ".lean"
    ][:60]
    pdf_files = [
        str(p.relative_to(repo_path))
        for p in files
        if p.suffix.lower() == ".pdf"
    ][:20]
    top_level_files = [
        str(p.relative_to(repo_path))
        for p in files
        if len(p.relative_to(repo_path).parts) == 1
    ][:30]

    return {
        "repo": repo,
        "root": str(repo_path),
        "readme_snippet": readme_snippet,
        "lean_files": lean_files,
        "pdf_files": pdf_files,
        "top_level_files": top_level_files,
    }


def extract_lean_theorem_refs(repo_path: Optional[Path]) -> list[str]:
    if repo_path is None:
        return [
            "Main.lean:12 theorem dryRunConnection",
            "Main.lean:29 lemma dryRunBridge",
        ]

    refs: list[str] = []
    pattern = re.compile(
        r"^\s*(?:@\[[^\]]+\]\s*)*(theorem|lemma|proposition|corollary|example)\s+([A-Za-z0-9_'.]+)"
    )
    for path in walk_repo_files(repo_path):
        if path.suffix != ".lean":
            continue
        rel = path.relative_to(repo_path)
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as handle:
                for line_no, line in enumerate(handle, start=1):
                    match = pattern.search(line)
                    if match:
                        refs.append(f"{rel}:{line_no} {match.group(1)} {match.group(2)}")
                        if len(refs) >= 80:
                            return refs
        except Exception:
            continue
    return refs


def keyword_relevance(repo: str, description: str) -> int:
    haystack = f"{repo} {description}".lower()
    score = 4
    weights = {
        "lean": 2,
        "fibonacci": 2,
        "golden ratio": 2,
        "zeckendorf": 2,
        "symbolic": 1,
        "dynamics": 1,
        "equational": 2,
        "formal verification": 1,
        "theorem": 1,
        "proof": 1,
        "algebra": 1,
    }
    for key, value in weights.items():
        if key in haystack:
            score += value
    return min(10, score)


# ---------------------------------------------------------------------------
# Stage A: discovery
# ---------------------------------------------------------------------------


def gh_search_repos(query: str, *, dry_run: bool) -> list[dict[str, Any]]:
    if dry_run:
        return [
            {
                "repo": "zblore/csd-lean4",
                "url": "https://github.com/zblore/csd-lean4",
                "description": "Lean 4 formalization with symbolic dynamics flavor",
                "query": query,
            },
            {
                "repo": "mysticflounder/equational-magma-theorems",
                "url": "https://github.com/mysticflounder/equational-magma-theorems",
                "description": "Lean 4 equational theorem proving experiments",
                "query": query,
            },
        ]

    gh_bin = ensure_binary(GH_PATH, "gh")
    search_args = [
        gh_bin,
        "search",
        "repos",
        query,
        "--language",
        "Lean",
        "--limit",
        "20",
        "--sort",
        "updated",
        "--json",
        "url,description,updatedAt,pushedAt",
    ]
    result = run_cmd(search_args, cwd=REPO_ROOT, timeout=300)
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or result.stdout.strip() or "gh search failed")

    rows = json.loads(result.stdout or "[]")
    repos: list[dict[str, Any]] = []
    for row in rows:
        url = row.get("url", "")
        match = re.search(r"github\.com/([^/\s]+/[^/\s]+?)(?:\.git)?/?$", url)
        if not match:
            continue
        repo = match.group(1)
        repos.append(
            {
                "repo": repo,
                "url": url,
                "description": row.get("description", "") or "",
                "updated_at": row.get("updatedAt", "") or "",
                "pushed_at": row.get("pushedAt", "") or "",
                "query": query,
            }
        )
    return repos


def score_candidates_with_codex(
    candidates: list[dict[str, Any]],
    *,
    model: Optional[str],
    dry_run: bool,
) -> list[dict[str, Any]]:
    if dry_run:
        scored: list[dict[str, Any]] = []
        for item in candidates:
            score = keyword_relevance(item["repo"], item.get("description", ""))
            scored.append({**item, "codex_score": score, "codex_reason": "dry-run heuristic"})
        return scored

    prompt = textwrap.dedent(
        f"""\
        You are Stage A2 of an event-driven community outreach pipeline.

        Goal:
        Rank Lean repositories by how likely they are to support a technically serious
        GitHub issue connecting their formalization work to the Automath repository at:
        {AUTOMATH_REPO_URL}

        Constraints:
        - Prefer repositories that are small-to-medium, active, mathematically substantive,
          and plausibly connect to Fibonacci / Zeckendorf / symbolic dynamics /
          equational reasoning / formal theorem proving.
        - Exclude trivial demos and generic boilerplate.
        - Return JSON only.

        Candidate repositories:
        {json.dumps(candidates, indent=2, ensure_ascii=False)}

        JSON schema:
        {{
          "candidates": [
            {{
              "repo": "owner/name",
              "score": 1,
              "reason": "short justification"
            }}
          ]
        }}
        """
    )
    raw = codex_exec(prompt, work_dir=REPO_ROOT, timeout=900, model=model, dry_run=dry_run)
    parsed = parse_json_from_output(raw)
    ranking = parsed.get("candidates", []) if isinstance(parsed, dict) else []
    by_repo = {item["repo"]: item for item in candidates}
    scored: list[dict[str, Any]] = []
    for row in ranking:
        repo = row.get("repo", "")
        if repo not in by_repo:
            continue
        merged = dict(by_repo[repo])
        merged["codex_score"] = coerce_score(row.get("score"), keyword_relevance(repo, merged.get("description", "")))
        merged["codex_reason"] = str(row.get("reason", ""))[:500]
        scored.append(merged)
    if scored:
        return scored

    fallback: list[dict[str, Any]] = []
    for item in candidates:
        score = keyword_relevance(item["repo"], item.get("description", ""))
        fallback.append({**item, "codex_score": score, "codex_reason": "heuristic fallback"})
    return fallback


def review_candidates_with_claude(
    candidates: list[dict[str, Any]],
    *,
    dry_run: bool,
) -> list[dict[str, Any]]:
    if dry_run:
        reviewed = []
        for item in candidates:
            reviewed.append({**item, "claude_score": max(1, item["codex_score"] - 1)})
        return reviewed

    prompt = textwrap.dedent(
        f"""\
        You are Stage A3 of a GitHub community outreach pipeline.
        Review the Codex-scored repository candidates below for technical outreach fit.

        Keep repositories that are mathematically substantive, active, and likely to
        support a precise contribution issue linked to {AUTOMATH_REPO_URL}.

        Return JSON only:
        {{
          "candidates": [
            {{
              "repo": "owner/name",
              "score": 1,
              "decision": "keep|drop",
              "reason": "short review note"
            }}
          ]
        }}

        Candidates:
        {json.dumps(candidates, indent=2, ensure_ascii=False)}
        """
    )
    raw = claude_exec(prompt, work_dir=REPO_ROOT, timeout=600, dry_run=dry_run)
    parsed = parse_json_from_output(raw)
    rows = parsed.get("candidates", []) if isinstance(parsed, dict) else []
    by_repo = {item["repo"]: item for item in candidates}
    reviewed: list[dict[str, Any]] = []
    for row in rows:
        repo = row.get("repo", "")
        if repo not in by_repo:
            continue
        if str(row.get("decision", "keep")).lower() == "drop":
            continue
        merged = dict(by_repo[repo])
        merged["claude_score"] = coerce_score(row.get("score"), merged["codex_score"])
        merged["claude_reason"] = str(row.get("reason", ""))[:500]
        reviewed.append(merged)
    if reviewed:
        return reviewed

    return [{**item, "claude_score": item["codex_score"]} for item in candidates]


def discover_candidates(*, model: Optional[str], dry_run: bool) -> list[dict[str, Any]]:
    processed = load_processed_repos()
    cutoff = recent_cutoff_date()
    seen: dict[str, dict[str, Any]] = {}

    logger.info("Stage A: discovery (processed=%d, cutoff=%s)", len(processed), cutoff)
    for raw_query in DISCOVERY_QUERIES:
        query = raw_query.replace("RECENT", cutoff)
        try:
            rows = gh_search_repos(query, dry_run=dry_run)
        except Exception as exc:
            logger.warning("Discovery query failed: %s (%s)", query, exc)
            continue
        for row in rows:
            repo = row["repo"]
            if repo.lower() == "leanprover-community/mathlib4" or "mathlib" in repo.lower():
                continue
            if repo in processed:
                continue
            current = seen.get(repo)
            if current is None:
                seen[repo] = row
            else:
                current["query"] = f"{current.get('query', '')}; {row.get('query', '')}".strip("; ")

    merged = list(seen.values())
    scored = score_candidates_with_codex(merged, model=model, dry_run=dry_run)
    # Bug 7 fix: removed Claude A3 review (redundant — Codex relevance score is enough
    # for pre-filtering; B4 is the critical safety net for actual findings).
    # Bad candidates still get filtered in Stage B via min(codex,claude) gate.

    final_rows: list[dict[str, Any]] = []
    for item in scored:
        final_score = item.get("codex_score", 0)
        if final_score < 7:
            continue
        final_rows.append(
            {
                "repo": item["repo"],
                "url": item.get("url", f"https://github.com/{item['repo']}"),
                "description": item.get("description", ""),
                "codex_score": item.get("codex_score", 0),
                "claude_score": 0,  # not reviewed by Claude at Stage A
                "final_score": final_score,
                "reason": item.get("codex_reason") or item.get("claude_reason", ""),
            }
        )

    final_rows.sort(key=lambda item: (-item["final_score"], item["repo"]))
    payload = {
        "generated_at": iso_now(),
        "queries": [q.replace("RECENT", cutoff) for q in DISCOVERY_QUERIES],
        "candidates": final_rows,
    }
    if not dry_run:
        CANDIDATES_FILE.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")

    if final_rows:
        logger.info("Discovered %d candidate repositories", len(final_rows))
        for item in final_rows[:10]:
            logger.info("  %s (final=%s)", item["repo"], item["final_score"])
    else:
        logger.info("No candidate repositories survived Stage A")
    return final_rows


# ---------------------------------------------------------------------------
# Stage B: research
# ---------------------------------------------------------------------------


def build_content_plan(
    repo: str,
    todo_task: str,
    inventory: dict[str, Any],
    theorem_refs: list[str],
) -> dict[str, Any]:
    """Build a concrete content plan. Reads target-specific docs if they exist,
    otherwise falls back to generic Lean file scanning.

    Like loning's oracle_pipeline reading PIPELINE.md per paper:
    we read targets/{repo}/*.md for specific research directions."""

    slug = repo_slug(repo)
    target_dir = SCRIPT_DIR / "targets" / slug

    # READ ALL TARGET FILES (like loning's PIPELINE.md pattern)
    # Everything in targets/{repo}/ is agent communication: .md research docs,
    # .py computation scripts, .json data results. All become context.
    target_context = ""
    if target_dir.exists():
        for f in sorted(target_dir.iterdir()):
            if f.is_file() and f.suffix in (".md", ".py", ".json", ".txt", ".csv"):
                content = f.read_text(encoding="utf-8")
                # .md files: full content (research docs, issue briefs)
                # .py files: just docstring + first 30 lines (script purpose)
                # .json files: summary only (data too large)
                if f.suffix == ".md":
                    target_context += f"\n\n--- {f.name} ---\n{content[:4000]}"
                elif f.suffix == ".py":
                    lines = content.split("\n")
                    header = "\n".join(lines[:30])
                    target_context += f"\n\n--- {f.name} (script, first 30 lines) ---\n{header}"
                elif f.suffix == ".json":
                    target_context += f"\n\n--- {f.name} ({len(content)} bytes, data file) ---"
                else:
                    target_context += f"\n\n--- {f.name} ---\n{content[:2000]}"

    # If we have target-specific docs, use them as the codex_task
    if target_context:
        plan = {
            "codex_task": (
                f"Read the research documents below for {repo}. "
                f"They describe specific issues, prior results, and computation data. "
                f"Your job: continue the research described, address open questions, "
                f"and produce findings that are NEW and USEFUL to the target.\n"
                f"{target_context}"
            ),
            "target_format": "GitHub issue",
            "target_format_example": "README.md",
            "output_type": "findings JSON",
            "output_path": str(target_dir / "research.md"),
            "content_list": [],  # empty = Codex does research, not formatting
            "what_target_gains": "answers to their specific open questions",
            "backflow": {"enabled": True, "description": "new computation results"},
        }
        logger.info("[%s] B0 plan from target docs (%d chars context)", repo, len(target_context))
        return plan

    # FALLBACK: generic plan from Lean file scanning
    # Read Conjectures.lean for open conjectures
    conjectures_file = REPO_ROOT / "lean4" / "Omega" / "Frontier" / "Conjectures.lean"
    open_conjectures: list[dict[str, Any]] = []
    if conjectures_file.exists():
        content = conjectures_file.read_text(encoding="utf-8")
        for match in re.finditer(r'/--\s*(.*?)\s*-/\s*def\s+(\w+)', content, re.DOTALL):
            doc = match.group(1).strip().split('\n')[0][:120]
            name = match.group(2)
            open_conjectures.append({
                "name": name,
                "category": "research_open",
                "ams": "37",
                "source_file": f"lean4/Omega/Frontier/Conjectures.lean",
                "doc_comment": doc,
                "proved": False,
            })

    # Read MomentSum.lean for proved test values
    moment_file = REPO_ROOT / "lean4" / "Omega" / "Folding" / "MomentSum.lean"
    test_cases: list[dict[str, Any]] = []
    if moment_file.exists():
        content = moment_file.read_text(encoding="utf-8")
        for match in re.finditer(r'theorem\s+(momentSum_\w+)\s*:', content):
            name = match.group(1)
            if any(kw in name for kw in ["zero", "one", "two", "three", "four", "five"]):
                test_cases.append({
                    "name": name,
                    "category": "test",
                    "ams": "37",
                    "source_file": "lean4/Omega/Folding/MomentSum.lean",
                    "doc_comment": f"Proved: {name}",
                    "proved": True,
                })

    # FiberRing.lean — proved ring isomorphism
    formalized_results: list[dict[str, Any]] = [{
        "name": "stableValueRingEquiv",
        "category": "research_formalized",
        "ams": "11",
        "source_file": "lean4/Omega/Folding/FiberRing.lean:157",
        "doc_comment": "X_m is ring-isomorphic to ZMod(Nat.fib(m+2))",
        "proved": True,
    }]

    # S₃ recurrence IS PROVED (S3Recurrence.lean + CCSPrime8Split.lean, no sorry).
    # Mark as formalized, not open.
    key_results: list[dict[str, Any]] = [{
        "name": "S₃_recurrence",
        "category": "research_formalized",
        "ams": "37",
        "source_file": "lean4/Omega/Folding/S3Recurrence.lean",
        "doc_comment": "S₃ linear recurrence: proved unconditionally in Automath",
        "proved": True,
    }, {
        "name": "S₂_exponential_growth",
        "category": "research_open",
        "ams": "37",
        "source_file": "lean4/Omega/Folding/MomentRecurrence.lean",
        "doc_comment": "S₂(m) = Theta(lambda_+^m) where lambda_+ is Perron root of t³-2t²-2t+2",
        "proved": False,
    }]

    all_content = test_cases[:5] + formalized_results + key_results + open_conjectures[:4]

    # Determine target format from repo
    if "formal-conjectures" in repo:
        task = (
            "Write a Lean 4 file matching the formal-conjectures format (see ABC.lean). "
            "Include Apache 2.0 header, import FormalConjectures.Util.ProblemImports, "
            "use @[category X, AMS N] attributes. Items marked proved=true get short proofs "
            "(by decide or by norm_num). Items marked proved=false get sorry."
        )
        fmt = "Lean file"
        example = "FormalConjectures/Wikipedia/ABC.lean"
        output = "tools/community-outreach/drafts/OmegaGoldenMeanShift_v2.lean"
    elif "equational_theories" in repo:
        task = (
            "Construct Fibonacci ring-operation magmas as separating countermodels. "
            "Use stableValueRingEquiv to define magma operations on ZMod(Nat.fib(m+2)) "
            "and test which equation pairs they separate."
        )
        fmt = "Lean file + data"
        example = "README.md CONTRIBUTING.md"
        output = "tools/community-outreach/drafts/FibonacciMagmas.lean"
    else:
        task = f"Analyze {repo} and draft a contribution using Automath results."
        fmt = "GitHub issue"
        example = ""
        output = f"tools/community-outreach/drafts/{repo.replace('/', '_')}_issue.md"

    plan = {
        "codex_task": task,
        "target_format": fmt,
        "target_format_example": example,
        "output_type": fmt,
        "output_path": output,
        "content_list": all_content,
        "what_target_gains": f"Fills AMS 37/11 gap with {len(all_content)} items ({sum(1 for c in all_content if not c.get('proved'))} open conjectures)",
        "backflow": {"enabled": False, "description": ""},
    }

    logger.info("[%s] B0 plan built programmatically: %d items (%d open, %d proved)",
                repo, len(all_content), sum(1 for c in all_content if not c.get("proved")),
                sum(1 for c in all_content if c.get("proved")))
    return plan


def build_stage_b0_plan_prompt(
    repo: str,
    inventory: dict[str, Any],
    todo_task: str = "",
    previous_rounds: Optional[list[dict[str, Any]]] = None,
    theorem_refs: Optional[list[str]] = None,
) -> str:
    """B0: Claude produces a concrete, narrow task spec for Codex.
    This is the step that was missing — Claude reads target format + Automath assets
    and tells Codex EXACTLY what to produce."""
    prev_section = ""
    if previous_rounds:
        best = max(previous_rounds, key=lambda r: max(r.get("codex_score", 0), r.get("claude_score", 0)))
        prev_section = (
            f"\n\nPrevious attempt scored {max(best.get('codex_score',0), best.get('claude_score',0))}/10."
            f"\nClaude feedback: {best.get('claude_notes', 'none')}"
            f"\nAdjust the task to address this feedback."
        )

    todo_section = f"\n\nTODO item context: {todo_task}" if todo_task else ""
    refs_section = ""
    if theorem_refs:
        refs_section = "\n\nAutomath theorem refs (sample):\n" + "\n".join(f"  - {r}" for r in theorem_refs[:15])

    return textwrap.dedent(
        f"""\
        You are the PLANNING step (B0) of a community outreach pipeline.
        Your job: produce a CONCRETE, NARROW task specification for Codex.

        Target repository: {repo}
        Target repo inventory: {json.dumps(inventory, indent=2, ensure_ascii=False)[:2000]}
        {todo_section}{prev_section}{refs_section}

        INSTRUCTIONS:

        YOU (Claude) must select the SPECIFIC mathematical content. Do NOT leave
        content selection to Codex — Codex cannot distinguish proved from open,
        true from false. YOU read the Automath sources and pick exactly what to include.

        1. What FORMAT does the target repo expect?
           (Check CONTRIBUTING.md, look at merged PRs)

        2. YOU read these Automath files and SELECT content:
           - lean4/Omega/Frontier/Conjectures.lean — 9 formal OPEN conjectures (sorry)
           - lean4/Omega/Folding/MomentSum.lean — PROVED moment sum values (test cases)
           - lean4/Omega/Folding/MomentRecurrence.lean — PROVED S₂ recurrence
           - lean4/Omega/Folding/FiberRing.lean — PROVED ring isomorphism
           - lean4/Omega/Folding/Entropy.lean — PROVED entropy results
           - Main paper theory/2026_golden_ratio_*/sections/ — open questions in Discussion

           For each item you select, mark it clearly:
           PROVED = can be @[category test] or @[category research formalized]
           OPEN = must be @[category research open] with sorry

        3. Write a COMPLETE content list for Codex. Codex should NOT search or decide
           what to include — it should only FORMAT your list into the target's structure.

        4. If deep research produces NEW results, flag for backflow to main paper.

        Return JSON only:
        {{
          "codex_task": "Write a Lean 4 file containing exactly the items listed below.
                        Do NOT add, remove, or modify items. Format only.",
          "target_format": "Lean file|GitHub issue|PR|zulip post|email",
          "target_format_example": "URL to example file in target repo to copy format from",
          "output_type": "Lean 4 file|issue body|post text",
          "output_path": "where to write the output",
          "content_list": [
            {{
              "name": "theorem/conjecture name",
              "category": "test|research_formalized|research_open",
              "ams": "11|37|40|47",
              "source_file": "lean4/Omega/path/File.lean:line",
              "lean_statement": "the actual Lean 4 statement to include (or sorry sketch)",
              "doc_comment": "one-line description for the doc comment",
              "proved": true
            }}
          ],
          "what_target_gains": "one sentence",
          "backflow": {{
            "enabled": false,
            "description": ""
          }}
        }}
        """
    )


def build_stage_b1_prompt(repo: str, inventory: dict[str, Any]) -> str:
    return textwrap.dedent(
        f"""\
        You are Stage B1 of a community outreach pipeline.

        Repository target: {repo}
        Automath repo root: {REPO_ROOT}
        Forbidden paths: {", ".join(FORBIDDEN_PATH_PATTERNS)}

        Read the target repository and the Automath repository. Identify the
        mathematically substantive parts of the target repo, especially Lean 4
        formalizations, README claims, and any PDF papers.

        Repository inventory:
        {json.dumps(inventory, indent=2, ensure_ascii=False)}

        Return JSON only:
        {{
          "summary": "technical summary",
          "themes": ["..."],
          "connections": ["possible bridge to Automath"],
          "pdfs": ["relative/path.pdf"],
          "lean_files": ["relative/path.lean"]
        }}
        """
    )


def build_stage_b2_prompt(
    repo: str,
    b1_data: dict[str, Any],
    previous_rounds: Optional[list[dict[str, Any]]] = None,
    automath_theorem_whitelist: Optional[list[str]] = None,
    deep_mode: bool = False,
    claude_plan: Optional[dict[str, Any]] = None,
    existing_research: str = "",
) -> str:
    """Build the B2 prompt. If claude_plan has a content_list, produce a SHORT
    formatting-only prompt. Otherwise fall back to the full research prompt."""

    # ROUTING: R1 (no previous rounds) → bridge-finding from scratch.
    # R2+ (has previous rounds with doc) → edit existing research.md.
    has_previous_doc = previous_rounds and any(r.get("doc_path") for r in previous_rounds)

    if has_previous_doc:
        # R2+ RESEARCH AGENT PATH: execute action_items first, then edit doc
        best_round = max(previous_rounds, key=lambda r: max(r.get("codex_score", 0), r.get("claude_score", 0)))
        best_doc = best_round.get("doc_path", "")
        best_notes = best_round.get("claude_notes", "")

        # Extract action_items from Claude's last review
        action_items_str = ""
        for prev in reversed(previous_rounds):
            notes = prev.get("claude_notes", "")
            # Look for action_items in the B4 review data
            action_items = prev.get("action_items", [])
            if action_items:
                action_items_str = json.dumps(action_items, indent=2, ensure_ascii=False)
                break

        target_dir = SCRIPT_DIR / "targets" / repo_slug(repo)
        scripts_available = ""
        if target_dir.exists():
            scripts = [f.name for f in target_dir.iterdir() if f.suffix == ".py"]
            if scripts:
                scripts_available = f"\n\nAvailable scripts in {target_dir}:\n" + "\n".join(f"  - {s}" for s in scripts)

        return textwrap.dedent(
            f"""\
            You are a research mathematician continuing deep work on {repo}.
            Your goal: RESOLVE the open questions below. Use whatever tools you need.

            ═══════════════════════════════════════════════════════════════
            OPEN QUESTIONS FROM CLAUDE'S REVIEW
            ═══════════════════════════════════════════════════════════════

            {best_notes}

            Action items:
            {action_items_str or "No structured action items — parse the notes above for what needs doing."}
            {scripts_available}

            ═══════════════════════════════════════════════════════════════
            YOUR JOB: RESOLVE EACH OPEN QUESTION
            ═══════════════════════════════════════════════════════════════

            For each question, decide the best approach:
            - Pure reasoning/proof → write the argument directly
            - Needs computation → write and run a Python script
            - Needs verification of a claim → test it (code or counterexample search)
            - Needs literature/code reading → read the relevant files

            You have full access to:
            - Python 3 with sympy, numpy, etc.
            - All files in {REPO_ROOT}
            - Scripts in {target_dir}/
            - The research document: `cat {best_doc}`

            If you write a script, save it to {target_dir}/<name>.py so future rounds
            can reuse it. But only write a script if computation is the right tool.
            A clean mathematical argument is just as valuable.

            ═══════════════════════════════════════════════════════════════
            THEN: UPDATE THE RESEARCH DOCUMENT
            ═══════════════════════════════════════════════════════════════

            Read: `cat {best_doc}`

            Add your results (proofs, computation outputs, new theorems).
            Keep all existing findings Claude didn't reject.
            Edit the file `{best_doc}` directly.

            ═══════════════════════════════════════════════════════════════

            STANDARDS:
            - Every claim must be backed by proof or computation. No hand-waving.
            - Do NOT write "further research needed" — resolve it or state what blocks you.
            - Do NOT remove findings unless Claude said to.

            Return JSON:
            {{
              "findings": [
                {{
                  "title": "what you resolved",
                  "type": "proof|computation|verification|counterexample|analysis",
                  "status": "resolved|partial|blocked",
                  "bridge": "the result (theorem statement, computed bounds, certificate, etc.)",
                  "method": "how you got the result (reasoning / script / literature)",
                  "script": "path if you wrote a script, null otherwise"
                }}
              ]
            }}
            """
        )

    # R1 BRIDGE-FINDING PATH: first round, read both sides and find connections
    if claude_plan and claude_plan.get("codex_task"):
        return textwrap.dedent(
            f"""\
            You are a mathematical research analyst. Your job is to find deep
            connections between two projects, like a researcher writing a bridge paper.

            TARGET: {repo}
            TASK: {claude_plan.get('codex_task', '')}
            {"" if not existing_research else chr(10) + "═══════════════════════════════════════════════════════════════" + chr(10) + "EXISTING RESEARCH (from previous runs — BUILD ON THIS, don't discard):" + chr(10) + "═══════════════════════════════════════════════════════════════" + chr(10) + existing_research[:4000] + chr(10) + chr(10) + "Keep the findings above. You may ADD new ones but do NOT remove existing." + chr(10)}
            ═══════════════════════════════════════════════════════════════
            STEP 1: DEEP-READ THE TARGET
            ═══════════════════════════════════════════════════════════════
            Read the target project thoroughly:
            - `gh api repos/{repo}/contents/README.md --jq '.content' | base64 -d`
            - Browse their code, issues, papers
            - Understand what THEY are working on, what problems THEY face

            ═══════════════════════════════════════════════════════════════
            STEP 2: DEEP-READ AUTOMATH
            ═══════════════════════════════════════════════════════════════
            Read the Omega project's main paper and code:
            - `cat theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/main.tex | head -200`
            - `cat lean4/Omega/Frontier/Conjectures.lean`
            - `rg "theorem|def " lean4/Omega/Folding/FiberRing.lean | head -20`
            - `rg "theorem|def " lean4/Omega/Folding/Entropy.lean | head -20`
            - Search for specific topics: `rg "<keyword from target>" lean4/ theory/`

            ═══════════════════════════════════════════════════════════════
            STEP 3: FIND BRIDGES (the real task)
            ═══════════════════════════════════════════════════════════════

            {RESEARCH_STANDARD_ZH}

            Like Tolmeton's issue #25 on this repo, find:
            - "Your X is the discrete version of our Y"
            - "Our theorem Z gives a special case of your conjecture W"
            - "The carry defect in our fold operator has an interpretation in your framework"

            Write a correspondence table:
            | # | Their result | Our result | Status | Bridge |
            Each row: what corresponds, whether proved on both sides,
            and what the bridge insight is.

            Be honest: mark each bridge as "proved|conjectured|analogy".
            Do NOT fabricate connections. If nothing deep exists, say so.

            ═══════════════════════════════════════════════════════════════

            Return JSON:
            {{
              "target_summary": "what the target project does (2 sentences)",
              "automath_relevant": "which Automath results are relevant (list file:theorem)",
              "findings": [
                {{
                  "title": "bridge title",
                  "type": "theorem|corollary|conjecture|analogy",
                  "status": "proved|conjectured|analogy",
                  "their_side": "what they have",
                  "our_side": "what we have",
                  "bridge": "the surprising connection",
                  "target_need": "how this helps THEM",
                  "automath_refs": ["lean4/Omega/path:line"],
                  "novelty_risk": "is this actually new?"
                }}
              ],
              "stop_reason": "why research stopped here"
            }}
            """
        )

    # SLOW PATH: no content_list, full research prompt (original behavior)
    feedback_section = ""
    if previous_rounds:
        # Find the best round's findings to DEEPEN (not discard)
        best_round = max(previous_rounds, key=lambda r: max(r.get("codex_score", 0), r.get("claude_score", 0)))
        best_score = max(best_round.get("codex_score", 0), best_round.get("claude_score", 0))
        best_findings = best_round.get("findings_summary", [])

        feedback_parts = []
        for i, prev in enumerate(previous_rounds, 1):
            feedback_parts.append(
                f"Round {i}: codex={prev.get('codex_score', 'N/A')}, "
                f"claude={prev.get('claude_score', 'N/A')}\n"
                f"  Claude notes: {prev.get('claude_notes', 'N/A')}"
            )

        # Find the best round's doc file for Codex to read
        best_doc = best_round.get("doc_path", "")
        doc_read_cmd = f"\n\nREAD THE PREVIOUS DOCUMENT FIRST:\n`cat {best_doc}`\n" if best_doc else ""

        # Extract Claude's specific actionable feedback items
        best_notes = best_round.get("claude_notes", "")

        feedback_section = (
            f"\n\nPREVIOUS ROUND scored {best_score}/10."
            + doc_read_cmd
            + f"\n\nClaude's feedback:\n{best_notes}\n"
            + "\n\nYOUR CONCRETE STEPS (follow like PR #37's Phase C):\n"
            f"Step 1: `cat {best_doc}` — read the existing document\n"
            "Step 2: Do NOT generate new findings. Your existing findings are IN the file.\n"
            "Step 3: Address Claude's SPECIFIC feedback by:\n"
            "   - If Claude said 'verify X' → write Python to verify X, add result to the finding\n"
            "   - If Claude said 'X is wrong' → fix the specific error in that finding\n"
            "   - If Claude said 'missing Y' → add Y as a NEW finding at the end\n"
            f"Step 4: Edit the file {best_doc} with your changes. Use the Edit tool or write.\n"
            "   Do NOT output a new document. EDIT the existing file.\n"
            "Step 5: `cat {best_doc}` to verify your edits are in the file.\n\n"
            "FORBIDDEN:\n"
            "- Do NOT rewrite the document from scratch\n"
            "- Do NOT remove any existing finding\n"
            "- Do NOT change finding titles or bridge descriptions unless fixing an error\n"
            "- Only ADD content (verification results, new findings) or FIX specific errors\n"
        ).replace("{best_doc}", best_doc)

    whitelist_section = ""
    if automath_theorem_whitelist:
        # Bug 6 fix: deep_mode gets FULL whitelist for broader exploration
        limit = len(automath_theorem_whitelist) if deep_mode else 80
        whitelist_section = (
            "\n\nAUTOMATH THEOREM WHITELIST (findings MUST reference these real theorems, "
            "do not fabricate theorem names):\n"
            + "\n".join(f"  - {t}" for t in automath_theorem_whitelist[:limit])
        )

    deep_section = ""
    if deep_mode:
        deep_section = textwrap.dedent("""

        ═══════════════════════════════════════════════════════════════
        DEEP RESEARCH MODE (previous rounds scored low — escalate depth)
        ═══════════════════════════════════════════════════════════════

        Previous attempts produced classical/shallow results. Go DEEPER:

        1. 读取目标 repo 的全部 Lean 4 源文件, 不只是 README 和顶层.
           用 rg / find / grep 扫描所有 .lean 文件, 逐个分析定义与定理.

        2. 读取 Automath 的论文 PDFs (theory/2026_*/ 下的 main.tex +
           sections/**/*.tex), 特别是 appendix 部分. 寻找未被形式化但
           已被证明的 frontier 结果.

        3. 不要满足于"对应关系"(A 对应 B). 要找到**真正的新定理**:
           - A 的结构在 B 的语境下给出新的不等式 / 渐近估计 / 分类
           - B 的方法论在 A 中给出新的证明或更强结果
           - A + B 的结合解决 A 或 B 单独无法解决的问题

        4. 如果真的没有深层联系, 诚实返回 "findings": [] 并说明
           "stop_reason". 不要为了完成任务而虚构.

        5. 优先考虑的深入方向:
           - 谱论: 碰撞核特征值, Perron-Frobenius, 转移算子
           - 模论: Fibonacci 模数塔, CRT 分解, 有限域结构
           - 遍历论: 熵, 极限分布, 大偏差
           - 对称性: Galois 作用, 拟共轭, 刚性定理
           - 数论算术: Zeckendorf 表示, Sturm 序列, p-adic 极限
        """)

    return textwrap.dedent(
        f"""\
        You are Stage B2 of a community outreach pipeline.

        Repository target: {repo}
        Automath repo root: {REPO_ROOT}
        Forbidden paths: {", ".join(FORBIDDEN_PATH_PATTERNS)}

        Stage B1 output:
        {json.dumps(b1_data, indent=2, ensure_ascii=False)}{feedback_section}{whitelist_section}{deep_section}

        ═══════════════════════════════════════════════════════════════
        CLAUDE'S PLAN (B0) — FOLLOW THIS EXACTLY
        ═══════════════════════════════════════════════════════════════
        {json.dumps(claude_plan or {}, indent=2, ensure_ascii=False)}

        YOUR JOB: Take the "content_list" above and FORMAT it into the
        target repo's structure. Do NOT add items. Do NOT remove items.
        Do NOT change mathematical statements. ONLY format.

        If "content_list" is provided:
          - Read the "target_format_example" to learn the exact file format
          - Write each item from content_list into the output file
          - Use the category, AMS tag, and lean_statement exactly as given
          - Add license header and imports matching the example

        If "content_list" is empty or missing, fall back to Step 1 below.

        ═══════════════════════════════════════════════════════════════
        STEP 1 (FALLBACK ONLY): UNDERSTAND WHAT THE TARGET REPO NEEDS
        ═══════════════════════════════════════════════════════════════

        Before looking at Automath, read the TARGET repo thoroughly:

        1. Read README.md — find "Future Work", "TODO", "Limitations",
           "Open Problems", "Help Wanted", "Contributing" sections.
        2. Read open issues: `gh api repos/{repo}/issues?state=open`
        3. Read the paper (if any) — find "Discussion", "Future Directions",
           "Open Questions" sections.
        4. Read CONTRIBUTING.md if it exists.

        Write down: what does THIS repo's author actually want help with?
        What are they stuck on? What would make their project better?
        What would they be grateful to receive?

        ═══════════════════════════════════════════════════════════════
        STEP 2: SEARCH THE ENTIRE AUTOMATH PROJECT
        ═══════════════════════════════════════════════════════════════

        Automath is a large project. USE YOUR TOOLS to search — do not
        read files manually. Search the ENTIRE project, not just lean4/:

        A) SEARCH with rg/grep across ALL directories:
           rg "<keywords from target needs>" lean4/ theory/ papers/ --type lean --type tex
           rg "conjecture|Conjecture|sorry|Future|Open" lean4/ theory/
           find theory/ -name "*.tex" | xargs grep -l "<keyword>"

        B) The MAIN PAPER has ALL content (34 sub-papers backflowed here):
           theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/
           sections/body/ — core theorems
           sections/appendix/ — advanced results, bridges, frontier
           READ the appendix — it has content not yet in lean4/

        C) OPEN CONJECTURES are in multiple places:
           lean4/Omega/Frontier/Conjectures.lean — 9 formal conjectures
           Main paper "Future Work" / "Open Questions" sections
           Individual papers' Discussion sections

        D) If you discover NEW mathematical results during research:
           - Note them in findings as type "new_result"
           - These will be BACKFLOWED to the main paper (Phase 2.5)
           - New results = new content for the project, not just outreach

        The contribution must be USEFUL TO THEM, not just mathematically
        interesting to us.

        ═══════════════════════════════════════════════════════════════
        STEP 3: FORMULATE FINDINGS AS GIFTS, NOT SHOWCASES
        ═══════════════════════════════════════════════════════════════

        Each finding should answer: "What does the target repo author
        gain from knowing this?" If the answer is "nothing concrete"
        or "they'd say 'interesting but so what?'", it's not a finding.

        Good: "Your issue #N asks for X. Automath's theorem Y gives you X
              for the special case Z, with a Lean 4 proof at file:line."
        Bad:  "Automath's theorem Y is related to your theorem X."

        Research standard (must follow verbatim):
        {RESEARCH_STANDARD_ZH}

        HARD CONSTRAINTS:
        1. Every `automath_refs` entry MUST point to a real file:line in the Automath repo.
           Do NOT invent paths. Verify the file exists before citing it.
        2. Theorem names MUST match actual Lean 4 theorem names from the whitelist.
        3. Do NOT invent fictional mathematical objects.
        4. If the target repo has no needs Automath can help with, return
           `"findings": []` with `"stop_reason"` explaining why.
        5. Every finding MUST include `"target_need"` — what specific need
           of the target repo this finding addresses.

        Return JSON only:
        {{
          "target_needs_analysis": {{
            "open_issues": ["issue #N: description"],
            "future_work": ["item from README/paper"],
            "missing_examples": ["what concrete examples they lack"],
            "formalization_gaps": ["what they want to formalize but haven't"]
          }},
          "findings": [
            {{
              "title": "succinct result title",
              "type": "theorem|corollary|conjecture|proposition",
              "status": "proved|conjectured|untested",
              "target_need": "which specific need from target_needs_analysis this addresses",
              "what_they_gain": "concrete benefit to the target repo author",
              "statement": "mathematical statement",
              "proof_sketch": "high-level proof sketch or validation path",
              "lean_refs": ["target repo file:line"],
              "automath_refs": ["automath path:line"],
              "novelty_risk": "short note"
            }}
          ],
          "stop_reason": "why this round can stop"
        }}
        """
    )


def build_stage_b25_verify_prompt(repo: str, findings: list[Any]) -> str:
    """B2.5: Codex verifies its own concrete algebra claims with Python.
    Like PR #37's `lake build` — execute then verify. If a claim is wrong, fix it."""
    return textwrap.dedent(
        f"""\
        You made these mathematical claims about {repo}. Some may have concrete
        algebra errors. Your job: VERIFY each concrete claim with Python, then
        fix or remove any that fail.

        FINDINGS TO VERIFY:
        {json.dumps(findings, indent=2, ensure_ascii=False)}

        FOR EACH FINDING that makes a concrete algebra claim (e.g., "NAND on GF(2)
        satisfies/fails equation X", or "3x+y mod 13 satisfies law Y"):

        1. Write a Python script that checks the claim:
           ```python
           # Example: check if NAND on GF(2) satisfies x◇(y◇x) = x
           def nand(x, y): return 1 - x*y
           for x in range(2):
               for y in range(2):
                   if nand(x, nand(y, x)) != x:
                       print(f"FAILS: x={{x}}, y={{y}}")
                       break
               else: continue
               break
           else:
               print("SATISFIES")
           ```

        2. Run the script: `python3 -c "..."`
        3. If the claim is WRONG: fix it or remove the finding
        4. If the claim is RIGHT: keep it

        CRITICAL RULES:
        - Do NOT rewrite findings. Only fix specific wrong numbers/claims.
        - Do NOT add or remove findings. Keep the same structure.
        - Do NOT change titles, bridges, or refs. Only change the specific
          wrong algebra result (e.g., "fails" → "satisfies", or fix a number).
        - If a finding has NO concrete algebra claim to verify, leave it unchanged.

        Return JSON:
        {{
          "verification_results": [
            {{"finding_index": 0, "claim": "...", "python_result": "...", "correct": true}},
            ...
          ],
          "corrected_findings": [
            // SAME findings list, SAME structure, only wrong numbers fixed
          ]
        }}
        """
    )


def build_stage_b3_prompt(repo: str, findings: list[Any]) -> str:
    return textwrap.dedent(
        f"""\
        You are Stage B3 of a community outreach pipeline.

        Score the following research findings for repository {repo}.
        Focus on mathematical correctness, novelty, and whether the resulting
        outreach issue would be technically credible and publishable.

        Findings:
        {json.dumps(findings, indent=2, ensure_ascii=False)}

        Return JSON only:
        {{
          "overall_score": 1,
          "correctness": 1,
          "novelty": 1,
          "publishability": 1,
          "decision": "advance|retry|skip",
          "notes": "short explanation"
        }}
        """
    )


def build_stage_b4_prompt(repo: str, findings: list[Any], codex_score_data: dict[str, Any]) -> str:
    return textwrap.dedent(
        f"""\
        You are Stage B4 (Claude final review) of a community outreach pipeline.

        Review the findings below for repository {repo}.
        Score on THREE dimensions equally weighted:

        1. CORRECTNESS: Is the math right? Are PROVED items actually proved in
           Automath? Are OPEN items actually open (not proved elsewhere)?
           CRITICAL: check that no "conjecture" is contradicted by Automath's
           own verified Lean proofs.
        2. PLAN COMPLIANCE: Did Codex follow the B0 content_list exactly?
           Every item from the list should be present. No invented items.
           Correct category tags (test vs research_open vs research_formalized).
        3. FORMAT QUALITY: Does the output match the target repo's format?
           (license header, imports, AMS tags, doc comments, sorry for open items)

        Score 8+ if: all content_list items present, math correct, format matches.
        Score <5 if: Codex added items not in the plan, or got proved/open wrong.

        Findings:
        {json.dumps(findings, indent=2, ensure_ascii=False)}

        Codex self-score:
        {json.dumps(codex_score_data, indent=2, ensure_ascii=False)}

        CRITICAL: You are not just a scorer. You are a research advisor.
        If you identify a gap, state the MATHEMATICAL GOAL clearly.
        NOT "investigate further" or "consider whether". Instead:
        "Prove that X holds for all Y" or "Compute the bound on Z" or
        "Find a counterexample to W in the range [a,b]".

        Let Codex decide whether to prove it by reasoning or by writing a script.
        Your job is to identify WHAT needs to be resolved, not HOW.

        Return JSON only:
        {{
          "overall_score": 1,
          "correctness": 1,
          "usefulness_to_target": 1,
          "gift_quality": 1,
          "verdict": "pass|retry|skip",
          "notes": "short review note",
          "action_items": [
            {{
              "type": "prove|compute|verify|disprove|extend",
              "goal": "the specific mathematical question to resolve",
              "expected_result": "what a successful resolution looks like",
              "context": "relevant files, prior results, or constraints",
              "reason": "why resolving this matters for the overall contribution"
            }}
          ]
        }}
        """
    )


def dry_run_b1(repo: str, inventory: dict[str, Any]) -> dict[str, Any]:
    return {
        "summary": f"Dry-run summary for {repo}",
        "themes": ["symbolic dynamics", "Lean 4 theorem proving"],
        "connections": ["finite-state structure aligns with Automath-style recurrence analysis"],
        "pdfs": inventory.get("pdf_files", []),
        "lean_files": inventory.get("lean_files", []),
    }


def dry_run_findings(repo: str, theorem_refs: list[str]) -> list[dict[str, Any]]:
    lead_ref = theorem_refs[0] if theorem_refs else "Main.lean:12 theorem dryRunConnection"
    aux_ref = theorem_refs[1] if len(theorem_refs) > 1 else lead_ref
    return [
        {
            "title": f"{repo} finite-state recurrence bridge",
            "type": "theorem",
            "status": "proved",
            "statement": "A recurrence-compatible invariant from the target repo can be transferred to an Automath encoding.",
            "connection": "This gives a concrete theorem-shaped bridge instead of a generic collaboration pitch.",
            "proof_sketch": "Track the target invariant through the Lean definitions, then reinterpret it as an Automath transition statistic.",
            "lean_refs": [lead_ref, aux_ref],
            "automath_refs": ["README.md:1"],
            "novelty_risk": "Needs literature check against existing published recurrence-transfer results.",
        }
    ]


def normalize_findings(raw: Any) -> list[dict[str, Any]]:
    if not isinstance(raw, list):
        return []
    findings: list[dict[str, Any]] = []
    for item in raw:
        if isinstance(item, dict):
            findings.append(item)
        elif isinstance(item, str):
            findings.append({"title": item, "status": "untested"})
    return findings


def run_stage_b(
    state: RepoState,
    *,
    inventory: dict[str, Any],
    theorem_refs: list[str],
    model: Optional[str],
    dry_run: bool,
    todo_item: Optional[dict[str, str]] = None,
) -> RepoState:
    if state.stage not in {"B", "NEW"}:
        return state

    # Bug 4 fix: build real Automath theorem whitelist for grounding
    automath_theorem_whitelist = load_automath_theorem_whitelist()

    # Bug 1 fix: accumulate previous rounds' feedback to pass to next round
    previous_rounds_feedback: list[dict[str, Any]] = []

    for round_num in range(state.round + 1, MAX_RESEARCH_ROUNDS + 1):
        state.stage = "B"
        state.round = round_num
        state.timestamps.setdefault("stage_b_started_at", iso_now())
        save_state(state)

        # Bug 6 fix: activate deep research mode after low-score rounds
        low_rounds_so_far = sum(
            1 for s in state.scores.get("final", []) if s < PASS_SCORE
        )
        deep_mode = low_rounds_so_far >= DEEP_MODE_THRESHOLD
        # In deep mode, B2 gets 2x longer timeout for thorough exploration
        # deep_mode was 3600s but overnight runs hit machine sleep → full timeout chain.
        # 1800s is enough for deep research. If Codex can't find bridges in 30 min, more time won't help.
        b2_timeout = 1800

        logger.info(
            "[%s] Stage B round %d (feedback_from=%d, deep_mode=%s)",
            state.repo, round_num, len(previous_rounds_feedback), deep_mode,
        )

        is_first_round = round_num == 1 or not previous_rounds_feedback

        if dry_run:
            b1_data = dry_run_b1(state.repo, inventory)
            findings = dry_run_findings(state.repo, theorem_refs)
            b3_data = {"overall_score": 9, "decision": "advance", "notes": "dry-run score"}
            b4_data = {"overall_score": 8, "verdict": "pass", "notes": "dry-run review"}
        else:
            if is_first_round:
                # ═══ R1: FULL PIPELINE (定基调) ═══════════════════════
                # B0: plan
                todo_task = ""
                if todo_item:
                    todo_task = todo_item.get("task", "")
                b0_plan = build_content_plan(state.repo, todo_task, inventory, theorem_refs)
                logger.info("[%s] R1 B0 plan: %s", state.repo,
                            str(b0_plan.get("codex_task", ""))[:120])

                # B1: Codex reads target
                b1_raw = codex_exec(
                    build_stage_b1_prompt(state.repo, inventory),
                    work_dir=REPO_ROOT,
                    timeout=1200,
                    model=model,
                    dry_run=dry_run,
                )
                parsed_b1 = parse_json_from_output(b1_raw)
                b1_data = parsed_b1 if isinstance(parsed_b1, dict) else {}
                if not b1_data:
                    b1_data = dry_run_b1(state.repo, inventory)

                # B2: Codex finds bridges (reads existing research.md if it exists)
                # Even R1 should know about prior findings — don't start from zero
                # if there's already a research doc from previous pipeline runs.
                existing_doc = SCRIPT_DIR / "targets" / repo_slug(state.repo) / "research.md"
                existing_context = ""
                if existing_doc.exists():
                    existing_context = existing_doc.read_text(encoding="utf-8")[:5000]
                    logger.info("[%s] R1 B2 loaded existing research.md (%d chars)",
                                state.repo, len(existing_context))

                b2_raw = codex_exec(
                    build_stage_b2_prompt(
                        state.repo, b1_data,
                        automath_theorem_whitelist=automath_theorem_whitelist,
                        claude_plan=b0_plan,
                        existing_research=existing_context,
                    ),
                    work_dir=REPO_ROOT,
                    timeout=b2_timeout,
                    model=model,
                    dry_run=dry_run,
                )

            else:
                # ═══ R2+: EDIT PATH (跳过 B0/B1) ═════════════════════
                logger.info("[%s] R%d: edit-path (skip B0/B1)", state.repo, round_num)
                b2_raw = codex_exec(
                    build_stage_b2_prompt(
                        state.repo, {},
                        previous_rounds=previous_rounds_feedback,
                        automath_theorem_whitelist=automath_theorem_whitelist,
                        deep_mode=deep_mode,
                        claude_plan=b0_plan,
                    ),
                    work_dir=REPO_ROOT,
                    timeout=b2_timeout,
                    model=model,
                    dry_run=dry_run,
                )
            parsed_b2 = parse_json_from_output(b2_raw)
            findings = normalize_findings(parsed_b2.get("findings", []) if isinstance(parsed_b2, dict) else [])

            # If B2 timed out or returned empty: SKIP this round entirely.
            # Don't generate fake findings — they break the document chain.
            if not findings or b2_raw in ("(timeout)", "(start-failed)", ""):
                logger.warning("[%s] R%d B2 empty/timeout — skipping round (preserving previous findings)",
                               state.repo, round_num)
                state.log_event("B", "round skipped (B2 empty)", round=round_num)
                save_state(state)
                auto_commit_push(state.repo, "B-skip", round_num, 0, dry_run=dry_run)
                continue  # next round, keep previous findings intact

            # ─── B2.5: Codex verifies concrete claims (R2+ only) ─────
            # R1 is direction-setting, no verification needed yet.
            # R2+ does deep research with concrete claims that need checking.
            if not is_first_round and findings:
                verify_raw = codex_exec(
                    build_stage_b25_verify_prompt(state.repo, findings),
                    work_dir=REPO_ROOT,
                    timeout=600,
                    model=model,
                    dry_run=dry_run,
                )
                parsed_verify = parse_json_from_output(verify_raw)
                if isinstance(parsed_verify, dict) and parsed_verify.get("corrected_findings"):
                    corrected = normalize_findings(parsed_verify["corrected_findings"])
                    if corrected:
                        logger.info("[%s] B2.5 verification corrected %d findings",
                                    state.repo, len(corrected))
                        findings = corrected

            # ─── B2.6 (R1 only): Claude reviews bridge quality ───────
            # R1 defines the direction. Claude catches bad bridges early.
            if is_first_round and findings:
                b26_raw = claude_exec(
                    f"Review these bridge findings for {state.repo}. "
                    f"Are they genuine mathematical connections or superficial renamings? "
                    f"Which findings should be KEPT for further development? "
                    f"Which should be DROPPED? Be specific.\n\n"
                    f"Findings:\n{json.dumps(findings, indent=2, ensure_ascii=False)}\n\n"
                    f"Return JSON: {{\"keep\": [indices], \"drop\": [indices], \"notes\": \"...\"}}",
                    work_dir=REPO_ROOT,
                    timeout=600,  # B2.6 Claude bridge review
                    dry_run=dry_run,
                )
                parsed_b26 = parse_json_from_output(b26_raw)
                if isinstance(parsed_b26, dict) and parsed_b26.get("keep"):
                    keep_indices = set(parsed_b26["keep"])
                    kept = [f for i, f in enumerate(findings) if i in keep_indices]
                    if kept:
                        logger.info("[%s] B2.6 Claude kept %d/%d findings",
                                    state.repo, len(kept), len(findings))
                        findings = kept

            # (B2.5 moved above — only runs on R2+, not R1)
            if False:  # old unconditional B2.5 removed
                verify_raw = codex_exec(
                    build_stage_b25_verify_prompt(state.repo, findings),
                    work_dir=REPO_ROOT,
                    timeout=600,
                    model=model,
                    dry_run=dry_run,
                )
                parsed_verify = parse_json_from_output(verify_raw)
                if isinstance(parsed_verify, dict) and parsed_verify.get("corrected_findings"):
                    corrected = normalize_findings(parsed_verify["corrected_findings"])
                    if corrected:
                        logger.info("[%s] B2.5 verification corrected %d findings",
                                    state.repo, len(corrected))
                        findings = corrected

            b3_raw = codex_exec(
                build_stage_b3_prompt(state.repo, findings),
                work_dir=REPO_ROOT,
                timeout=900,
                model=model,
                dry_run=dry_run,
            )
            parsed_b3 = parse_json_from_output(b3_raw)
            b3_data = parsed_b3 if isinstance(parsed_b3, dict) else {}

            b4_raw = claude_exec(
                build_stage_b4_prompt(state.repo, findings, b3_data),
                work_dir=REPO_ROOT,
                timeout=900,
                dry_run=dry_run,
            )
            parsed_b4 = parse_json_from_output(b4_raw)
            b4_data = parsed_b4 if isinstance(parsed_b4, dict) else {}

        # Bug 2 fix: fallback score = 0 (not 10) when Codex fails.
        codex_score = coerce_score(b3_data.get("overall_score"), 0)
        claude_score = coerce_score(b4_data.get("overall_score"), 0)
        if codex_score == 0 and claude_score == 0:
            final_score = 0
        elif codex_score == 0:
            final_score = claude_score
        elif claude_score == 0:
            final_score = codex_score
        else:
            final_score = min(codex_score, claude_score)

        # Bug 8 fix: ACCUMULATE best findings across rounds instead of overwriting.
        # Keep current round's findings if better; otherwise keep previous best.
        prev_best_score = max(state.scores.get("final", []) or [0])
        if final_score >= prev_best_score or not state.findings:
            state.findings = findings  # this round is the new best
            logger.info("[%s] Round %d becomes new best (score %d >= prev %d)",
                        state.repo, round_num, final_score, prev_best_score)
        else:
            logger.info("[%s] Round %d not better (score %d < prev best %d), keeping previous findings",
                        state.repo, round_num, final_score, prev_best_score)
        state.scores.setdefault("codex", []).append(codex_score)
        state.scores.setdefault("claude", []).append(claude_score)
        state.scores.setdefault("final", []).append(final_score)

        # Document-driven memory: write full findings + review to a file
        # so next round's Codex can READ the complete document, not just a summary.
        # Write to targets/{repo}/research.md — single file, git tracks versions
        target_dir = SCRIPT_DIR / "targets" / repo_slug(state.repo)
        target_dir.mkdir(parents=True, exist_ok=True)
        doc_path = target_dir / "research.md"
        # If doc exists, read it and append Claude review. If not, write from scratch.
        existing_doc = ""
        if doc_path.exists():
            existing_doc = doc_path.read_text(encoding="utf-8")

        if existing_doc:
            # Append new review to existing doc
            review_entry = (
                f"\n\n## Claude Review R{round_num} (codex={codex_score}, claude={claude_score})\n"
                f"{b4_data.get('notes', 'no review')}\n"
            )
            doc_content = existing_doc + review_entry
        else:
            # Create new doc with findings
            doc_content = f"# {state.repo} — Research Document\n\n"
            doc_content += f"## Findings\n"
            for i, f_item in enumerate(findings):
                if isinstance(f_item, dict):
                    doc_content += f"\n### Finding {i+1}: {f_item.get('title', 'untitled')}\n"
                    for k in ['type', 'status', 'their_side', 'our_side', 'bridge',
                               'target_need', 'statement', 'connection', 'proof_sketch',
                               'automath_refs', 'novelty_risk']:
                        v = f_item.get(k)
                        if v:
                            doc_content += f"- **{k}**: {v}\n"
            doc_content += f"\n## Claude Review R{round_num} (codex={codex_score}, claude={claude_score})\n"
            doc_content += f"{b4_data.get('notes', 'no review')}\n"
        try:
            doc_path.parent.mkdir(parents=True, exist_ok=True)
            doc_path.write_text(doc_content, encoding="utf-8")
            logger.info("[%s] Wrote research doc: %s (%d chars)", state.repo, doc_path.name, len(doc_content))
        except Exception as exc:
            logger.warning("[%s] Failed to write doc: %s", state.repo, exc)

        previous_rounds_feedback.append({
            "round": round_num,
            "codex_score": codex_score,
            "claude_score": claude_score,
            "claude_notes": str(b4_data.get("notes", ""))[:1000],
            "codex_notes": str(b3_data.get("notes", ""))[:500],
            "action_items": b4_data.get("action_items", []),  # Claude's actionable fixes
            "doc_path": str(doc_path),  # Codex can `cat` this file next round
            "findings_summary": [
                {
                    "title": f.get("title", "")[:120],
                    "type": f.get("type", ""),
                    "status": f.get("status", ""),
                    "connection": str(f.get("connection", ""))[:200],
                }
                for f in findings[:5]
            ],
        })

        state.log_event(
            "B",
            "research round completed",
            round=round_num,
            score=final_score,
            detail=json.dumps(
                {
                    "codex_score": codex_score,
                    "claude_score": claude_score,
                    "claude_notes": str(b4_data.get("notes", ""))[:500],
                    "findings": findings[:3],
                },
                ensure_ascii=False,
            ),
        )
        save_state(state)
        auto_commit_push(state.repo, "B", round_num, final_score, dry_run=dry_run)

        # Backflow only on final round (research complete, not mid-iteration)
        # Bug 8 fix: pass gate uses GLOBAL BEST score across all rounds,
        # not just current round. This prevents good findings from being discarded
        # just because the latest round tried a worse angle.
        global_best = max(state.scores.get("final", []) or [final_score])
        if global_best >= PASS_SCORE:
            state.stage = "C"
            state.round = 0
            state.timestamps["stage_b_completed_at"] = iso_now()
            state.log_event("B", "passed research gate", score=global_best,
                            verdict="advance",
                            detail=f"global_best={global_best} (current_round={final_score})")
            save_state(state)

            # Phase 2.5: BACKFLOW — Codex proposes placement, Claude reviews, generate .tex
            backflow_placement = backflow_to_main_paper(state, model=model, dry_run=dry_run)

            return state

        if len(state.scores["final"]) >= LOW_SCORE_STREAK and all(
            score < LOW_SCORE_SKIP for score in state.scores["final"][-LOW_SCORE_STREAK:]
        ):
            state.stage = "SKIPPED"
            state.error = ""
            state.timestamps["completed_at"] = iso_now()
            state.log_event("B", "skipped after low-score streak", score=final_score, verdict="skip")
            save_state(state)
            auto_commit_push(state.repo, "B", round_num, final_score, dry_run=dry_run)
            mark_processed(state.repo, dry_run=dry_run)
            return state

    state.stage = "SKIPPED"
    state.timestamps["completed_at"] = iso_now()
    last_score = state.scores["final"][-1] if state.scores["final"] else 0
    state.log_event("B", "max research rounds exhausted", score=last_score)
    save_state(state)

    # Backflow on final round — research is done, write to main paper
    backflow_to_main_paper(state, model=model, dry_run=dry_run)

    auto_commit_push(state.repo, "B-exhausted", MAX_RESEARCH_ROUNDS, last_score, dry_run=dry_run)
    mark_processed(state.repo, dry_run=dry_run)
    return state


# ---------------------------------------------------------------------------
# Stage C: draft issue
# ---------------------------------------------------------------------------


def build_stage_c1_prompt(
    repo: str,
    findings: list[Any],
    theorem_refs: list[str],
    inventory: dict[str, Any],
    revision_note: str = "",
    backflow_placement: Optional[dict[str, Any]] = None,
) -> str:
    note_block = f"User revision note:\n{revision_note}\n\n" if revision_note else ""

    # If backflow was done, include links to the paper section and bridge doc
    backflow_context = ""
    if backflow_placement:
        gen = backflow_placement.get("gen_result", {})
        bridge_path = gen.get("bridge_doc_path", "")
        if bridge_path:
            # Convert absolute path to GitHub URL
            rel_path = str(bridge_path).replace(str(REPO_ROOT) + "/", "")
            backflow_context = (
                f"\n\nBACKFLOW COMPLETED: The research has been written into the Omega paper.\n"
                f"- Paper section: {backflow_placement.get('placement', 'appendix')}/{backflow_placement.get('section_dir', '')}\n"
                f"- Bridge document (linkable): {AUTOMATH_REPO_URL}/blob/dev/{rel_path}\n"
                f"- Verification scripts: referenced in the bridge doc\n\n"
                f"Your issue/reply MUST reference the bridge document URL above.\n"
                f"This is how readers can verify the claims — link to the repo, not just prose.\n"
            )

    return textwrap.dedent(
        f"""\
        You are Stage C1 of a community outreach pipeline.

        Draft a GitHub issue or issue reply for repository {repo}.
        This must read like a serious technical contribution, not a pitch.
        {backflow_context}
        Requirements:
        - Include the main theorem statement(s) and proof sketch
        - Reference verification scripts and computational certificates
        - If a bridge document exists, link it prominently
        - Cite Lean 4 theorem references using exact file:line form
        - Honest proved/conjectured/untested labeling
        - Avoid self-promotion. Lead with the math, mention the repo naturally.
        - The body must end with exactly:
          {AUTOMATH_TRAILER}
        - Return JSON only.

        {note_block}Findings:
        {json.dumps(findings, indent=2, ensure_ascii=False)}

        Lean theorem refs:
        {json.dumps(theorem_refs[:40], indent=2, ensure_ascii=False)}

        Repository inventory:
        {json.dumps(inventory, indent=2, ensure_ascii=False)}

        JSON schema:
        {{
          "title": "issue title",
          "body": "markdown issue body"
        }}
        """
    )


def build_stage_c2_prompt(repo: str, title: str, body: str) -> str:
    return textwrap.dedent(
        f"""\
        You are Stage C2 of a community outreach pipeline.

        Review the GitHub issue draft below for repository {repo}.
        Check:
        - technical accuracy
        - tone (no self-promotion)
        - honest proved/conjectured/untested labeling
        - Lean 4 theorem references look plausible and specific
        - body ends with {AUTOMATH_TRAILER}

        Return JSON only:
        {{
          "approved": true,
          "overall_score": 1,
          "title": "possibly revised title",
          "body": "possibly revised body",
          "notes": "short review note"
        }}

        Draft title:
        {title}

        Draft body:
        {body}
        """
    )


def fallback_draft(repo: str, findings: list[dict[str, Any]], theorem_refs: list[str]) -> tuple[str, str]:
    title = f"Potential formal bridge between {repo.split('/')[-1]} and Automath"
    rows = []
    for item in findings[:5]:
        status = item.get("status", "untested")
        rows.append(
            f"| {item.get('title', 'Unnamed connection')} | {status} | "
            f"{'; '.join(item.get('lean_refs', theorem_refs[:1])) or 'n/a'} | "
            f"{item.get('connection', '')} |"
        )
    if not rows:
        rows.append("| Candidate connection | untested | n/a | Requires fresh validation |")

    body = "\n".join(
        [
            "I have been comparing this Lean 4 repository against Automath and found a few contribution-shaped bridges that look worth checking.",
            "",
            "| Correspondence | Status | Lean refs | Evidence |",
            "| --- | --- | --- | --- |",
            *rows,
            "",
            "### Proof Sketches",
            *[
                f"- **{item.get('title', 'Connection')}**: {item.get('proof_sketch', 'Validation path still needs full formal checking.')}"
                for item in findings[:5]
            ],
            "",
            "### Why This Might Matter",
            "- The overlap is specific enough to support a concrete theorem-level discussion instead of a generic collaboration request.",
            "- The proved/conjectured/untested split keeps the proposal honest about current evidence.",
            "",
            AUTOMATH_TRAILER,
        ]
    )
    return title, sanitize_issue_text(body)


def run_stage_c(
    state: RepoState,
    *,
    inventory: dict[str, Any],
    theorem_refs: list[str],
    revision_note: str,
    model: Optional[str],
    dry_run: bool,
    backflow_placement: Optional[dict[str, Any]] = None,
) -> RepoState:
    if state.stage not in {"C", "D"}:
        return state

    # Stage C runs AFTER backflow. The reply/issue draft references the paper section
    # and bridge document that backflow produced.
    state.stage = "C"
    state.round = 1
    state.timestamps.setdefault("stage_c_started_at", iso_now())
    save_state(state)
    logger.info("[%s] Stage C (C1 only, user is final gate, backflow=%s)",
                state.repo, "yes" if backflow_placement else "no")

    if dry_run:
        title, body = fallback_draft(state.repo, normalize_findings(state.findings), theorem_refs)
    else:
        c1_raw = codex_exec(
            build_stage_c1_prompt(
                state.repo, normalize_findings(state.findings), theorem_refs,
                inventory, revision_note, backflow_placement=backflow_placement,
            ),
            work_dir=REPO_ROOT,
            timeout=1200,
            model=model,
            dry_run=dry_run,
        )
        parsed_c1 = parse_json_from_output(c1_raw)
        if isinstance(parsed_c1, dict):
            title = str(parsed_c1.get("title", "")).strip()
            body = sanitize_issue_text(str(parsed_c1.get("body", "")).strip())
        else:
            title, body = "", ""
        if not title or not body:
            title, body = fallback_draft(state.repo, normalize_findings(state.findings), theorem_refs)

    state.draft_title = title
    state.draft_body = sanitize_issue_text(body)
    state.log_event(
        "C",
        "draft created by C1 (auto-approved, user reviews in Stage D)",
        round=1,
        score=8,
        verdict="advance",
        detail=f"title={title[:120]!r} body_len={len(state.draft_body)}",
    )
    save_state(state)

    if state.draft_title and state.draft_body:
        state.stage = "D"
        state.round = 0
        state.timestamps["stage_c_completed_at"] = iso_now()
        save_state(state)
        auto_commit_push(state.repo, "C", 1, 8, dry_run=dry_run)
        return state

    # C1 produced empty output — hard failure
    state.stage = "SKIPPED"
    state.timestamps["completed_at"] = iso_now()
    state.log_event("C", "C1 produced empty draft", verdict="skip")
    save_state(state)
    mark_processed(state.repo, dry_run=dry_run)
    return state


# ---------------------------------------------------------------------------
# Stage D: interactive approval + submission
# ---------------------------------------------------------------------------


def create_issue(repo: str, title: str, body: str, *, dry_run: bool) -> str:
    if dry_run:
        return f"https://github.com/{repo}/issues/DRY-RUN"

    gh_bin = ensure_binary(GH_PATH, "gh")
    result = run_cmd(
        [gh_bin, "issue", "create", "--repo", repo, "--title", title, "--body", body],
        cwd=REPO_ROOT,
        timeout=600,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or result.stdout.strip() or "gh issue create failed")
    lines = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    return lines[-1] if lines else ""


def stage_d_prompt(state: RepoState) -> str:
    return "\n".join(
        [
            "=" * 80,
            f"Target repo: {state.repo}",
            f"Title: {state.draft_title}",
            "",
            state.draft_body,
            "",
        ]
    )


def run_stage_d(state: RepoState, *, dry_run: bool) -> tuple[RepoState, str]:
    state.stage = "D"
    save_state(state)

    if dry_run:
        logger.info("[%s] Stage D dry-run preview", state.repo)
        logger.info("%s", stage_d_prompt(state))
        state.log_event("D", "dry-run preview generated")
        save_state(state)
        return state, ""

    print(stage_d_prompt(state))
    while True:
        action = input("Action [approve/revise/skip]: ").strip().lower()
        if action == "approve":
            url = create_issue(state.repo, state.draft_title, state.draft_body, dry_run=dry_run)
            state.submission_url = url
            state.stage = "DONE"
            state.timestamps["completed_at"] = iso_now()
            state.log_event("D", "issue submitted", verdict="approve", detail=url)
            save_state(state)
            auto_commit_push(state.repo, "D", 0, 10, dry_run=dry_run)
            mark_processed(state.repo, dry_run=dry_run)
            return state, ""
        if action == "revise":
            note = input("Revision notes (optional): ").strip()
            state.stage = "C"
            state.round = 0
            state.log_event("D", "revision requested", verdict="revise", detail=note)
            save_state(state)
            return state, note
        if action == "skip":
            state.stage = "SKIPPED"
            state.timestamps["completed_at"] = iso_now()
            state.log_event("D", "skipped by user", verdict="skip")
            save_state(state)
            mark_processed(state.repo, dry_run=dry_run)
            return state, ""
        print("Please enter approve, revise, or skip.")


# ---------------------------------------------------------------------------
# Orchestration
# ---------------------------------------------------------------------------


def ensure_state(repo: str, *, skip_to: str) -> RepoState:
    state = load_state(repo) or RepoState(repo=repo)
    state.timestamps.setdefault("created_at", iso_now())
    if skip_to:
        state.stage = skip_to
        state.round = 0
        state.error = ""
        state.log_event(skip_to, "stage override requested")
    elif state.stage in {"DONE", "SKIPPED"} and not state.submission_url:
        logger.info("[%s] State already terminal at %s", repo, state.stage)
    save_state(state)
    return state


def process_repo_to_stage_d(
    repo: str,
    *,
    skip_to: str,
    model: Optional[str],
    dry_run: bool,
    todo_item: Optional[dict[str, str]] = None,
) -> RepoState:
    if not valid_repo_slug(repo):
        state = RepoState(repo=repo, stage="ERROR", error="Invalid repo slug")
        save_state(state)
        return state

    state = ensure_state(repo, skip_to=skip_to)
    if state.stage == "DONE" and not skip_to:
        return state

    try:
        with repo_checkout(repo, dry_run=dry_run) as repo_path:
            inventory = repo_inventory(repo_path, repo)
            theorem_refs = extract_lean_theorem_refs(repo_path)

            # Stage B produces research + backflow placement
            backflow_placement = None
            if state.stage == "B":
                state = run_stage_b(
                    state,
                    inventory=inventory,
                    theorem_refs=theorem_refs,
                    model=model,
                    dry_run=dry_run,
                    todo_item=todo_item,
                )
                # Retrieve backflow placement from state events
                for evt in reversed(state.events):
                    if evt.get("action") == "backflow completed":
                        try:
                            backflow_placement = json.loads(evt.get("detail", "{}"))
                        except (json.JSONDecodeError, TypeError):
                            pass
                        break

            # Stage C drafts the reply AFTER backflow (references paper section)
            if state.stage == "C":
                state = run_stage_c(
                    state,
                    inventory=inventory,
                    theorem_refs=theorem_refs,
                    revision_note="",
                    model=model,
                    dry_run=dry_run,
                    backflow_placement=backflow_placement,
                )

            return state
    except Exception as exc:
        state.stage = "ERROR"
        state.error = str(exc)
        state.log_event(state.stage, "processing failed", detail=str(exc))
        save_state(state)
        logger.exception("[%s] Processing failed", repo)
        return state


def complete_repo_interactively(
    state: RepoState,
    *,
    model: Optional[str],
    dry_run: bool,
) -> RepoState:
    while state.stage == "D":
        state, revision_note = run_stage_d(state, dry_run=dry_run)
        if state.stage != "C":
            return state
        with repo_checkout(state.repo, dry_run=dry_run) as repo_path:
            inventory = repo_inventory(repo_path, state.repo)
            theorem_refs = extract_lean_theorem_refs(repo_path)
            state = run_stage_c(
                state,
                inventory=inventory,
                theorem_refs=theorem_refs,
                revision_note=revision_note,
                model=model,
                dry_run=dry_run,
            )
    return state


def process_repositories(
    repos: list[str],
    *,
    parallel: int,
    skip_to: str,
    model: Optional[str],
    dry_run: bool,
    todo_item: Optional[dict[str, str]] = None,
) -> list[RepoState]:
    unique_repos = []
    seen = set()
    for repo in repos:
        if repo not in seen:
            unique_repos.append(repo)
            seen.add(repo)

    if not unique_repos:
        return []

    logger.info("Processing %d repositories (parallel=%d)", len(unique_repos), parallel)
    states: list[RepoState] = []
    worker_count = max(1, parallel)
    if worker_count == 1:
        for repo in unique_repos:
            states.append(process_repo_to_stage_d(repo, skip_to=skip_to, model=model, dry_run=dry_run, todo_item=todo_item))
    else:
        with ThreadPoolExecutor(max_workers=worker_count) as executor:
            future_map = {
                executor.submit(
                    process_repo_to_stage_d,
                    repo,
                    skip_to=skip_to,
                    model=model,
                    dry_run=dry_run,
                ): repo
                for repo in unique_repos
            }
            for future in as_completed(future_map):
                repo = future_map[future]
                try:
                    states.append(future.result())
                except Exception as exc:
                    logger.exception("[%s] Worker failed", repo)
                    failed = RepoState(repo=repo, stage="ERROR", error=str(exc))
                    save_state(failed)
                    states.append(failed)
    return sorted(states, key=lambda state: state.repo)


# ---------------------------------------------------------------------------
# Status / CLI
# ---------------------------------------------------------------------------


def print_status() -> None:
    states = load_all_states()
    processed = load_processed_repos()
    print(f"Community outreach states: {len(states)}")
    print(f"Processed repos: {len(processed)}")
    if CANDIDATES_FILE.exists():
        print(f"Candidates file: {CANDIDATES_FILE}")
    print("")
    for state in sorted(states, key=lambda item: item.repo):
        final_scores = state.scores.get("final", [])
        codex_scores = state.scores.get("codex", [])
        claude_scores = state.scores.get("claude", [])
        print(state.repo)
        print(f"  Stage:    {state.stage}")
        print(f"  Round:    {state.round}")
        print(f"  Scores:   codex={codex_scores} claude={claude_scores} final={final_scores}")
        if state.submission_url:
            print(f"  Issue:    {state.submission_url}")
        if state.error:
            print(f"  Error:    {state.error}")
        print("")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Community outreach pipeline for GitHub mathematical contributions",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent(
            """\
            Examples:
              python3 tools/community-outreach/outreach_pipeline.py --status
              python3 tools/community-outreach/outreach_pipeline.py --discover --parallel 2
              python3 tools/community-outreach/outreach_pipeline.py --repo owner/name
              python3 tools/community-outreach/outreach_pipeline.py --repo owner/name --skip-to C
            """
        ),
    )
    parser.add_argument("--discover", action="store_true", help="Run Stage A discovery and process the resulting candidates")
    parser.add_argument("--repo", action="append", default=[], help="Target repository in owner/name form; repeatable")
    parser.add_argument("--todo", action="store_true", help="Claim and process next TODO item from TODO.md")
    parser.add_argument("--status", action="store_true", help="Show persisted state")
    parser.add_argument("--skip-to", choices=["B", "C", "D"], default="", help="Override the starting stage for --repo targets")
    parser.add_argument("--parallel", "-p", type=int, default=1, help="Number of repositories to process in parallel")
    parser.add_argument("--dry-run", action="store_true", help="Do not call external services or submit issues")
    parser.add_argument("--model", default=None, help="Override Codex model")
    return parser.parse_args()


TODO_FILE = SCRIPT_DIR / "TODO.md"


def parse_todo() -> list[dict[str, str]]:
    """Parse TODO.md, return list of unclaimed items with id, repo, task description."""
    if not TODO_FILE.exists():
        return []
    items: list[dict[str, str]] = []
    for line in TODO_FILE.read_text(encoding="utf-8").splitlines():
        # Match: - [ ] **FC-01**: description
        m = re.match(r"^- \[ \] \*\*(\w+-\d+)\*\*:\s*(.*)", line)
        if not m:
            continue
        item_id = m.group(1)
        desc = m.group(2).strip()
        # Extract repo from context (section headers above)
        # FC = formal-conjectures, EQ = equational_theories, FB = FormalBook, etc.
        repo_map = {
            "FC": "google-deepmind/formal-conjectures",
            "EQ": "teorth/equational_theories",
            "FB": "mo271/FormalBook",
            "RH": "math-inc/RiemannHypothesisCurves",
            "ZU": "",  # Zulip, no repo
        }
        prefix = item_id.split("-")[0]
        repo = repo_map.get(prefix, "")
        if repo:
            items.append({"id": item_id, "repo": repo, "task": desc})
    return items


def claim_todo(item_id: str) -> None:
    """Mark a TODO item as CLAIMED in TODO.md."""
    if not TODO_FILE.exists():
        return
    content = TODO_FILE.read_text(encoding="utf-8")
    old = f"- [ ] **{item_id}**:"
    new = f"- [~] **{item_id}** (CLAIMED):"
    if old in content:
        TODO_FILE.write_text(content.replace(old, new, 1), encoding="utf-8")
        logger.info("Claimed TODO item: %s", item_id)


def complete_todo(item_id: str, result: str = "DONE") -> None:
    """Mark a TODO item as DONE or SKIP in TODO.md."""
    if not TODO_FILE.exists():
        return
    content = TODO_FILE.read_text(encoding="utf-8")
    # Match both unclaimed and claimed states
    for pattern in [f"- [~] **{item_id}** (CLAIMED):", f"- [ ] **{item_id}**:"]:
        if pattern in content:
            if result == "DONE":
                content = content.replace(pattern, f"- [x] **{item_id}** (DONE):", 1)
            else:
                content = content.replace(pattern, f"- [-] **{item_id}** (SKIP):", 1)
            TODO_FILE.write_text(content, encoding="utf-8")
            logger.info("Marked TODO %s as %s", item_id, result)
            return


def main() -> int:
    args = parse_args()

    if args.status:
        print_status()
        return 0

    repos: list[str] = []
    todo_item: Optional[dict[str, str]] = None

    if args.todo:
        items = parse_todo()
        if not items:
            print("No TODO items available.", file=sys.stderr)
            return 0
        todo_item = items[0]
        claim_todo(todo_item["id"])
        repos.append(todo_item["repo"])
        logger.info("Claimed TODO: %s → %s (%s)", todo_item["id"], todo_item["repo"], todo_item["task"][:80])
        auto_commit_push(todo_item["repo"], "TODO", 0, 0, dry_run=args.dry_run)

    if args.discover:
        candidates = discover_candidates(model=args.model, dry_run=args.dry_run)
        repos.extend(item["repo"] for item in candidates)
    repos.extend(args.repo)

    if not repos:
        print("Specify --discover, --repo, or --status.", file=sys.stderr)
        return 1

    for repo in args.repo:
        if not valid_repo_slug(repo):
            print(f"Invalid repo slug: {repo}", file=sys.stderr)
            return 1

    states = process_repositories(
        repos,
        parallel=args.parallel,
        skip_to=args.skip_to,
        model=args.model,
        dry_run=args.dry_run,
        todo_item=todo_item,
    )

    if not args.dry_run:
        for idx, state in enumerate(states):
            if state.stage == "D":
                logger.info("[%d/%d] Entering Stage D for %s", idx + 1, len(states), state.repo)
                states[idx] = complete_repo_interactively(state, model=args.model, dry_run=args.dry_run)

    failed = [state for state in states if state.stage == "ERROR"]
    skipped = [state for state in states if state.stage == "SKIPPED"]
    ready = [state for state in states if state.stage == "D"]
    done = [state for state in states if state.stage == "DONE"]

    logger.info(
        "Run summary: done=%d ready=%d skipped=%d failed=%d",
        len(done),
        len(ready),
        len(skipped),
        len(failed),
    )

    # Update TODO status if running in --todo mode
    if todo_item:
        if done:
            complete_todo(todo_item["id"], "DONE")
        elif skipped:
            complete_todo(todo_item["id"], "SKIP")
        auto_commit_push(
            todo_item.get("repo", "TODO"),
            "TODO-complete",
            0,
            max((s.scores.get("final", []) or [0])[-1] for s in states) if states else 0,
            dry_run=args.dry_run,
        )

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
