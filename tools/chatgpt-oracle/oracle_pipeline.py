#!/usr/bin/env python3
"""Oracle Pipeline v2 — 两条管线、条件循环、每步 commit、轮次追踪。

═══════════════════════════════════════════════════════════════
管线一: 新文章 (--new)  N0 → N1 → N2 → N3 → 自动进入管线二
═══════════════════════════════════════════════════════════════
  N0: Codex 期刊选择 — 根据主题/大纲内容选最佳投稿期刊 (JSON)
  N1: Codex 深度研究 — 基于主题/大纲产出新定理+证明 → commit
  N2: Codex 组装论文骨架 — 生成完整 .tex 框架 → commit
  N3: Codex 期刊风格初稿 — 按 N0 选定期刊风格写完整论文 → commit
  → 自动进入 Review 管线 Stage F

═══════════════════════════════════════════════════════════════
管线二: Review 已有文章 (默认)  F → A → B → C → D
═══════════════════════════════════════════════════════════════
  Stage F: 期刊方向适配（fit-check, ≥6 pass, 否则自动建议更合适期刊）
    F1: Codex 评估论文 vs 目标期刊适配度 (JSON)
    F2: Claude review 适配评估
    Gate: fit_score ≥ 6 → Stage A (原目标期刊)
          fit_score < 6 → 自动切换到建议期刊, 进入 Stage A

  Stage A: Codex Review + 风格优化（score-gated loop, ≥8 pass）
    A1: Codex review 质量 + 修复 → commit
    A2: Codex 期刊风格优化 → commit
    A3: Codex 自评 1-10 分
    A4: Claude review 评价
    Gate: min(codex, claude) ≥ 8 → Stage B; else → A1 (max 5 rounds)

  Stage B: Oracle 审稿（minor-revision-gated loop）
    B1: 编译 PDF → commit
    B2: Oracle editorial review → EVENT WAIT
    B3: 解析 verdict
    Gate: verdict ∈ {accept, minor revision} → Stage C
    B4: Codex fix issues → commit
    B5: Claude review fixes → commit
    → B1 (max 4 rounds)

  Stage C: Claude 独立审阅（approval-gated loop）
    C1: Claude 独立审阅 → 返回 verdict
    Gate: verdict = submit → Stage D
    C2: Codex fix → commit
    → C1 (max 4 rounds)

  Stage D: 回流主论文
    D1: Codex 检查回流候选 → 返回 backflow items
    D2: Claude review 回流方案
    Gate: approved → D3
    D3: Codex 修改主论文 → commit
    D4: Codex 验证 → commit
    D5: Claude 审阅回流质量 → 不满意则 Codex 补充修改 → commit

Usage:
  # Review 已有文章:
  python3 oracle_pipeline.py --paper theory/2026_xxx/ --target-journal "Adv. Math."

  # 新文章:
  python3 oracle_pipeline.py --new --topic "Golden ratio folding" --target-journal "Adv. Math."
  python3 oracle_pipeline.py --new --outline outline.md --target-journal "JEMS"

  # 通用:
  python3 oracle_pipeline.py --all --parallel 2 --continuous
  python3 oracle_pipeline.py --status
  python3 oracle_pipeline.py --dry-run --all
"""

from __future__ import annotations

import argparse
import base64
import json
import logging
import os
import re
import shutil
import subprocess
import sys
import textwrap
import threading
import time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED, Future
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional

# ---------------------------------------------------------------------------
# Paths & constants
# ---------------------------------------------------------------------------

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
THEORY_DIR = REPO_ROOT / "theory"
LOG_DIR = SCRIPT_DIR / "logs"
STATE_DIR = SCRIPT_DIR / "pipeline_state"

ORACLE_SERVER = "http://127.0.0.1:8765"
PAPERS_PUB_DIR_CONST = REPO_ROOT / "papers" / "publication"

# Platform-aware Codex discovery
def _find_codex() -> str:
    found = shutil.which("codex")
    if found:
        return found
    if sys.platform == "win32":
        npm_codex = Path.home() / "AppData" / "Roaming" / "npm" / "codex.cmd"
        if npm_codex.exists():
            return str(npm_codex)
    elif sys.platform == "darwin":
        for p in ("/opt/homebrew/bin/codex", "/usr/local/bin/codex"):
            if Path(p).exists():
                return p
    return "codex"

CODEX_PATH = _find_codex()
IS_WINDOWS = sys.platform == "win32"

# ── Machine assignment ─────────────────────────────────────────────────
# Split 21 papers between two machines to avoid git conflicts.
# Each machine only processes its assigned papers.
# Windows (this machine if IS_WINDOWS): has Oracle server + Tampermonkey
# Mac: parallel Codex processing
#
# Assignment: roughly balanced by review maturity (real review count).
# Papers with more reviews = closer to done = Windows (Oracle machine).
# Newer papers = more Codex work needed = Mac.

MACHINE_ASSIGNMENT = {
    # ── Windows machine (PAUSED as of 2026-04-17) ────────────────
    # Not processing any papers currently
    "win32": [],
    # ── Mac machine (claiming ALL 21 papers, Windows paused) ────
    "darwin": [
        # Originally Windows-assigned (11 papers, close to acceptance):
        "2026_circle_dimension_haar_pullback_cauchy_weight_jfa",
        "2026_conservative_extension_chain_state_forcing_apal",
        "2026_conservative_extension_chain_state_forcing_apal_focused",
        "2026_dynamical_zeta_finite_part_spectral_fingerprint_etds",
        "2026_JphisComm_待投稿",
        "2026_prime_languages_sofic_obstructions_dynamical_zeta",
        "2026_yang_lee_quartic_spectral_curve_discriminant_factorization_lee_yang_edge_singularity",
        "2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists",
        "2026_scan_projection_address_semantics_sigma_nonexpansion_etds",
        "2026_recursive_addressing_prefix_sites_tac",
        "2026_fredholm_witt_cyclic_block_spectral_rigidity_symbolic_zeta",
        # Originally Mac-assigned (10 papers):
        "2026_cubical_stokes_inverse_boundary_readout_jdsgt",
        "2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints",
        "2026_fold_truncation_defect_stokes_dynamical_systems",
        "2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal",
        "2026_prefix_scan_error_boundary_rates_dynamical_systems",
        "2026_projection_ontological_mathematics_core_tams",
        "2026_chebotarev_quotient_entropy_fold_groupoid_rigidity",
        "2026_joukowsky_elliptic_godel_lorentz_mahler_capacity",
        "2026_window6_spectral_rigidity_hypercube_lumpability_fold_gauge",
        "2026_zeckendorf_stable_arithmetic_fibonacci_congruence_online",
    ],
}

def get_my_papers() -> list[str]:
    """Return paper dir names assigned to this machine."""
    return MACHINE_ASSIGNMENT.get(sys.platform, [])

_git_lock = threading.Lock()
_state_lock = threading.Lock()

# Stage gate thresholds
SCORE_PASS_THRESHOLD = 8

# Known journal abbreviation → full name mapping
JOURNAL_ABBREV = {
    "jfa": "Journal of Functional Analysis",
    "apal": "Annals of Pure and Applied Logic",
    "etds": "Ergodic Theory and Dynamical Systems",
    "tams": "Transactions of the American Mathematical Society",
    "tac": "Theory and Applications of Categories",
    "jdsgt": "Journal of Dynamics and Differential Equations",
    "jphiscomm": "Journal of Physics Communications",
    "jphyscomm": "Journal of Physics Communications",
    "jst": "Journal of Spectral Theory",
    "jems": "Journal of the European Mathematical Society",
    "cmp": "Communications in Mathematical Physics",
    "adv": "Advances in Mathematics",
    "iumj": "Indiana University Mathematics Journal",
    "imrn": "International Mathematics Research Notices",
    "plms": "Proceedings of the London Mathematical Society",
    "jlms": "Journal of the London Mathematical Society",
    "crelle": "Journal für die reine und angewandte Mathematik",
    "duke": "Duke Mathematical Journal",
    "gafa": "Geometric and Functional Analysis",
    "am": "Annals of Mathematics",
    "acta": "Acta Mathematica",
    "inventiones": "Inventiones Mathematicae",
}


PROGRAM_BOARD = REPO_ROOT / "papers" / "publication" / "PROGRAM_BOARD.md"

# Normalized short names used in PROGRAM_BOARD.md → match to dir names
_BOARD_JOURNAL_EXPAND = {
    "ergodic th. dyn. sys.": "Ergodic Theory and Dynamical Systems",
    "ann. pure appl. logic": "Annals of Pure and Applied Logic",
    "trans. ams": "Transactions of the American Mathematical Society",
    "j. funct. anal.": "Journal of Functional Analysis",
    "j. spectral theory": "Journal of Spectral Theory",
    "monatshefte math.": "Monatshefte für Mathematik",
    "dynamical systems": "Ergodic Theory and Dynamical Systems",
    "imrn": "International Mathematics Research Notices",
}


def _load_board_journals() -> dict[str, str]:
    """Parse PROGRAM_BOARD.md and return {dir_keyword: full_journal_name}."""
    result: dict[str, str] = {}
    if not PROGRAM_BOARD.exists():
        return result
    try:
        text = PROGRAM_BOARD.read_text(encoding="utf-8")
    except Exception:
        return result

    # Match table rows: | Paper desc | Target journal | Stage | Status |
    for m in re.finditer(
        r"\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*P\d",
        text,
    ):
        paper_desc = m.group(1).strip()
        raw_journal = m.group(2).strip()

        # Expand abbreviated journal name
        journal = _BOARD_JOURNAL_EXPAND.get(raw_journal.lower(), raw_journal)

        # Extract dir-name hint from paper desc or parenthetical
        # e.g. "ETDS (scan projection)" → "scan_projection"
        # e.g. "JFA (circle dimension)" → "circle_dimension"
        paren = re.search(r"\(([^)]+)\)", paper_desc)
        if paren:
            key = paren.group(1).strip().lower().replace(" ", "_")
            result[key] = journal

        # Also store the short name itself: "ETDS-zeta" → "etds_zeta"
        short = paper_desc.split("(")[0].strip().lower()
        short = re.sub(r"[^a-z0-9]+", "_", short).strip("_")
        if short:
            result[short] = journal

    return result


# ── PROGRAM_BOARD.md full-table parser ────────────────────────────────
# The board is the single source of truth for paper status and journal
# targets.  discover_papers() uses it to skip submitted/published papers
# and to refuse unregistered papers.

_board_entries: Optional[dict[str, dict]] = None


def _load_board_entries() -> dict[str, dict]:
    """Parse PROGRAM_BOARD.md status table.

    Expected row format (backtick-wrapped dir name):
      | `dir_name` | journal | status | reroute |

    Returns {dir_name: {"journal": str, "status": str, "reroute": str}}.
    """
    result: dict[str, dict] = {}
    if not PROGRAM_BOARD.exists():
        return result
    try:
        text = PROGRAM_BOARD.read_text(encoding="utf-8")
    except Exception:
        return result

    for m in re.finditer(
        r"\|\s*`([^`]+)`\s*\|\s*([^|]*?)\s*\|\s*([^|]*?)\s*\|\s*([^|]*?)\s*\|",
        text,
    ):
        dir_name = m.group(1).strip()
        journal = m.group(2).strip()
        status = m.group(3).strip()
        reroute = m.group(4).strip()
        result[dir_name] = {
            "journal": journal,
            "status": status,
            "reroute": reroute,
        }
    return result


def _get_board_entries() -> dict[str, dict]:
    global _board_entries
    if _board_entries is None:
        _board_entries = _load_board_entries()
    return _board_entries


def _invalidate_board_cache() -> None:
    """Invalidate cached board entries (call after updating the file)."""
    global _board_entries, _board_journals
    _board_entries = None
    _board_journals = None


def _board_skip(status: str) -> bool:
    """Return True if this paper should be skipped by the pipeline."""
    s = status.strip()
    for prefix in ("已投", "已接收", "接收", "已发表", "拒稿", "骨架", "归档",
                    "待分诊"):
        if s.startswith(prefix):
            return True
    return False


# Cache board journals at module load (derived from board entries)
_board_journals: Optional[dict[str, str]] = None


def _get_board_journals() -> dict[str, str]:
    global _board_journals
    if _board_journals is None:
        _board_journals = _load_board_journals()
    return _board_journals


def detect_target_journal(paper_dir: str) -> str:
    """Auto-detect target journal for a paper.

    Priority:
      1. PROGRAM_BOARD.md exact dir-name match (authoritative)
      2. PROGRAM_BOARD.md keyword match (legacy compat)
      3. Paper's own PIPELINE.md
      4. Journal abbreviation in directory name
      5. Empty string → Stage F will select via codex
    """
    paper_path = Path(paper_dir)
    name_lower = paper_path.name.lower()

    # 1. PROGRAM_BOARD exact match on dir name
    entries = _get_board_entries()
    entry = entries.get(paper_path.name)
    if entry and entry["journal"] and entry["journal"] != "—":
        journal = entry["journal"]
        return _BOARD_JOURNAL_EXPAND.get(journal.lower(), journal)

    # 2. PROGRAM_BOARD keyword match (legacy)
    board = _get_board_journals()
    for key, journal in board.items():
        if key in name_lower:
            return journal

    # 3. Check paper's own PIPELINE.md
    pipeline_md = paper_path / "PIPELINE.md"
    if pipeline_md.exists():
        try:
            text = pipeline_md.read_text(encoding="utf-8")[:3000]
            m = re.search(
                r"(?:target|venue|journal)\s*[:=]\s*(.+?)(?:\n|\(|$)",
                text, re.IGNORECASE,
            )
            if m:
                journal = m.group(1).strip().rstrip(".,;")
                journal = re.sub(r"\*+", "", journal).strip()
                if len(journal) > 5:
                    return journal
        except Exception:
            pass

    # 4. Check directory name for known abbreviations
    for abbrev, full_name in JOURNAL_ABBREV.items():
        if (name_lower.endswith(f"_{abbrev}")
            or f"_{abbrev}_" in name_lower
            or name_lower == abbrev):
            return full_name

    return ""
MAX_STAGE_A_ROUNDS = 5
MAX_STAGE_B_ROUNDS = 4
MAX_STAGE_C_ROUNDS = 4

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------

LOG_DIR.mkdir(parents=True, exist_ok=True)
STATE_DIR.mkdir(parents=True, exist_ok=True)

_log_file = LOG_DIR / f"pipeline_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"

# Windows console needs utf-8 stream handler to avoid cp1252 crashes
class _Utf8StreamHandler(logging.StreamHandler):
    def emit(self, record):
        try:
            msg = self.format(record)
            # Force utf-8 on Windows console
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
logger = logging.getLogger("oracle-pipeline")

# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class StageLog:
    """One iteration of a stage."""
    stage: str
    round_num: int
    timestamp: str = ""
    action: str = ""
    score: int = 0
    verdict: str = ""
    detail: str = ""
    committed: bool = False
    commit_hash: str = ""

    def to_dict(self) -> dict:
        return vars(self)


@dataclass
class PaperState:
    """Full persistent state for a paper's pipeline run."""
    paper_dir: str
    paper_name: str
    main_paper_dir: str = ""       # 主论文目录（用于 Stage D 回流）
    target_journal: str = ""

    # Current position
    current_stage: str = "F"       # F / A / B / C / D / DONE
    current_round: int = 0         # within-stage round counter

    # Stage F tracking (journal fit)
    stage_f_fit_score: int = 0
    stage_f_original_journal: str = ""
    stage_f_suggested_journal: str = ""
    stage_f_passed: bool = False

    # Stage A tracking
    stage_a_rounds: int = 0
    stage_a_scores: list[int] = field(default_factory=list)
    stage_a_passed: bool = False
    stage_a0_done: bool = False    # Literature audit one-shot

    # Stage B tracking
    stage_b_rounds: int = 0
    stage_b_verdicts: list[str] = field(default_factory=list)
    stage_b_passed: bool = False

    # Stage C tracking
    stage_c_rounds: int = 0
    stage_c_verdicts: list[str] = field(default_factory=list)
    stage_c_passed: bool = False

    # Stage D tracking
    stage_d_backflow_items: list[str] = field(default_factory=list)
    stage_d_passed: bool = False

    # Full history
    history: list[dict] = field(default_factory=list)

    # Meta
    pdf_path: str = ""
    started_at: str = ""
    completed_at: str = ""
    error: str = ""

    def log_event(self, stage: str, action: str, **kwargs) -> StageLog:
        entry = StageLog(
            stage=stage,
            round_num=kwargs.get("round_num", self.current_round),
            timestamp=datetime.now().isoformat(),
            action=action,
            score=kwargs.get("score", 0),
            verdict=kwargs.get("verdict", ""),
            detail=kwargs.get("detail", "")[:20000],
            committed=kwargs.get("committed", False),
            commit_hash=kwargs.get("commit_hash", ""),
        )
        self.history.append(entry.to_dict())
        return entry

    def to_dict(self) -> dict:
        return {
            "paper_dir": self.paper_dir,
            "paper_name": self.paper_name,
            "main_paper_dir": self.main_paper_dir,
            "target_journal": self.target_journal,
            "current_stage": self.current_stage,
            "current_round": self.current_round,
            "stage_f_fit_score": self.stage_f_fit_score,
            "stage_f_original_journal": self.stage_f_original_journal,
            "stage_f_suggested_journal": self.stage_f_suggested_journal,
            "stage_f_passed": self.stage_f_passed,
            "stage_a_rounds": self.stage_a_rounds,
            "stage_a_scores": self.stage_a_scores,
            "stage_a_passed": self.stage_a_passed,
            "stage_a0_done": self.stage_a0_done,
            "stage_b_rounds": self.stage_b_rounds,
            "stage_b_verdicts": self.stage_b_verdicts,
            "stage_b_passed": self.stage_b_passed,
            "stage_c_rounds": self.stage_c_rounds,
            "stage_c_verdicts": self.stage_c_verdicts,
            "stage_c_passed": self.stage_c_passed,
            "stage_d_backflow_items": self.stage_d_backflow_items,
            "stage_d_passed": self.stage_d_passed,
            "history": self.history[-50:],  # keep last 50 entries
            "pdf_path": self.pdf_path,
            "started_at": self.started_at,
            "completed_at": self.completed_at,
            "error": self.error,
            "total_rounds": (self.stage_a_rounds + self.stage_b_rounds
                             + self.stage_c_rounds),
        }


# ---------------------------------------------------------------------------
# State persistence
# ---------------------------------------------------------------------------

def _state_file(paper_name: str) -> Path:
    safe = re.sub(r"[^a-zA-Z0-9_-]", "_", paper_name)
    return STATE_DIR / f"{safe}.json"


def save_state(state: PaperState) -> None:
    with _state_lock:
        path = _state_file(state.paper_name)
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(state.to_dict(), f, indent=2, ensure_ascii=False)


def load_state(paper_name: str) -> Optional[PaperState]:
    path = _state_file(paper_name)
    if not path.exists():
        return None
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        s = PaperState(paper_dir=data["paper_dir"], paper_name=data["paper_name"])
        for key in ("main_paper_dir", "target_journal", "current_stage",
                     "current_round",
                     "stage_f_fit_score", "stage_f_original_journal",
                     "stage_f_suggested_journal", "stage_f_passed",
                     "stage_a_rounds", "stage_a_passed", "stage_a0_done",
                     "stage_b_rounds", "stage_b_passed", "stage_c_rounds",
                     "stage_c_passed", "stage_d_passed", "pdf_path",
                     "started_at", "completed_at", "error"):
            if key in data:
                setattr(s, key, data[key])
        s.stage_a_scores = data.get("stage_a_scores", [])
        s.stage_b_verdicts = data.get("stage_b_verdicts", [])
        s.stage_c_verdicts = data.get("stage_c_verdicts", [])
        s.stage_d_backflow_items = data.get("stage_d_backflow_items", [])
        s.history = data.get("history", [])
        return s
    except Exception:
        return None


def rebuild_rounds_from_git(state: PaperState) -> None:
    """Recover max prior round numbers from commit history.

    Pipeline state files occasionally get lost (crash, branch switch, manual
    reset) but git log always has the ground truth. Scan for commits matching
    'stage-A R\\d+' etc and advance state counters to the observed maximum so
    subsequent rounds don't silently repeat work already committed.
    """
    paper_path = Path(state.paper_dir)
    if not paper_path.exists():
        return
    try:
        rel = paper_path.relative_to(REPO_ROOT)
    except ValueError:
        rel = paper_path

    try:
        with _git_lock:
            result = subprocess.run(
                ["git", "log", "--all", "--format=%s", "--", str(rel)],
                cwd=str(REPO_ROOT), capture_output=True, text=True,
                timeout=30,
            )
    except Exception as e:
        logger.debug(f"[{state.paper_name}] git log failed for state rebuild: {e}")
        return

    if result.returncode != 0:
        return

    max_a = state.stage_a_rounds
    max_b = state.stage_b_rounds
    max_c = state.stage_c_rounds
    for line in result.stdout.splitlines():
        m = re.search(r"stage-A\s+R(\d+)", line, re.IGNORECASE)
        if m:
            max_a = max(max_a, int(m.group(1)))
        m = re.search(r"stage-B\s+R(\d+)", line, re.IGNORECASE)
        if m:
            max_b = max(max_b, int(m.group(1)))
        m = re.search(r"stage-C\s+R(\d+)", line, re.IGNORECASE)
        if m:
            max_c = max(max_c, int(m.group(1)))
        # Oracle review rounds (legacy format: "Oracle R14", "gate_R9")
        m = re.search(r"(?:oracle|gate)[\s_]+R(\d+)", line, re.IGNORECASE)
        if m:
            max_b = max(max_b, int(m.group(1)))
    if max_a != state.stage_a_rounds:
        logger.info(f"[{state.paper_name}] git-rebuild: stage_a_rounds "
                    f"{state.stage_a_rounds} → {max_a}")
        state.stage_a_rounds = max_a
    if max_b != state.stage_b_rounds:
        logger.info(f"[{state.paper_name}] git-rebuild: stage_b_rounds "
                    f"{state.stage_b_rounds} → {max_b}")
        state.stage_b_rounds = max_b
    if max_c != state.stage_c_rounds:
        logger.info(f"[{state.paper_name}] git-rebuild: stage_c_rounds "
                    f"{state.stage_c_rounds} → {max_c}")
        state.stage_c_rounds = max_c


# ---------------------------------------------------------------------------
# Shell / HTTP / Git helpers
# ---------------------------------------------------------------------------

def run_cmd(cmd: list[str], *, cwd: Optional[Path] = None,
            timeout: int = 300) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd, cwd=str(cwd or REPO_ROOT),
        capture_output=True, text=True, timeout=timeout,
        stdin=subprocess.DEVNULL,
        encoding="utf-8", errors="replace",
    )


def http_post(url: str, data: dict, timeout: int = 30) -> dict:
    import urllib.request
    req = urllib.request.Request(
        url, data=json.dumps(data).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    resp = urllib.request.urlopen(req, timeout=timeout)
    return json.loads(resp.read().decode("utf-8"))


def http_get(url: str, timeout: int = 10) -> dict:
    import urllib.request
    resp = urllib.request.urlopen(url, timeout=timeout)
    return json.loads(resp.read().decode("utf-8"))


def oracle_server_alive() -> bool:
    try:
        return "queue_length" in http_get(f"{ORACLE_SERVER}/status", timeout=5)
    except Exception:
        return False


# Files that are pipeline artifacts, NOT paper content. Never commit these.
_ARTIFACT_PATTERNS = (
    "literature_audit.md", "cross_paper_dedup.md", "temp_patch.txt",
    ".pipeline.stop",
)


def _add_paper_only(paper_path: Path) -> None:
    """git add only .tex .bib .sty files under paper_path. Skip artifacts."""
    run_cmd(["git", "add", "--", str(paper_path / "*.tex"),
             str(paper_path / "**/*.tex"),
             str(paper_path / "*.bib"),
             str(paper_path / "**/*.bib"),
             str(paper_path / "*.sty")])
    # Unstage any artifacts that might have slipped in
    for pattern in _ARTIFACT_PATTERNS:
        run_cmd(["git", "reset", "HEAD", "--",
                 str(paper_path / pattern),
                 str(paper_path / "**" / pattern)])


def _diff_summary(paper_path: Path) -> str:
    """One-line summary of what changed: files modified, lines added/removed."""
    result = run_cmd(["git", "diff", "--cached", "--stat", str(paper_path)])
    lines = result.stdout.strip().splitlines()
    if not lines:
        return ""
    # Last line is like " 5 files changed, 120 insertions(+), 30 deletions(-)"
    summary = lines[-1].strip() if lines else ""
    # Also list changed .tex filenames (short)
    changed = [l.split("|")[0].strip().split("/")[-1]
               for l in lines[:-1] if "|" in l and ".tex" in l]
    if changed:
        return f"{', '.join(changed[:4])}; {summary}"
    return summary


def git_stage(paper_path: Path, *, tag: str = "") -> bool:
    """Stage .tex/.bib changes under paper_path (no commit, no artifacts)."""
    with _git_lock:
        _add_paper_only(paper_path)
        staged = run_cmd(["git", "diff", "--cached", "--name-only",
                          str(paper_path)])
        return bool(staged.stdout.strip())


def git_commit(paper_path: Path, msg: str, *, tag: str = "") -> str:
    """Commit .tex/.bib changes under paper_path. No artifacts. Thread-safe.

    Commit message includes a diff summary showing what actually changed.
    """
    with _git_lock:
        _add_paper_only(paper_path)
        staged = run_cmd(["git", "diff", "--cached", "--name-only",
                          str(paper_path)])
        if not staged.stdout.strip():
            logger.info(f"{tag} No paper changes to commit")
            return ""
        paper_short = paper_path.name.replace("2026_", "")[:40]
        diff_info = _diff_summary(paper_path)
        body = f"Changes: {diff_info}" if diff_info else ""
        full_msg = (
            f"[{paper_short}] {msg}\n\n"
            f"{body}\n\n"
            f"Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>"
        )
        result = run_cmd(["git", "commit", "-m", full_msg])
        if result.returncode == 0:
            h = run_cmd(["git", "rev-parse", "--short", "HEAD"]).stdout.strip()
            logger.info(f"{tag} Committed: {h} — {msg[:60]}")
            return h
        logger.warning(f"{tag} Commit failed: {result.stderr[:200]}")
        return ""


def git_commit_multi(paths: list[Path], msg: str, *, tag: str = "") -> str:
    """Commit changes across multiple paths (for Stage D backflow)."""
    with _git_lock:
        has_changes = False
        for p in paths:
            s = run_cmd(["git", "status", "--porcelain", str(p)])
            if s.stdout.strip():
                has_changes = True
                run_cmd(["git", "add", str(p)])
        if not has_changes:
            return ""
        full_msg = (
            f"{msg}\n\n"
            f"Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>"
        )
        result = run_cmd(["git", "commit", "-m", full_msg])
        if result.returncode == 0:
            h = run_cmd(["git", "rev-parse", "--short", "HEAD"]).stdout.strip()
            logger.info(f"{tag} Committed: {h} — {msg[:60]}")
            return h
        return ""


# ---------------------------------------------------------------------------
# Oracle (ChatGPT Pro) interface
# ---------------------------------------------------------------------------

def oracle_submit(task_id: str, prompt: str,
                  pdf_path: Optional[Path] = None,
                  model: str = "chatgpt-5.4-pro-extended") -> bool:
    payload: dict = {"task_id": task_id, "prompt": prompt, "model": model}
    if pdf_path and pdf_path.exists():
        with open(pdf_path, "rb") as f:
            payload["pdf_base64"] = base64.b64encode(f.read()).decode("ascii")
        payload["pdf_name"] = pdf_path.name
    try:
        http_post(f"{ORACLE_SERVER}/submit", payload, timeout=30)
        return True
    except Exception as e:
        logger.error(f"Oracle submit failed: {e}")
        return False


def is_oracle_response_valid(response: str) -> bool:
    """Reject extraction-failure garbage (<2KB, thinking preamble, prompt echo).

    Historical Oracle userscript extraction-failure rate is ≥40%.
    Valid referee reviews are always ≥2KB and contain structural anchors like
    "verdict", "blocker", "revision", or a numbered issue table.
    """
    if not response:
        return False
    cleaned = response.strip()
    if len(cleaned) < 2000:
        return False
    lower = cleaned.lower()
    # Structural anchors expected in a substantive review
    anchors = ("verdict", "revision", "blocker", "medium", "accept",
               "reject", "issue", "referee")
    if not any(a in lower for a in anchors):
        return False
    # Reject single-phrase thinking preambles like "I", "s to change..."
    if len(cleaned.split()) < 50:
        return False
    return True


def oracle_poll(task_id: str, timeout: int = 7200,
                poll_interval: int = 30) -> str:
    """EVENT WAIT — blocks until oracle responds.

    Registers with oracle_wait_enter/exit so the rolling dispatcher
    knows how many workers are I/O-blocked (not consuming CPU).
    """
    oracle_wait_enter()
    logger.info(f"EVENT WAIT: oracle {task_id} (max {timeout}s, "
                f"oracle_waiters={get_oracle_wait_count()})")
    start = time.time()
    try:
        while time.time() - start < timeout:
            try:
                data = http_get(f"{ORACLE_SERVER}/result/{task_id}", timeout=10)
                if data.get("status") == "completed":
                    r = data.get("response", "")
                    logger.info(f"Oracle response: {task_id} ({len(r)} chars, "
                                f"{int(time.time()-start)}s)")
                    return r
            except Exception:
                pass
            elapsed = int(time.time() - start)
            if elapsed > 0 and elapsed % 60 == 0:
                logger.info(f"  Waiting for {task_id}... ({elapsed}s, "
                            f"oracle_waiters={get_oracle_wait_count()})")
            time.sleep(poll_interval)
        return ""
    finally:
        oracle_wait_exit()


# ---------------------------------------------------------------------------
# Codex exec
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Memory-pressure guard (macOS) — borrowed from codex_formalize.py
# ---------------------------------------------------------------------------

def _macos_pressure_level() -> int:
    """Return macOS memory-pressure level: 1=NORMAL, 2=WARN, 4=URGENT, 8=CRITICAL."""
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


def wait_for_memory(tag: str = "", threshold: int = 4,
                    poll: int = 30, max_wait: int = 600) -> None:
    """Block until macOS memory pressure drops below threshold.

    Only active on macOS. Prevents OOM when parallel codex + claude
    processes saturate unified memory on M-series Macs.
    """
    if sys.platform != "darwin":
        return
    waited = 0
    while waited < max_wait:
        level = _macos_pressure_level()
        if level < threshold:
            return
        level_name = {1: "NORMAL", 2: "WARN", 4: "URGENT", 8: "CRITICAL"}.get(
            level, f"UNKNOWN({level})")
        if waited == 0:
            logger.warning(f"{tag} Memory pressure {level_name} >= threshold, "
                           f"waiting before next codex/claude call...")
        time.sleep(poll)
        waited += poll
    logger.warning(f"{tag} Memory pressure wait timed out after {max_wait}s, "
                   f"proceeding anyway")


def _kill_process_tree(pid: int) -> None:
    """Forcefully kill process and all descendants.

    Codex spawns node + codex binary + children; subprocess.run's kill misses them,
    leaving orphans that consume resources and can corrupt state. Borrowed from
    outreach_pipeline.py Bug 3 fix (commit 1cab05f6).
    """
    if IS_WINDOWS:
        try:
            subprocess.run(["taskkill", "/F", "/T", "/PID", str(pid)],
                           capture_output=True, timeout=10)
        except Exception:
            pass
        return
    try:
        os.killpg(os.getpgid(pid), 15)  # SIGTERM
        time.sleep(2)
        os.killpg(os.getpgid(pid), 9)   # SIGKILL
    except (ProcessLookupError, OSError):
        pass
    # Also kill orphaned children via pgrep
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


def codex_exec(prompt: str, *, work_dir: Optional[Path] = None,
               timeout_seconds: int = 1800, model: Optional[str] = None,
               dry_run: bool = False) -> str:
    if dry_run:
        logger.info(f"[DRY RUN] codex exec:\n{prompt[:200]}...")
        return "(dry run)"

    wait_for_memory(tag="[codex]")

    codex_bin = CODEX_PATH if Path(CODEX_PATH).exists() else shutil.which("codex")
    if not codex_bin:
        logger.error("Codex CLI not found")
        return ""

    import tempfile
    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False,
                                     encoding="utf-8") as f:
        f.write(prompt)
        prompt_file = f.name

    out_fd, out_file = tempfile.mkstemp(suffix=".txt", prefix="codex_out_")
    os.close(out_fd)

    # Use both --json (JSONL stream) and -o (last message).
    # --json gives us all agent_message events as fallback if -o is empty.
    cmd = [
        codex_bin, "exec",
        "--dangerously-bypass-approvals-and-sandbox",
        "--json",
        "-C", str(work_dir or REPO_ROOT), "-o", out_file,
    ]
    if model:
        cmd.extend(["-m", model])
    cmd.append("-")

    # Windows: .cmd wrappers need shell=True
    use_shell = IS_WINDOWS and str(codex_bin).endswith(".cmd")

    # Use Popen + start_new_session so we can kill the entire process tree on
    # timeout (codex spawns node + codex binary + children; subprocess.run's
    # kill misses them). Borrowed from outreach_pipeline.py Bug 3 fix.
    start = time.monotonic()
    result = None
    popen_kwargs: dict = dict(
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=str(work_dir or REPO_ROOT),
        shell=use_shell,
        encoding="utf-8", errors="replace",
    )
    if not IS_WINDOWS:
        popen_kwargs["start_new_session"] = True

    class _Result:
        def __init__(self, stdout="", stderr="", returncode=0):
            self.stdout = stdout
            self.stderr = stderr
            self.returncode = returncode

    try:
        with open(prompt_file, "r", encoding="utf-8") as pf:
            prompt_text = pf.read()
        proc = subprocess.Popen(cmd, **popen_kwargs)
        try:
            stdout, stderr = proc.communicate(input=prompt_text,
                                               timeout=timeout_seconds + 30)
            result = _Result(stdout, stderr, proc.returncode)
        except subprocess.TimeoutExpired:
            logger.warning(f"Codex timed out after {timeout_seconds}s, "
                           f"killing process tree (pid={proc.pid})")
            _kill_process_tree(proc.pid)
            try:
                stdout, stderr = proc.communicate(timeout=10)
            except subprocess.TimeoutExpired:
                stdout, stderr = "", ""
            result = _Result(stdout, stderr, -9)
    except OSError as exc:
        logger.error(f"Codex failed to start: {exc}")
        os.unlink(prompt_file)
        try:
            os.unlink(out_file)
        except OSError:
            pass
        return "(start-failed)"
    finally:
        elapsed = time.monotonic() - start
        rc = result.returncode if result else "?"
        logger.info(f"Codex exec: {elapsed:.1f}s (rc={rc})")
        try:
            os.unlink(prompt_file)
        except OSError:
            pass

    output = ""
    try:
        # Prefer -o output (the cleanly-extracted last agent message)
        if os.path.exists(out_file) and os.path.getsize(out_file) > 0:
            with open(out_file, "r", encoding="utf-8") as f:
                output = f.read()
        else:
            # Fallback: parse JSONL stream from stdout, concat all agent_message text
            stdout = (result.stdout or "") if result else ""
            messages = []
            for line in stdout.splitlines():
                line = line.strip()
                if not line.startswith("{"):
                    continue
                try:
                    evt = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if evt.get("type") == "item.completed":
                    item = evt.get("item", {})
                    if item.get("type") == "agent_message" and item.get("text"):
                        messages.append(item["text"])
            output = "\n\n".join(messages)
            if not output:
                # Last resort: raw stdout (may contain reasoning noise)
                output = stdout
                if not output and result and result.stderr:
                    logger.warning(f"Codex stderr: {result.stderr[:300]}")
    finally:
        try:
            os.unlink(out_file)
        except OSError:
            pass
    return output


# ---------------------------------------------------------------------------
# Claude CLI exec (independent verification — NOT codex)
# ---------------------------------------------------------------------------

def _find_claude() -> str:
    """Find the Claude Code CLI binary."""
    found = shutil.which("claude")
    if found:
        return found
    if sys.platform == "darwin":
        for p in ("/opt/homebrew/bin/claude", "/usr/local/bin/claude"):
            if Path(p).exists():
                return p
    elif sys.platform == "win32":
        npm_claude = Path.home() / "AppData" / "Roaming" / "npm" / "claude.cmd"
        if npm_claude.exists():
            return str(npm_claude)
    return "claude"

CLAUDE_PATH = _find_claude()


def claude_exec(prompt: str, *, work_dir: Optional[Path] = None,
                timeout_seconds: int = 600,
                dry_run: bool = False) -> str:
    """Call Claude Code CLI for independent review/verification.

    Uses `claude -p --dangerously-skip-permissions` for non-interactive
    execution. Claude reads the repo, has full context, and provides
    independent judgment separate from Codex.

    Used for: Stage F2, A4, C1, D2 (all verification/review steps).
    """
    if dry_run:
        logger.info(f"[DRY RUN] claude_exec:\n{prompt[:200]}...")
        return "(dry run)"

    wait_for_memory(tag="[claude]")

    claude_bin = CLAUDE_PATH
    if not Path(claude_bin).exists() and not shutil.which(claude_bin):
        logger.warning("Claude CLI not found — falling back to codex_exec")
        return codex_exec(prompt, work_dir=work_dir, dry_run=dry_run)

    cmd = [claude_bin, "-p", "--dangerously-skip-permissions"]

    use_shell = IS_WINDOWS and str(claude_bin).endswith(".cmd")

    start = time.monotonic()
    result = None
    try:
        result = subprocess.run(
            cmd, input=prompt, capture_output=True, text=True,
            timeout=timeout_seconds,
            cwd=str(work_dir or REPO_ROOT),
            shell=use_shell,
            encoding="utf-8", errors="replace",
        )
    except subprocess.TimeoutExpired:
        logger.warning(f"Claude CLI timed out after {timeout_seconds}s")
        return "(timeout)"
    finally:
        elapsed = time.monotonic() - start
        rc = result.returncode if result else "?"
        logger.info(f"Claude CLI: {elapsed:.1f}s (rc={rc})")

    output = result.stdout or ""
    if result and result.returncode != 0:
        logger.warning(f"Claude CLI error: {result.stderr[:300]}")
        if not output:
            logger.warning("Falling back to codex_exec")
            return codex_exec(prompt, work_dir=work_dir, dry_run=dry_run)

    return output


# ---------------------------------------------------------------------------
# Compile PDF
# ---------------------------------------------------------------------------

def read_compile_errors(paper_path: Path, max_chars: int = 4000) -> str:
    """Tail of main.log focused on LaTeX error lines.

    Returns up to ``max_chars`` of text centred on lines starting with '!'
    (LaTeX fatal markers) plus the preceding 2 lines for context.
    Empty string means either no log file or no parseable error.
    """
    log = paper_path / "main.log"
    if not log.exists():
        return ""
    try:
        text = log.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return ""
    lines = text.splitlines()
    err_chunks: list[str] = []
    for i, line in enumerate(lines):
        if line.startswith("!") or line.startswith("l."):
            start = max(0, i - 2)
            end = min(len(lines), i + 6)
            err_chunks.append("\n".join(lines[start:end]))
    if not err_chunks:
        return "\n".join(lines[-80:])[:max_chars]
    return "\n---\n".join(err_chunks)[:max_chars]


def try_compile(paper_path: Path, *, dry_run: bool = False) -> bool:
    """Best-effort compile. Returns True iff a PDF was produced."""
    if dry_run:
        return True
    pdf = compile_pdf(paper_path, dry_run=False)
    return bool(pdf and pdf.exists())


def build_compile_fix_prompt(paper_dir: str, error_tail: str) -> str:
    return textwrap.dedent(f"""\
        LaTeX compilation failed for the paper in {paper_dir}.
        The last round of edits broke the build.

        Error tail from main.log (most important lines):
        ```
        {error_tail}
        ```

        Fix ONLY the compile errors. Do not change mathematical content.
        After fixing, re-compile:
          cd {paper_dir} && xelatex -interaction=nonstopmode main.tex
    """)


def compile_gate(paper_path: Path, *, model: Optional[str] = None,
                 dry_run: bool = False, tag: str = "") -> bool:
    """Compile; on failure invoke Codex once to repair; compile again.

    Returns True iff the final compile succeeds. Callers may still commit
    on failure if they prefer continuing over blocking, but the gate gives
    them the signal to decide.
    """
    if try_compile(paper_path, dry_run=dry_run):
        return True
    err = read_compile_errors(paper_path)
    logger.warning(f"{tag} compile failed; invoking Codex to repair "
                   f"({len(err)} chars of errors)")
    codex_exec(build_compile_fix_prompt(str(paper_path), err),
               work_dir=paper_path, timeout_seconds=600,
               model=model, dry_run=dry_run)
    return try_compile(paper_path, dry_run=dry_run)


def compile_pdf(paper_path: Path, *, dry_run: bool = False) -> Optional[Path]:
    if dry_run:
        return paper_path / "main.pdf"
    main_tex = paper_path / "main.tex"
    if not main_tex.exists():
        return None

    # Prefer tectonic (self-contained, auto-downloads packages, no bibtex loop)
    tectonic = shutil.which("tectonic")
    if tectonic:
        run_cmd([tectonic, "--keep-logs", "-Z", "continue-on-errors",
                 "main.tex"], cwd=paper_path, timeout=300)
        pdf = paper_path / "main.pdf"
        if pdf.exists():
            return pdf

    # Fallback: traditional xelatex/pdflatex pipeline
    content = main_tex.read_text(encoding="utf-8", errors="replace")
    compiler_name = ("xelatex" if any(k in content for k in ("xeCJK", "ctex", "fontspec"))
                     else "pdflatex")
    compiler = shutil.which(compiler_name)
    if not compiler:
        logger.warning(f"No LaTeX compiler found ({compiler_name} missing, "
                       f"tectonic missing) — skip PDF")
        return None

    for _ in range(2):
        run_cmd([compiler, "-interaction=nonstopmode", "-halt-on-error",
                 "main.tex"], cwd=paper_path, timeout=120)
    has_bib = ((paper_path / "references.bib").exists()
               or (paper_path / "references_local.bib").exists())
    if has_bib and shutil.which("bibtex"):
        run_cmd(["bibtex", "main"], cwd=paper_path, timeout=60)
        for _ in range(2):
            run_cmd([compiler, "-interaction=nonstopmode", "-halt-on-error",
                     "main.tex"], cwd=paper_path, timeout=120)
    pdf = paper_path / "main.pdf"
    return pdf if pdf.exists() else None


# ---------------------------------------------------------------------------
# Prompt builders
# ---------------------------------------------------------------------------

def summarize_content_changes(paper_path: Path,
                               pre_theorems: list[tuple[str, str]]
                               ) -> str:
    """Generate a human-readable summary of what mathematical content changed.

    Returns a string like:
      "added Theorem: Doob transform (thm:poisson-doob); corrected Lemma 3.2 proof;
       expanded sec_introduction (+120 lines); 3 new references"
    """
    post_theorems = extract_theorem_statements(paper_path)
    pre_labels = {label for label, _ in pre_theorems}
    post_labels = {label for label, _ in post_theorems}

    new_labels = sorted(post_labels - pre_labels)
    removed_labels = sorted(pre_labels - post_labels)

    parts = []

    # New theorems
    for label in new_labels[:5]:
        # Clean up label for readability
        short = label.replace("thm:", "").replace("prop:", "").replace(
            "cor:", "").replace("lem:", "").replace("def:", "")
        short = short.replace("_", " ").replace("-", " ")[:60]
        parts.append(f"added {short}")

    # Removed/renamed theorems
    if removed_labels:
        parts.append(f"removed/renamed {len(removed_labels)} theorem(s)")

    # Count new references
    try:
        bib_files = list(paper_path.glob("*.bib")) + list(paper_path.glob("**/*.bib"))
        new_refs = 0
        for bib in bib_files:
            result = run_cmd(["git", "diff", "--cached", "--", str(bib)])
            if result.stdout:
                new_refs += result.stdout.count("+@")
        if new_refs > 0:
            parts.append(f"{new_refs} new references")
    except Exception:
        pass

    if not parts:
        # Fallback: just count line changes
        pre_len = sum(len(body) for _, body in pre_theorems)
        post_len = sum(len(body) for _, body in post_theorems)
        delta = post_len - pre_len
        if delta > 0:
            parts.append(f"expanded proofs (+{delta} chars)")
        elif delta < 0:
            parts.append(f"tightened proofs ({delta} chars)")
        else:
            parts.append("style/formatting improvements")

    return "; ".join(parts)


def update_program_board(paper_name: str, stage: str, detail: str) -> None:
    """Update PROGRAM_BOARD.md status column for a paper in-place.

    Finds the row whose backtick-wrapped dir name matches paper_name
    and overwrites the status cell.  Thread-safe via _git_lock.
    """
    if not PROGRAM_BOARD.exists():
        return
    new_status = f"{stage} ({detail})" if detail else stage
    try:
        with _git_lock:
            text = PROGRAM_BOARD.read_text(encoding="utf-8")
            lines = text.split("\n")
            updated = False
            needle = f"`{paper_name}`"
            for i, line in enumerate(lines):
                if needle not in line:
                    continue
                parts = line.split("|")
                # Expected: ['', ' `dir` ', ' journal ', ' status ', ' reroute ', '']
                if len(parts) >= 5:
                    parts[3] = f" {new_status} "
                    lines[i] = "|".join(parts)
                    updated = True
                break
            if updated:
                PROGRAM_BOARD.write_text("\n".join(lines), encoding="utf-8")
                run_cmd(["git", "add", str(PROGRAM_BOARD)])
                _invalidate_board_cache()
                logger.info(f"PROGRAM_BOARD updated: {paper_name} ��� {new_status}")
            else:
                logger.warning(
                    f"Paper {paper_name} not found in PROGRAM_BOARD.md — "
                    f"add a row to track it")
    except Exception as e:
        logger.warning(f"Failed to update PROGRAM_BOARD: {e}")


def verify_substantive_change(paper_path: Path,
                               pre_theorems: list[tuple[str, str]],
                               min_new_theorems: int = 1,
                               min_new_content_chars: int = 500,
                               ) -> tuple[bool, str]:
    """Anti-fake gate: verify A-DEEP actually added substantive new content.

    Compares theorem count and total content length before vs after codex edit.
    Returns (passed, reason).

    Catches the pattern where codex claims to add "deep research" but actually
    only rephrases existing text, reorganizes sections, or adds filler prose.
    Borrowed concept from codex_formalize.py anti-cheat gate (e7bfb0fa).
    """
    post_theorems = extract_theorem_statements(paper_path)

    pre_labels = {label for label, _ in pre_theorems}
    post_labels = {label for label, _ in post_theorems}
    new_labels = post_labels - pre_labels

    pre_content_len = sum(len(body) for _, body in pre_theorems)
    post_content_len = sum(len(body) for _, body in post_theorems)
    content_delta = post_content_len - pre_content_len

    # Also check raw .tex line count delta
    total_lines = 0
    for tex in paper_path.glob("**/*.tex"):
        try:
            total_lines += len(tex.read_text(encoding="utf-8",
                                              errors="replace").splitlines())
        except Exception:
            pass

    if len(new_labels) >= min_new_theorems and content_delta >= min_new_content_chars:
        return True, (f"Added {len(new_labels)} new theorem(s): "
                      f"{', '.join(sorted(new_labels)[:5])}; "
                      f"+{content_delta} chars content")

    if len(new_labels) == 0 and content_delta < min_new_content_chars:
        return False, (f"FAKE EXTENSION: no new theorems added, "
                       f"content delta only +{content_delta} chars "
                       f"(threshold: {min_new_content_chars}). "
                       f"Codex likely rephrased without adding substance.")

    if len(new_labels) == 0 and content_delta >= min_new_content_chars:
        return True, (f"No new labels but +{content_delta} chars content "
                      f"(existing theorems expanded)")

    return True, (f"{len(new_labels)} new labels, +{content_delta} chars")


def extract_theorem_statements(paper_path: Path) -> list[tuple[str, str]]:
    """Extract (label, statement_text) for every theorem-like environment.

    Theorem environments include theorem, proposition, lemma, corollary,
    definition. Statement text is the raw body up to \\end{...}. Used by the
    cross-paper dedup scan; cheap programmatic filter before invoking Codex.
    """
    results: list[tuple[str, str]] = []
    pattern = re.compile(
        r"\\begin\{(theorem|proposition|lemma|corollary|definition)\}"
        r"(?:\[[^\]]*\])?\s*"
        r"(?:\\label\{([^}]+)\})?"
        r"(.*?)"
        r"\\end\{\1\}",
        re.DOTALL,
    )
    for tex in paper_path.glob("**/*.tex"):
        try:
            text = tex.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        for m in pattern.finditer(text):
            label = m.group(2) or f"unlabelled:{tex.name}:{m.start()}"
            body = re.sub(r"\s+", " ", m.group(3)).strip()
            if len(body) < 40:  # skip trivial/stub environments
                continue
            results.append((label, body))
    return results


def detect_cross_paper_overlaps(current_paper: Path,
                                other_papers: list[Path],
                                min_phrase_len: int = 60,
                                min_shared_phrases: int = 3,
                                ) -> list[dict]:
    """Programmatic pre-filter: find theorem statements that share long
    verbatim phrases with statements in sibling papers.

    Returns a list of overlap records. Each record points to a local theorem
    label plus the sibling paper and the shared phrases, so Codex can inspect
    and either rewrite or cite the prior occurrence.
    """
    local_stmts = extract_theorem_statements(current_paper)
    overlaps: list[dict] = []

    for sibling in other_papers:
        if sibling.resolve() == current_paper.resolve():
            continue
        sibling_stmts = extract_theorem_statements(sibling)
        sibling_phrases: dict[str, set[str]] = {}
        for slabel, sbody in sibling_stmts:
            # Sliding window of long verbatim phrases
            phrases = set()
            for i in range(0, len(sbody) - min_phrase_len, 20):
                phrases.add(sbody[i:i + min_phrase_len])
            sibling_phrases[slabel] = phrases

        for label, body in local_stmts:
            for slabel, sphrases in sibling_phrases.items():
                shared = [p for p in sphrases
                          if p in body and not _is_boilerplate(p)]
                if len(shared) >= min_shared_phrases:
                    overlaps.append({
                        "local_label": label,
                        "sibling": sibling.name,
                        "sibling_label": slabel,
                        "shared_phrases": shared[:5],
                    })
                    break  # one match per (local, sibling) is enough
    return overlaps


_BOILERPLATE_MARKERS = (
    "let $", "let \\", "suppose ", "assume ", "for every ", "for all ",
    "there exists ", "denote by ", "write $", "set $",
    "shift of finite type", "subshift of finite type",
    "$\\mathbb{r}$", "$\\mathbb{c}$", "$\\mathbb{z}$", "$\\mathbb{n}$",
    "\\begin{equation}", "\\end{equation}",
)


def _is_boilerplate(phrase: str) -> bool:
    """Heuristic: a shared phrase is boilerplate if it's common math prose
    rather than a substantive result statement. Prevents false positives on
    routine 'Let X be a ...' openers."""
    low = phrase.lower()
    return any(marker in low for marker in _BOILERPLATE_MARKERS)


def build_cross_paper_dedup_prompt(paper_dir: str,
                                    overlaps_json: str) -> str:
    """A_DEDUP prompt: resolve cross-paper duplication by rewriting or citing."""
    return textwrap.dedent(f"""\
        You are resolving cross-paper duplication in the paper at {paper_dir}.

        The programmatic scan found statements that share long verbatim phrases
        with theorems in sibling papers under papers/publication/. Each overlap
        record gives:
          - local_label: the label of the duplicate statement in THIS paper
          - sibling: directory name of the sibling paper
          - sibling_label: the label of the near-duplicate in the sibling
          - shared_phrases: specific verbatim strings shared between the two

        Overlaps (JSON):
        ```json
        {overlaps_json}
        ```

        ## Task for each overlap record

        Open the sibling paper and read the corresponding labelled statement.
        Then choose EXACTLY ONE of the following resolutions for the local copy:

        A) **Cite and defer**: if the statement is genuinely the same result,
           delete the local proof and rewrite the local statement as a one-line
           citation of the sibling: "See \\cite{{sibling-bib-key}}, Theorem X".
           This is the correct action when the two papers legitimately share
           a common building block. Add the sibling to references.bib.

        B) **Reframe with concrete increment**: if the local statement adds a
           genuine increment (wider class, sharper constant, new application),
           rewrite it so the increment is explicit in the statement itself
           ("Under [extra hypothesis], ... [new bound]"), and acknowledge the
           sibling result in a `\\begin{{remark}}` block immediately after.

        C) **Delete**: if the local statement is a stealth copy with no
           increment and the sibling is the authoritative version, delete the
           local theorem and every reference to its label. Update the proof
           flow if needed.

        ## Hard rules

        1. Option (A) is the default. Pick (B) only if you can write down the
           specific quantitative or qualitative increment in one sentence.
           Pick (C) only if the local statement adds nothing at all.
        2. Do NOT produce paraphrased rewordings of the sibling statement and
           call them new — that is exactly what this stage is preventing.
        3. After each resolution, compile the paper and verify no dangling
           \\ref to the deleted/renamed label remains.

        ## Output
        - Edit .tex files directly.
        - Write `cross_paper_dedup.md` in {paper_dir} summarising each resolution
          (local_label | sibling | chosen_action | one-line rationale).
        - Compile: cd {paper_dir} && xelatex -interaction=nonstopmode main.tex
    """)


def build_literature_audit_prompt(paper_dir: str, target_journal: str) -> str:
    """A0 prompt: produce theorem-by-theorem comparison with prior work.

    This is the single mechanism that forced the dynamical_zeta paper from
    over-claimed "Theorem A/B" to honest "Supporting propositions" with
    proper Sharp 1991 / Parry-Pollicott 1986 citations. It deserves its own
    stage instead of being a bullet inside A1.
    """
    return textwrap.dedent(f"""\
        You are a senior referee for "{target_journal}" doing a scholarly
        positioning audit of the paper in {paper_dir}.

        ## Task

        Produce a file `literature_audit.md` in {paper_dir} containing a single
        Markdown table with ONE ROW PER theorem, proposition, corollary,
        lemma, or definition that appears in the paper's main body (skip
        proofs-only appendices). No empty cells.

        Columns:
          label     — the \\label{{...}} of the statement
          kind      — theorem / proposition / lemma / corollary / definition
          class     — classical-input  /  novel-increment  /  conditional-corollary
          closest-prior — author(year, theorem/eqn number) of the nearest known
                          statement. Must be a real reference; if none exists,
                          write "none known" and explain in the next column why
                          you searched and found nothing.
          citation-key — the bib key if already in references.bib, else
                         propose a new key and add the entry to references.bib.
          increment — one sentence: what does OUR statement add over the
                      closest-prior? If class=classical-input, write
                      "no increment; used as building block".
          hypothesis-status — for each hypothesis used: verifiable /
                              generically-satisfied / open. If the manuscript
                              's disclosure of hypothesis status is inaccurate,
                              say so.

        ## Hard rules (this stage fails if any is violated)

        1. Every result labelled "Theorem" in the paper that you classify as
           `classical-input` must be demoted — edit the .tex file to rename
           `\\begin{{theorem}}` to `\\begin{{proposition}}` and prepend the
           title with "Supporting". Example:
             \\begin{{theorem}}[Finite-part formula]  →
             \\begin{{proposition}}[Supporting finite-part formula]

        2. Any `novel-increment` row whose increment sentence paraphrases an
           existing classical statement ("we generalise ...", "we extend ...")
           without naming a concrete quantitative or qualitative gain is
           treated as mis-classification. Re-classify as classical-input.

        3. Fill bib gaps. For every `closest-prior` entry not yet in
           references.bib, add a proper @article / @book entry with DOI or
           arXiv number. Do not insert TODO placeholders.

        4. After the table, add a subsection inside the paper's introduction
           (new .tex content) titled
             "Theorem-by-theorem comparison with prior work"
           which narrates the table in 3–6 paragraphs, crediting each classical
           input to the right author and isolating the novel increment in one
           sentence per item.

        5. Do NOT add new mathematical content in this stage. This stage is
           pure positioning and demotion. New content belongs to A-DEEP.

        ## Output
        - Edit .tex files (demote mis-classified theorems, add the new
          comparison subsection).
        - Write literature_audit.md as described.
        - Update references.bib with any newly cited prior work.
        - Compile: cd {paper_dir} && xelatex -interaction=nonstopmode main.tex
    """)


def build_quality_review_prompt(paper_dir: str, target_journal: str,
                                round_num: int,
                                prior_feedback: str = "") -> str:
    """Stage A prompt: review existing paper quality + fix issues.

    prior_feedback (optional): accumulated issues/scores from previous rounds,
    so codex doesn't repeat the same surface fixes and can address persistent
    problems. (Borrowed from community-outreach pipeline deep_mode pattern.)
    """
    feedback_section = ""
    if prior_feedback:
        feedback_section = textwrap.dedent(f"""

            ## Previous rounds' feedback (DO NOT repeat prior surface fixes)
            The paper has been through earlier quality-review rounds. Here is
            what reviewers flagged previously. Address issues that have NOT
            yet been resolved, and focus on DEEPER problems:
            {prior_feedback}
        """)

    return textwrap.dedent(f"""\
        You are an editor of "{target_journal}" reviewing a submission.
        This is quality-review round {round_num} for the paper in: {paper_dir}
        {feedback_section}
        ## Task: Review & Improve to Acceptance Standard

        Read the entire paper as a critical referee. Identify and FIX every issue
        that would prevent acceptance at "{target_journal}":

        - Proof gaps, missing steps, implicit assumptions → add the missing reasoning
        - Weak or unsupported claims → strengthen with evidence or remove
        - Unclear arguments → rewrite with explicit logical progression
        - Missing or incomplete references → add to references.bib and cite
        - Redundant/filler content → cut it; tighten the exposition
        - Theorems that lack novelty justification → add context showing what's new

        Requirements:
        - Do NOT add new research directions or new theorems — only improve what exists
        - Do NOT reproduce others' published proofs; cite them instead
        - Use rigorous academic language throughout. No colloquialisms.
        - No revision artifacts, no "we fixed X", no changelogs.

        ## Output
        Edit .tex files directly. After editing, compile:
          cd {paper_dir} && xelatex -interaction=nonstopmode main.tex
    """)


def build_deep_extension_prompt(paper_dir: str, target_journal: str,
                                 prior_issues: str, round_num: int) -> str:
    """Stage A deep-research escalation: paper too shallow → add new theorems.

    Invoked when FUNDAMENTAL issues are "insufficient depth/novelty for journal".
    Reads existing paper, conducts original research, produces NEW genuine theorems
    that elevate the paper to the target journal's bar.
    """
    return textwrap.dedent(f"""\
        You are a research mathematician whose paper has been flagged as insufficient
        in mathematical depth for "{target_journal}". Round {round_num} deep extension.
        Paper: {paper_dir}

        ## Context: Reviewer concerns
        {prior_issues}

        ## Task: Deep Original Research to Raise the Paper's Bar

        Read the ENTIRE existing paper first. Then conduct genuinely new research
        that addresses the depth concerns. You MUST produce results at the level
        expected by "{target_journal}".

        Requirements:
        - Find NEW striking, publishable conclusions that extend or deepen the
          paper's framework. These must be results that would actually impress a
          referee at "{target_journal}" — NOT reshuffling of existing content.
        - Push until you have at least ONE genuinely non-trivial new theorem with
          complete proof. Do not produce incremental filler.
        - Do NOT just rewrite prose or fix typos — this step is for ADDING
          mathematical content.
        - Do NOT reproduce reasoning already published by others. You MAY use
          their results as building blocks — cite them properly.
        - Every new theorem/proposition must have a complete rigorous proof.
        - Add missing references to references.bib.
        - Use rigorous academic language throughout.

        ## Anti-drift constraints (HARD RULES)
        These rules exist because prior rounds produced paraphrased filler
        labelled as new content. Violating any of them makes this round a
        no-op and wastes the budget:

        1. **No synonymous restatement.** A "new" theorem obtained by renaming
           an existing theorem, restricting it, or specialising constants is
           NOT new. If the statement differs from an existing labelled result
           only in wording or notation, it is forbidden.
        2. **No intermediate-process conclusions.** Do not announce lemmas of
           the form "we have proved that ..." that are stepping stones toward
           a later theorem. Only the final load-bearing statement counts.
        3. **Number and timestamp every new conclusion.** Each new theorem /
           proposition / corollary carries a bold inline tag
             [New-N | {datetime.now().strftime('%Y-%m-%d')}]
           where N continues the count across the paper (and rounds — check the
           highest existing [New-*] tag in the paper before starting). This tag
           lives INSIDE the theorem environment, right after \\begin{{theorem}}[...].
        4. **No self-plagiarism across papers.** Before adding a theorem, grep
           every sibling paper in papers/publication/2026_*/*.tex. If ≥70%
           literal overlap or the statement already exists under another label,
           abort that theorem and choose a different extension direction.
        5. **Rigorous academic register only.** No colloquialisms, no
           first-person narrative ("we now show", "note that"), no filler
           ("interestingly", "remarkably"), no hedging ("it seems", "likely").
           Use the formal declarative voice of top-tier journal papers.

        ## Strategy
        Concrete ways to add depth (pick what fits the paper):
        - Generalize a restricted result to a broader setting (wider function class,
          higher dimension, more general spaces)
        - Prove a converse / optimality / rigidity statement
        - Establish quantitative refinements (sharp constants, error bounds)
        - Connect to another area and derive applications
        - Prove a structural classification the existing results hinted at
        - Extend from special cases (cube/monomial/abelian) to general cases

        ## Output
        Integrate new content into the existing paper structure. Edit .tex files
        directly. After editing, compile:
          cd {paper_dir} && xelatex -interaction=nonstopmode main.tex

        No revision artifacts, no changelogs. Write as if this was always in the paper.
    """)


def build_journal_style_prompt(paper_dir: str, target_journal: str,
                                round_num: int) -> str:
    return textwrap.dedent(f"""\
        You are a senior copyeditor who has published extensively in "{target_journal}".
        This is style-optimization round {round_num} for: {paper_dir}

        ## Task: Full Journal-Style Optimization

        Study the language, structure, and conventions of papers recently published
        in "{target_journal}". Then comprehensively rewrite this paper to match.

        Specific requirements:
        - Prose should read as natural expert writing, NOT as AI-generated text.
          Vary sentence length. Use the specific phrasings, transitions, and
          hedging patterns that human authors in this journal actually use.
        - Study how published papers in this journal balance main body vs. appendix
          content. Adjust our paper's ratio to match.
        - Match the journal's conventions for: writing style, word choice habits,
          logical progression, theorem-proof formatting, section structure,
          introduction framing, abstract density, citation style.
        - You may restructure sections, merge or split content, reorder arguments
          — whatever produces the most natural, journal-native result.
        - Preserve all mathematical content and \\leanverified annotations.
        - No revision artifacts, no "we improved", no changelogs.

        ## Output
        Edit .tex files directly. Compile when done:
          cd {paper_dir} && xelatex -interaction=nonstopmode main.tex
    """)


def build_self_score_prompt(paper_dir: str, target_journal: str) -> str:
    return textwrap.dedent(f"""\
        You are a referee for "{target_journal}". Read the paper in {paper_dir}.

        Score the paper from 1 to 10 on each dimension, then give an overall score.

        ## Calibration anchor (use this distribution)
        - A paper accepted at "{target_journal}" typically scores 8.
        - A paper recently rejected by "{target_journal}" typically scores 5–6.
        - A paper with correct but derivative content scores 4.
        - Score ≥9 is reserved for results the journal would highlight.
        Prior: P(score ≥ 8) ≤ 5%, P(score ≥ 9) ≤ 1%.

        If you propose overall_score ≥ 8, you MUST name in "strengths" three
        specific papers from "{target_journal}" in the last 24 months that you
        believe are comparable or weaker than this submission, with a one-line
        reason each. Unsubstantiated ≥8 scores are treated as evidence of
        self-inflation and will be rejected by the downstream Claude reviewer.

        ## Scoring Dimensions
        1. **Mathematical depth & novelty** (are the results genuinely new?)
        2. **Proof completeness** (any gaps, missing steps, implicit assumptions?)
        3. **Writing quality** (natural academic prose, not AI-generated?)
        4. **Journal fit** (matches "{target_journal}" conventions?)
        5. **Structure & flow** (logical progression, appropriate body/appendix ratio?)

        ## Issue Classification
        For each key issue, classify as:
          - SURFACE: fixable by editing (wording, structure, missing cite)
          - FUNDAMENTAL: needs deeper research to fix — insufficient novelty for
            the journal, results too shallow, proofs depend on un-justified inputs,
            or pieces lack conceptual unity. These require NEW mathematical content,
            not editing. (The pipeline will escalate to deep-research extension.)

        ## Output Format (MUST follow exactly)
        Output a single JSON block:

        ```json
        {{
          "scores": {{
            "depth_novelty": <1-10>,
            "proof_completeness": <1-10>,
            "writing_quality": <1-10>,
            "journal_fit": <1-10>,
            "structure_flow": <1-10>
          }},
          "overall_score": <1-10>,
          "verdict": "<accept|revise|reject>",
          "key_issues": [
            {{"issue": "...", "type": "SURFACE|FUNDAMENTAL"}}
          ],
          "strengths": ["strength1", "strength2", ...],
          "specific_fixes": ["fix1", "fix2", ...],
          "research_directions": [
            "concrete new theorem/extension that would raise the paper to 8+"
          ],
          "prognosis_can_reach_8": "yes|no|unclear"
        }}
        ```

        Be ruthlessly honest.
        - prognosis_can_reach_8="yes" → SURFACE issues only, editing will fix
        - prognosis_can_reach_8="no" → needs NEW mathematical content. Fill
          research_directions with concrete extensions (new theorems, wider settings,
          sharper bounds, applications, converses) that would elevate the paper.
          The pipeline will use these to drive deep-research extension.
        Do NOT edit any files — only output the JSON evaluation.
    """)


def build_oracle_review_prompt(target_journal: str) -> str:
    return textwrap.dedent(f"""\
        You are a referee for "{target_journal}". Review the attached paper.

        Start your reply with a single line exactly of the form
          Overall verdict: <Accept|Minor revision|Major revision|Reject>
        so the verdict can be parsed unambiguously. Then provide the full review.

        1. **Overall verdict** (labelled as above)
        2. **Novelty rating** per main theorem: HIGH / MEDIUM / LOW with a
           one-sentence justification.
        3. **Issue table** (Markdown table; no empty cells):
           ID | Section | Severity (BLOCKER/MEDIUM/LOW) | Description | Suggested fix
        4. **Proof audit**: Pick the TWO deepest theorems. Redo the key identity
           by hand. Report any step where a suspicious identity is silently used,
           e.g.  χ(C^{{-1}}) = χ(C)  (should be conjugate),  Tr(AB) = Tr(A)Tr(B),
           det(A+B) = det(A)+det(B), det(exp A) = exp(det A), limit/sum exchange
           without justification, cancellation of an operator that may be
           non-invertible. Cite line numbers.
        5. **Conditional hypothesis map**: List every hypothesis invoked in the
           main theorems. For each, flag verifiable / generically satisfied /
           open, and say whether the manuscript correctly discloses its status.
        6. **Theorem-by-theorem comparison with last 5 years of {target_journal}**:
           output a Markdown table with columns
             our result | closest prior result | citation | novel increment
           One row per main theorem.
        7. **Missing references**: important related work not cited. Give DOI
           or arXiv number where possible.
        8. **Concrete fixes**: for each BLOCKER and MEDIUM issue, show HOW to
           fix with mathematical content (corrected proof sketch, precise bound,
           missing lemma statement, etc.).

        Be rigorous. Do not hedge. Focus on what needs to change, not on what
        the paper already says. A single wrong identity in a main theorem is a
        BLOCKER, not a LOW.
    """)


def build_oracle_re_review_prompt(target_journal: str) -> str:
    return textwrap.dedent(f"""\
        This is a REVISED paper resubmitted to "{target_journal}".

        1. For each previous issue: RESOLVED / PARTIALLY / UNRESOLVED
        2. Any new problems introduced?
        3. Overall verdict: Accept / Minor revision / Major revision / Reject
        4. Remaining blockers preventing acceptance

        If this paper now meets the standards of "{target_journal}", state Accept.
    """)


def build_codex_fix_from_issues_prompt(paper_dir: str, issues_text: str,
                                        round_num: int) -> str:
    return textwrap.dedent(f"""\
        You are fixing referee issues in the paper at: {paper_dir}
        Fix round {round_num}.

        ## Issues to fix (severity-sorted)
        {issues_text}

        ## Instructions
        1. Fix BLOCKER issues first, then MEDIUM, then LOW
        2. For mathematical gaps: add missing proof steps or lemmas
        3. For unclear arguments: rewrite with explicit reasoning
        4. For missing references: add to references.bib and cite
        5. Do NOT delete existing theorems — improve them
        6. Do NOT add revision notes or "fixed per reviewer" language
        7. Keep all \\leanverified annotations intact
        8. Compile: cd {paper_dir} && xelatex -interaction=nonstopmode main.tex

        Only edit .tex and .bib files inside {paper_dir}.
    """)


def build_claude_independent_review_prompt(paper_dir: str,
                                            target_journal: str) -> str:
    return textwrap.dedent(f"""\
        Independent pre-submission review for "{target_journal}".
        Paper directory: {paper_dir}

        Read ALL .tex files. Evaluate as if you are the final gatekeeper before
        submission. Check:

        1. Every proof is complete — no gaps, no hand-waving
        2. No revision artifacts ("we fixed", "as suggested", etc.)
        3. Writing reads as natural expert prose, not AI-generated
        4. References compile (no ?? or missing citations)
        5. Section structure matches "{target_journal}" conventions
        6. Body/appendix ratio is appropriate
        7. \\leanverified tags reference actual Lean theorems
        8. Abstract accurately summarizes contributions

        ## Output Format (MUST follow exactly)
        ```json
        {{
          "verdict": "<submit|revise>",
          "issues": ["issue1", "issue2", ...],
          "quality_notes": "free text summary"
        }}
        ```

        verdict = "submit" means ready for journal submission.
        verdict = "revise" means more work needed — list issues precisely.
        Do NOT edit files — only output the JSON review.
    """)


def build_codex_fix_from_claude_prompt(paper_dir: str,
                                        issues: list[str],
                                        round_num: int) -> str:
    issues_text = "\n".join(f"  {i+1}. {iss}" for i, iss in enumerate(issues))
    return textwrap.dedent(f"""\
        Fix issues found by independent Claude review.
        Paper: {paper_dir}
        Fix round {round_num}.

        ## Issues
        {issues_text}

        ## Instructions
        1. Read the relevant .tex files
        2. Fix each issue directly
        3. No revision notes, no changelogs
        4. Compile: cd {paper_dir} && xelatex -interaction=nonstopmode main.tex

        Only edit .tex and .bib files inside {paper_dir}.
    """)


def build_backflow_check_prompt(paper_dir: str, main_paper_dir: str) -> str:
    return textwrap.dedent(f"""\
        You are checking whether results from a sub-paper should flow back
        into the main paper.

        Sub-paper (just improved): {paper_dir}
        Main paper: {main_paper_dir}

        ## Task
        1. Read both papers
        2. Identify theorems, lemmas, or results in the sub-paper that are:
           - Referenced or used by the main paper
           - Stronger/corrected versions of results in the main paper
           - New results that should be cited or incorporated
        3. For each candidate, specify exactly what should change in the main paper

        ## Output Format (MUST follow exactly)
        ```json
        {{
          "backflow_items": [
            {{
              "sub_paper_result": "Theorem 3.2 (improved bound)",
              "main_paper_location": "Section 4, after Proposition 4.1",
              "action": "update_citation|add_reference|incorporate_result|update_statement",
              "detail": "exact description of what to change"
            }}
          ],
          "summary": "one paragraph overview"
        }}
        ```

        If nothing needs to flow back, return empty backflow_items array.
        Do NOT edit any files — only output the JSON analysis.
    """)


def build_backflow_apply_prompt(paper_dir: str, main_paper_dir: str,
                                 items: list[dict]) -> str:
    items_text = ""
    for i, item in enumerate(items, 1):
        items_text += (
            f"  {i}. [{item.get('action','')}] "
            f"{item.get('sub_paper_result','')}\n"
            f"     Location: {item.get('main_paper_location','')}\n"
            f"     Detail: {item.get('detail','')}\n"
        )
    return textwrap.dedent(f"""\
        Apply backflow changes from sub-paper to main paper.

        Sub-paper: {paper_dir}
        Main paper: {main_paper_dir}

        ## Changes to apply
        {items_text}

        ## Instructions
        1. Read the main paper's .tex files
        2. Apply each change as specified
        3. Update references.bib if new citations are needed
        4. Keep all existing content intact — only add/update as specified
        5. Compile: cd {main_paper_dir} && xelatex -interaction=nonstopmode main.tex

        Only edit files in {main_paper_dir}.
    """)


# ---------------------------------------------------------------------------
# Parsing helpers
# ---------------------------------------------------------------------------

def parse_json_from_output(text: str) -> dict:
    """Extract first JSON block from codex/claude output."""
    m = re.search(r"```json\s*(\{.*?\})\s*```", text, re.DOTALL)
    if m:
        try:
            return json.loads(m.group(1))
        except json.JSONDecodeError:
            pass
    # Try bare JSON
    for m2 in re.finditer(r'\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}', text, re.DOTALL):
        try:
            d = json.loads(m2.group(0))
            if any(k in d for k in ("overall_score", "verdict", "backflow_items",
                                      "scores", "issues")):
                return d
        except json.JSONDecodeError:
            continue
    return {}


def parse_oracle_issues(review_text: str) -> list[dict]:
    """Extract structured issues from oracle review."""
    issues = []
    # Table rows: ID | Section | BLOCKER | desc | fix
    rows = re.findall(
        r"(\d+)\s*\|\s*([^|]+)\|\s*(BLOCKER|MEDIUM|LOW|HIGH|CRITICAL)\s*\|\s*([^|]+?)(?:\|\s*(.+))?$",
        review_text, re.MULTILINE | re.IGNORECASE,
    )
    for row in rows:
        issues.append({
            "id": row[0].strip(), "section": row[1].strip(),
            "severity": row[2].strip().upper(),
            "description": row[3].strip(),
            "suggested_fix": row[4].strip() if len(row) > 4 and row[4] else "",
        })
    # Fallback: numbered items
    if not issues:
        for m in re.finditer(
            r"(?:^|\n)\s*(\d+)[.)\]]\s*(.*?(?:BLOCKER|MEDIUM|LOW|CRITICAL|HIGH).*?)(?=\n\s*\d+[.)\]]|\Z)",
            review_text, re.DOTALL | re.IGNORECASE,
        ):
            sev = re.search(r"(BLOCKER|CRITICAL|HIGH|MEDIUM|LOW)",
                            m.group(2), re.IGNORECASE)
            issues.append({
                "id": m.group(1).strip(), "section": "unknown",
                "severity": sev.group(1).upper() if sev else "MEDIUM",
                "description": m.group(2).strip()[:500],
                "suggested_fix": "",
            })
    sev_order = {"BLOCKER": 0, "CRITICAL": 1, "HIGH": 2, "MEDIUM": 3, "LOW": 4}
    issues.sort(key=lambda x: sev_order.get(x.get("severity", "LOW"), 5))
    return issues


_VERDICT_PATTERNS = (
    r"minor\s+revision",
    r"major\s+revision",
    r"^reject(?:ion)?\s*$",
    r"\breject\b(?!\s+(?:if|when|unless|on\s))",
    r"\baccept(?:ed)?\b(?!ance|able)",
)


def extract_verdict(text: str) -> str:
    """Parse the Oracle's overall verdict.

    Priority 1: an explicit label like "Overall verdict:" / "Recommendation:".
    Priority 2: search the first and last 1500 chars only (verdict belongs to
    the summary sections, not mid-review discussion of alternatives).
    Priority 3: tolerate substring false positives by requiring word boundaries
    and rejecting occurrences inside "acceptance", "unacceptable", "reject if …".
    """
    t = text.strip()

    # Priority 1: labelled verdict line
    label = re.search(
        r"(?:overall\s+verdict|recommendation|decision|final\s+verdict)\s*[:\-]\s*"
        r"(accept(?:ed)?|minor\s+revision|major\s+revision|reject(?:ion)?)",
        t, re.IGNORECASE,
    )
    if label:
        v = label.group(1).lower().strip()
        v = re.sub(r"\s+", " ", v)
        if v.startswith("accept"):
            return "accept"
        if v.startswith("minor"):
            return "minor revision"
        if v.startswith("major"):
            return "major revision"
        if v.startswith("reject"):
            return "reject"

    # Priority 2: scan head + tail where conclusions usually sit
    head = t[:1500].lower()
    tail = t[-1500:].lower()
    for zone in (head, tail):
        # Prefer strongest verdict first, then revisions, then accept, then reject
        if re.search(r"minor\s+revision", zone):
            return "minor revision"
        if re.search(r"major\s+revision", zone):
            return "major revision"
        if re.search(r"\baccept(?:ed)?\b(?!ance|able)", zone):
            return "accept"
        if re.search(r"\breject(?:ion|ed)?\b(?!\s+(?:if|when|unless|on\s))",
                     zone):
            return "reject"
    return "unknown"


def format_issues_for_codex(issues: list[dict]) -> str:
    lines = []
    for i, iss in enumerate(issues, 1):
        sev = iss.get("severity", "?")
        sec = iss.get("section", "?")
        desc = iss.get("description", "")
        fix = iss.get("suggested_fix", "")
        lines.append(f"  {i}. [{sev}] Section {sec}: {desc}")
        if fix:
            lines.append(f"     Suggested fix: {fix}")
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════
# STAGE F: Journal Fit Check (one-shot, auto-reroute if poor fit)
# ═══════════════════════════════════════════════════════════════════════════

FIT_PASS_THRESHOLD = 6


def build_journal_fit_prompt(paper_dir: str, target_journal: str) -> str:
    return textwrap.dedent(f"""\
        You are an experienced editor who handles submissions for multiple
        mathematics and mathematical-physics journals.

        Paper directory: {paper_dir}
        Proposed target journal: "{target_journal}"

        ## Task: Journal-Fit Assessment

        Read the paper and evaluate how well it fits "{target_journal}".
        Consider:
        1. **Subject area match** — does the paper's topic fall within the
           journal's typical scope? (e.g., pure math journal vs applied,
           analysis vs algebra vs geometry, physics-adjacent vs pure)
        2. **Technical depth** — is the mathematical depth at the level the
           journal expects? (top journal = deep new theory; specialized
           journal = solid contribution in a niche)
        3. **Length & style** — does the paper's size and exposition match
           the journal's norms?
        4. **Impact expectation** — would referees of this journal find the
           results significant?
        5. **Competition** — are there better-fit journals for this exact topic?

        ## Output Format (MUST follow exactly)
        ```json
        {{
          "fit_score": <1-10>,
          "fit_verdict": "<excellent|good|marginal|poor>",
          "subject_match": <1-10>,
          "depth_match": <1-10>,
          "style_match": <1-10>,
          "rationale": "2-3 sentence explanation",
          "suggested_journals": [
            {{
              "name": "Journal Name",
              "fit_score": <1-10>,
              "reason": "why this is a better fit"
            }}
          ]
        }}
        ```

        suggested_journals: list 2-3 alternatives ranked by fit.
        Always include the original target journal in your comparison.
        Do NOT edit any files — only output the JSON assessment.
    """)


def run_stage_f(state: PaperState, *, dry_run: bool = False,
                model: Optional[str] = None) -> bool:
    """Stage F: Journal fit check. One-shot. Auto-reroutes if poor fit."""
    tag = f"[{state.paper_name}|F]"
    paper_path = Path(state.paper_dir)

    state.stage_f_original_journal = state.target_journal
    save_state(state)

    # ── F1: Codex fit assessment ─────────────────────────────────
    logger.info(f"{tag} F1 — Codex journal fit assessment "
                f"(target: {state.target_journal})")
    prompt = build_journal_fit_prompt(state.paper_dir, state.target_journal)
    out = codex_exec(prompt, work_dir=paper_path,
                     timeout_seconds=600, model=model, dry_run=dry_run)

    fit_data = parse_json_from_output(out) if not dry_run else {
        "fit_score": 5, "fit_verdict": "marginal",
        "subject_match": 4, "depth_match": 6, "style_match": 5,
        "rationale": "dry run: paper is marginal fit for target",
        "suggested_journals": [
            {"name": "Journal of Functional Analysis", "fit_score": 8,
             "reason": "better scope match"},
            {"name": "Advances in Mathematics", "fit_score": 5,
             "reason": "too broad for this paper"},
        ],
    }

    # Fail-safe: JSON parse failure must NOT trigger reroute with phantom 0.
    # Keep the original target journal and let Stage A handle quality issues.
    if not fit_data or fit_data.get("fit_score") is None:
        logger.warning(f"{tag} F1 JSON parse failed (response {len(out)} chars) "
                       f"— keeping original journal '{state.target_journal}', "
                       f"skipping reroute gate")
        state.stage_f_fit_score = -1
        state.stage_f_passed = True
        state.log_event("F", "fit_parse_failed",
                        detail=f"raw_head={out[:500]}")
        save_state(state)
        return True

    fit_score = fit_data.get("fit_score", 0)
    state.stage_f_fit_score = fit_score
    state.log_event("F", "codex_fit_assessment", score=fit_score,
                    detail=json.dumps(fit_data, ensure_ascii=False)[:10000])
    save_state(state)

    logger.info(f"{tag} Fit score: {fit_score}/10 "
                f"(threshold: {FIT_PASS_THRESHOLD})")

    # ── F2: Claude review — ONLY in the ambiguous zone ────────────
    # Skip Claude for clear cases: high fit score = trust Codex; very low fit
    # = trust Codex's reroute suggestion. Only invoke Claude in the gray band
    # 4 ≤ fit ≤ 6 where the journal-match call is genuinely close.
    alts = fit_data.get("suggested_journals", [])
    codex_top_recommendation = alts[0]["name"] if alts else state.target_journal

    if fit_score >= 7:
        # Clear pass — trust Codex, skip Claude entirely
        logger.info(f"{tag} F2 skipped (fit={fit_score} ≥ 7, high-confidence pass)")
        final_fit = fit_score
        recommended = state.target_journal
    elif fit_score <= 3:
        # Clear fail — adopt Codex's top alternative, skip Claude
        logger.info(f"{tag} F2 skipped (fit={fit_score} ≤ 3, adopting Codex's "
                    f"top suggestion: {codex_top_recommendation})")
        final_fit = fit_score
        recommended = codex_top_recommendation
    else:
        # Ambiguous zone 4-6: Claude second opinion is load-bearing
        logger.info(f"{tag} F2 — Claude review (ambiguous fit={fit_score})")
        claude_prompt = textwrap.dedent(f"""\
            Review this journal-fit assessment.
            Paper: {state.paper_dir}
            Target: {state.target_journal}

            Codex assessment:
            {json.dumps(fit_data, indent=2, ensure_ascii=False)[:3000]}

            Questions:
            1. Is the fit score fair?
            2. Are the suggested alternative journals reasonable?
            3. Which journal would you recommend?

            Output ONLY:
            ```json
            {{
              "adjusted_fit_score": <1-10>,
              "recommended_journal": "journal name",
              "notes": "brief explanation"
            }}
            ```
        """)
        out2 = claude_exec(claude_prompt, work_dir=paper_path, dry_run=dry_run)
        claude_data = parse_json_from_output(out2) if not dry_run else {
            "adjusted_fit_score": 4,
            "recommended_journal": "Journal of Functional Analysis",
            "notes": "dry run",
        }
        adjusted = claude_data.get("adjusted_fit_score", fit_score)
        recommended = claude_data.get(
            "recommended_journal", codex_top_recommendation)
        final_fit = min(fit_score, adjusted)
        state.log_event("F", "claude_review_fit", score=adjusted,
                        detail=json.dumps(claude_data,
                                          ensure_ascii=False)[:10000])
        save_state(state)
        logger.info(f"{tag} Final fit: {final_fit}/10 "
                    f"(codex={fit_score}, claude={adjusted})")

    # ── Gate: fit ≥ threshold → keep target; else → reroute ──────
    if final_fit >= FIT_PASS_THRESHOLD:
        logger.info(f"{tag} STAGE F PASSED — keeping target: "
                    f"{state.target_journal}")
        state.stage_f_passed = True
        save_state(state)
        return True

    # Auto-reroute to recommended journal
    old = state.target_journal
    state.target_journal = recommended
    state.stage_f_suggested_journal = recommended
    state.stage_f_passed = True
    save_state(state)

    logger.info(f"{tag} FIT TOO LOW ({final_fit} < {FIT_PASS_THRESHOLD}) — "
                f"rerouting: {old} → {recommended}")

    # Log the suggested alternatives (alts defined earlier at F2)
    for alt in alts[:3]:
        logger.info(f"{tag}   Alternative: {alt.get('name', '?')} "
                    f"(fit={alt.get('fit_score', '?')}): "
                    f"{alt.get('reason', '')}")

    return True


# ═══════════════════════════════════════════════════════════════════════════
# STAGE A: Codex Quality Review + Journal Style (score-gated loop)
# ═══════════════════════════════════════════════════════════════════════════

def run_stage_a_dedup(state: PaperState, *, round_num: int,
                       model: Optional[str] = None,
                       dry_run: bool = False, tag: str = "") -> bool:
    """Cross-paper self-plagiarism check, triggered after A-DEEP.

    Runs a programmatic overlap scan across all sibling papers under
    papers/publication/. If overlaps are found, invokes Codex once to
    resolve each via cite/reframe/delete. Cheap filter → expensive fix,
    so this is skipped entirely when the paper has no duplicate phrasing
    (the common case).
    """
    paper_path = Path(state.paper_dir)
    logger.info(f"{tag} A-DEDUP — Cross-paper overlap scan")

    if dry_run:
        logger.info(f"{tag} A-DEDUP [dry run] skip")
        return True

    # Collect sibling papers (everything in papers/publication/ except self
    # and non-paper directories)
    siblings: list[Path] = []
    if PAPERS_PUB_DIR_CONST.exists():
        for p in PAPERS_PUB_DIR_CONST.iterdir():
            if not p.is_dir():
                continue
            if p.name.startswith("."):
                continue
            if p.name in ("oracle", "backflow", "strategy"):
                continue
            if p.resolve() == paper_path.resolve():
                continue
            siblings.append(p)

    overlaps = detect_cross_paper_overlaps(paper_path, siblings)
    if not overlaps:
        logger.info(f"{tag} A-DEDUP: no overlaps found, skip")
        state.log_event("A", "cross_paper_dedup", round_num=round_num,
                        detail="clean: 0 overlaps")
        save_state(state)
        return True

    logger.warning(f"{tag} A-DEDUP: found {len(overlaps)} overlap candidates, "
                   f"invoking Codex to resolve")
    # Truncate list to avoid prompt blow-up; worst offenders first
    overlaps_json = json.dumps(overlaps[:15], indent=2, ensure_ascii=False)

    prompt = build_cross_paper_dedup_prompt(state.paper_dir, overlaps_json)
    codex_exec(prompt, work_dir=paper_path,
               timeout_seconds=2400, model=model, dry_run=dry_run)
    compiled = compile_gate(paper_path, model=model, dry_run=dry_run,
                            tag=f"{tag} A-DEDUP")
    git_stage(paper_path, tag=tag)  # A-DEDUP intermediate
    state.log_event("A", "cross_paper_dedup", round_num=round_num,
                    detail=f"{len(overlaps)} overlaps resolved; "
                           f"compiled={compiled}",
                    committed=False, commit_hash="")
    save_state(state)
    return True


def run_stage_a(state: PaperState, *, dry_run: bool = False,
                model: Optional[str] = None) -> bool:
    tag = f"[{state.paper_name}|A]"
    paper_path = Path(state.paper_dir)

    # Snapshot theorems at Stage A start for content change summary
    _stage_a_pre_theorems = extract_theorem_statements(paper_path)

    # ── A0: Literature audit (one-shot, before any round) ─────────
    # This is the highest-leverage prompt: it reclassifies over-claimed
    # theorems as supporting propositions and produces the comparison table
    # that earlier manual interventions found most valuable.
    if not state.stage_a0_done:
        logger.info(f"{tag} A0 — Literature audit + positioning")
        prompt_a0 = build_literature_audit_prompt(
            state.paper_dir, state.target_journal)
        codex_exec(prompt_a0, work_dir=paper_path,
                   timeout_seconds=3600, model=model, dry_run=dry_run)
        compiled_a0 = compile_gate(paper_path, model=model, dry_run=dry_run,
                                   tag=f"{tag} A0")
        h = git_commit(paper_path,
                       "stage-A0: literature audit + theorem demotion"
                       + ("" if compiled_a0 else " (compile FAILED)"),
                       tag=tag)
        state.stage_a0_done = True
        state.log_event("A", "literature_audit",
                        committed=bool(h), commit_hash=h,
                        detail=f"compiled={compiled_a0}")
        save_state(state)

    for rnd in range(state.stage_a_rounds + 1, MAX_STAGE_A_ROUNDS + 1):
        state.stage_a_rounds = rnd
        state.current_round = rnd
        save_state(state)

        # ── A1: Codex quality review + fix ─────────────────────────
        # Accumulate feedback from previous rounds so codex addresses persistent
        # issues rather than repeating surface fixes.
        prior_feedback = ""
        if state.history:
            past_scores = []
            past_issues = []
            for h_ev in state.history[-20:]:
                if h_ev.get("action") in ("codex_self_score",
                                           "claude_review_score"):
                    past_scores.append(
                        f"R{h_ev.get('round_num')} "
                        f"{h_ev.get('action')}: "
                        f"{h_ev.get('score', '?')}/10"
                    )
                    # Try to extract issue list from detail JSON
                    try:
                        d = json.loads(h_ev.get("detail", "{}"))
                        for issue in d.get("key_issues", [])[:3]:
                            if isinstance(issue, dict):
                                past_issues.append(
                                    f"  - [{issue.get('type', '?')}] "
                                    f"R{h_ev.get('round_num')}: "
                                    f"{issue.get('issue', '')[:200]}"
                                )
                            else:
                                past_issues.append(
                                    f"  - R{h_ev.get('round_num')}: "
                                    f"{str(issue)[:200]}"
                                )
                    except Exception:
                        pass
            if past_scores or past_issues:
                prior_feedback = ("Score history: " + ", ".join(past_scores[-6:])
                                  + "\n\nRecurring issues:\n"
                                  + "\n".join(past_issues[-8:]))

        # Escalate timeout if stuck in low scores (borrowed from outreach pipeline)
        low_rounds = sum(1 for s in state.stage_a_scores if s < SCORE_PASS_THRESHOLD)
        a1_timeout = 3600 if low_rounds >= 2 else 2400

        logger.info(f"{tag} Round {rnd}: A1 — Codex quality review "
                    f"(timeout={a1_timeout}s, prior_rounds={len(state.stage_a_scores)})")
        prompt_a1 = build_quality_review_prompt(
            state.paper_dir, state.target_journal, rnd,
            prior_feedback=prior_feedback)
        codex_exec(prompt_a1, work_dir=paper_path,
                   timeout_seconds=a1_timeout, model=model, dry_run=dry_run)
        compiled_a1 = compile_gate(paper_path, model=model, dry_run=dry_run,
                                   tag=f"{tag} A1")
        git_stage(paper_path, tag=tag)  # A1 intermediate
        state.log_event("A", "codex_quality_review", round_num=rnd,
                        committed=bool(h), commit_hash=h,
                        detail=f"compiled={compiled_a1}")
        save_state(state)

        # ── A2: Codex journal style optimization ─────────────────
        logger.info(f"{tag} Round {rnd}: A2 — Codex journal style")
        prompt_a2 = build_journal_style_prompt(
            state.paper_dir, state.target_journal, rnd)
        codex_exec(prompt_a2, work_dir=paper_path,
                   timeout_seconds=2400, model=model, dry_run=dry_run)
        compiled_a2 = compile_gate(paper_path, model=model, dry_run=dry_run,
                                   tag=f"{tag} A2")
        git_stage(paper_path, tag=tag)  # A2 intermediate optimization"
        state.log_event("A", "codex_journal_style", round_num=rnd,
                        committed=bool(h), commit_hash=h,
                        detail=f"compiled={compiled_a2}")
        save_state(state)

        # ── A3: Codex self-score (retry if empty JSON) ──────────
        score_data = {}
        # ── A3 + A4: Parallel independent dual review ───────────────
        # Both Codex and Claude read the paper fresh and score independently.
        # Neither sees the other's answer — that's the whole point. Running
        # them in parallel cuts wall-time by ~40% and eliminates the 跟风
        # failure mode where Claude just ratifies whatever Codex said.
        logger.info(f"{tag} Round {rnd}: A3+A4 — Parallel independent dual review")

        def _codex_score():
            prompt = build_self_score_prompt(
                state.paper_dir, state.target_journal)
            for attempt in range(1, 3):
                out = codex_exec(prompt, work_dir=paper_path,
                                 timeout_seconds=600, model=model,
                                 dry_run=dry_run)
                data = parse_json_from_output(out) if not dry_run else {
                    "overall_score": 6 + rnd,
                    "verdict": "revise" if rnd < 3 else "accept",
                    "key_issues": [f"dry run codex issue R{rnd}"],
                    "specific_fixes": [f"dry run codex fix R{rnd}"],
                    "prognosis_can_reach_8": "yes",
                }
                if data.get("overall_score") is not None:
                    return data
                logger.warning(f"{tag} Codex self-score attempt {attempt} "
                               f"empty/unparseable, retrying")
            return {}

        def _claude_score():
            prompt = build_self_score_prompt(
                state.paper_dir, state.target_journal)
            for attempt in range(1, 3):
                out = claude_exec(prompt, work_dir=paper_path,
                                  dry_run=dry_run)
                data = parse_json_from_output(out) if not dry_run else {
                    "overall_score": 5 + rnd,
                    "verdict": "revise" if rnd < 3 else "accept",
                    "key_issues": [f"dry run claude issue R{rnd}"],
                    "specific_fixes": [f"dry run claude fix R{rnd}"],
                    "prognosis_can_reach_8": "yes",
                }
                if data.get("overall_score") is not None:
                    return data
                logger.warning(f"{tag} Claude self-score attempt {attempt} "
                               f"empty/unparseable, retrying")
            return {}

        with ThreadPoolExecutor(max_workers=2) as ex:
            f_codex = ex.submit(_codex_score)
            f_claude = ex.submit(_claude_score)
            score_data = f_codex.result()
            claude_data = f_claude.result()

        score = score_data.get("overall_score", 0) if score_data else 0
        adjusted = claude_data.get("overall_score", 0) if claude_data else 0

        state.stage_a_scores.append(score)
        state.log_event("A", "codex_self_score", round_num=rnd,
                        score=score,
                        detail=json.dumps(score_data, ensure_ascii=False)[:10000])
        state.log_event("A", "claude_independent_score", round_num=rnd,
                        score=adjusted,
                        detail=json.dumps(claude_data, ensure_ascii=False)[:10000])
        save_state(state)

        logger.info(f"{tag} Round {rnd}: Codex={score}/10  Claude={adjusted}/10 "
                    f"(threshold = {SCORE_PASS_THRESHOLD})")

        # Skip rounds where BOTH reviewers returned empty JSON; if one is
        # empty and the other succeeded, use the successful one as the
        # single-side signal (min() would collapse to 0 otherwise).
        codex_ok = bool(score_data and score_data.get("overall_score") is not None)
        claude_ok = bool(claude_data and claude_data.get("overall_score") is not None)
        if not codex_ok and not claude_ok:
            logger.warning(f"{tag} Round {rnd}: both reviewers returned empty "
                           f"JSON, skipping decision")
            continue
        if codex_ok and claude_ok:
            final_score = min(score, adjusted)
        elif codex_ok:
            logger.warning(f"{tag} Claude score missing, using codex={score}")
            final_score = score
        else:
            logger.warning(f"{tag} Codex score missing, using claude={adjusted}")
            final_score = adjusted

        logger.info(f"{tag} Round {rnd}: Final score = {final_score} "
                    f"(codex={score}, claude={adjusted}, min-of-both)")

        # ── Handle FUNDAMENTAL verdict: escalate to DEEP RESEARCH ──
        # "FUNDAMENTAL" = paper not deep enough → push deeper, don't downgrade.
        # Both reviewers must independently say "no" to avoid false escalation.
        codex_prog = score_data.get("prognosis_can_reach_8", "unclear") if score_data else "unclear"
        claude_prog = claude_data.get("prognosis_can_reach_8", "unclear") if claude_data else "unclear"
        if codex_prog == "no" and claude_prog == "no":
            logger.warning(f"{tag} FUNDAMENTAL depth issue flagged. "
                           f"Escalating to DEEP RESEARCH extension.")

            # Collect concerns from BOTH independent reviewers. Union of
            # issues gives A-DEEP a richer failure-mode map than any single
            # reviewer would produce.
            prior_issues = json.dumps({
                "codex_key_issues": score_data.get("key_issues", []) if score_data else [],
                "codex_specific_fixes": score_data.get("specific_fixes", []) if score_data else [],
                "codex_research_directions": score_data.get("research_directions", []) if score_data else [],
                "claude_key_issues": claude_data.get("key_issues", []) if claude_data else [],
                "claude_specific_fixes": claude_data.get("specific_fixes", []) if claude_data else [],
                "claude_research_directions": claude_data.get("research_directions", []) if claude_data else [],
                "current_score_codex": score,
                "current_score_claude": adjusted,
                "final_score": final_score,
            }, ensure_ascii=False, indent=2)[:5000]

            logger.info(f"{tag} Round {rnd}: A-DEEP — Codex deep research extension")

            # Snapshot theorems BEFORE deep extension (for anti-fake gate)
            pre_theorems = extract_theorem_statements(paper_path)

            deep_prompt = build_deep_extension_prompt(
                state.paper_dir, state.target_journal, prior_issues, rnd)
            codex_exec(deep_prompt, work_dir=paper_path,
                       timeout_seconds=3600, model=model, dry_run=dry_run)
            compiled_deep = compile_gate(paper_path, model=model,
                                         dry_run=dry_run,
                                         tag=f"{tag} A-DEEP")

            # Anti-fake gate: verify A-DEEP actually added substance
            if not dry_run:
                substantive, reason = verify_substantive_change(
                    paper_path, pre_theorems)
                if not substantive:
                    logger.warning(f"{tag} ANTI-FAKE: {reason}")
                    logger.warning(f"{tag} Reverting codex deep extension — "
                                   f"no real content added")
                    # Revert the fake changes
                    run_cmd(["git", "checkout", "--", str(paper_path)])
                    state.log_event("A", "anti_fake_revert", round_num=rnd,
                                    detail=reason)
                    save_state(state)
                    continue
                else:
                    logger.info(f"{tag} Anti-fake: PASS — {reason}")

            git_stage(paper_path, tag=tag)  # A-DEEP intermediate
            state.log_event("A", "codex_deep_extension", round_num=rnd,
                            score=final_score,
                            detail=f"Triggered by FUNDAMENTAL verdict "
                                   f"at score {final_score}/10; "
                                   f"compiled={compiled_deep}",
                            committed=False, commit_hash="")
            save_state(state)

            # ── A-DEDUP: cross-paper self-plagiarism check ──────────
            # A-DEEP may generate new theorems that duplicate content in
            # sibling papers (we have 20+ related papers). Run cheap
            # programmatic scan first; only invoke Codex if overlaps found.
            run_stage_a_dedup(state, round_num=rnd, model=model,
                              dry_run=dry_run, tag=tag)

            logger.info(f"{tag} Deep extension complete, continuing to next round "
                        f"for re-evaluation")
            continue

        # ── Gate: pass if ≥ threshold ────────────────────────────
        if final_score >= SCORE_PASS_THRESHOLD:
            logger.info(f"{tag} STAGE A PASSED at round {rnd} "
                        f"(score {final_score} >= {SCORE_PASS_THRESHOLD})")
            content_summary = summarize_content_changes(
                paper_path, _stage_a_pre_theorems)
            git_commit(paper_path,
                       f"Stage A ({final_score}/10, {rnd}R): "
                       f"{content_summary}", tag=tag)
            update_program_board(state.paper_name, "A-DONE",
                                 f"score {final_score}/10, {rnd} rounds")
            state.stage_a_passed = True
            save_state(state)
            return True

        logger.info(f"{tag} Score {final_score} < {SCORE_PASS_THRESHOLD}, "
                    f"looping (round {rnd}/{MAX_STAGE_A_ROUNDS})")

    # Max rounds exhausted — proceed anyway with warning
    best = max(state.stage_a_scores) if state.stage_a_scores else 0
    logger.warning(f"{tag} Max {MAX_STAGE_A_ROUNDS} rounds exhausted, "
                   f"proceeding with best score {best}")
    content_summary = summarize_content_changes(
        paper_path, _stage_a_pre_theorems)
    git_commit(paper_path,
               f"Stage A ({best}/10, {MAX_STAGE_A_ROUNDS}R max): "
               f"{content_summary}", tag=tag)
    update_program_board(state.paper_name, "A-DONE",
                         f"best {best}/10, {MAX_STAGE_A_ROUNDS} rounds (max)")
    state.stage_a_passed = True  # forced pass
    save_state(state)
    return True


# ═══════════════════════════════════════════════════════════════════════════
# STAGE B: Oracle Review (minor-revision-gated loop)
# ═══════════════════════════════════════════════════════════════════════════

def run_stage_b(state: PaperState, *, dry_run: bool = False,
                model: Optional[str] = None,
                oracle_timeout: int = 7200) -> bool:
    tag = f"[{state.paper_name}|B]"
    paper_path = Path(state.paper_dir)

    for rnd in range(state.stage_b_rounds + 1, MAX_STAGE_B_ROUNDS + 1):
        state.stage_b_rounds = rnd
        state.current_round = rnd
        save_state(state)

        # ── B1: Compile PDF ──────────────────────────────────────
        logger.info(f"{tag} Round {rnd}: B1 — Compile PDF")
        pdf = compile_pdf(paper_path, dry_run=dry_run)
        if pdf:
            state.pdf_path = str(pdf)
        git_stage(paper_path, tag=tag)  # B1 intermediate, tag=tag)
        state.log_event("B", "compile_pdf", round_num=rnd,
                        committed=False, commit_hash="")
        save_state(state)

        # ── B2: Oracle editorial review (EVENT WAIT) ─────────────
        # Sanitize paper_name to ASCII for URL safety (中文 in task_id breaks polling)
        safe_name = re.sub(r"[^a-zA-Z0-9_-]", "_", state.paper_name)[:80]
        task_id = f"review_{safe_name}_B{rnd}_{int(time.time())}"
        prompt = (build_oracle_review_prompt(state.target_journal) if rnd == 1
                  else build_oracle_re_review_prompt(state.target_journal))

        logger.info(f"{tag} Round {rnd}: B2 — Oracle review")

        if dry_run:
            response = ("Overall verdict: Major revision\n"
                        "1 | Section 3 | MEDIUM | simulated issue | fix it"
                        if rnd < 2 else "Overall verdict: Minor revision")
        else:
            # Oracle userscript has ≥40% extraction-failure rate historically.
            # Retry until we get a substantive response or exhaust attempts.
            # Failed attempts are archived to oracle/bad/ for debugging but
            # never enter the live done/ pool.
            bad_dir = SCRIPT_DIR / "oracle" / "bad"
            bad_dir.mkdir(parents=True, exist_ok=True)
            response = ""
            for attempt in range(1, 4):
                pdf_path = Path(state.pdf_path) if state.pdf_path else None
                attempt_task = f"{task_id}_a{attempt}"
                logger.info(f"{tag} B2 oracle attempt {attempt}/3 "
                            f"(task={attempt_task})")
                if not oracle_submit(attempt_task, prompt, pdf_path):
                    state.error = "Oracle submit failed"
                    return False
                save_state(state)
                raw = oracle_poll(attempt_task, timeout=oracle_timeout)
                if is_oracle_response_valid(raw):
                    response = raw
                    break
                # Archive the garbage response for audit
                if raw:
                    (bad_dir / f"{attempt_task}.md").write_text(
                        raw, encoding="utf-8")
                logger.warning(f"{tag} Oracle attempt {attempt} returned "
                               f"garbage ({len(raw)} chars), archived to "
                               f"oracle/bad/{attempt_task}.md, retrying")
            if not response:
                state.error = f"Oracle failed B{rnd}: 3 garbage attempts"
                return False

        # Save oracle response (only substantive ones reach done/)
        done_dir = SCRIPT_DIR / "oracle" / "done"
        done_dir.mkdir(parents=True, exist_ok=True)
        (done_dir / f"{task_id}.md").write_text(response, encoding="utf-8")

        # ── B3: Parse verdict ────────────────────────────────────
        verdict = extract_verdict(response)
        issues = parse_oracle_issues(response)
        state.stage_b_verdicts.append(verdict)
        state.log_event("B", "oracle_review", round_num=rnd,
                        verdict=verdict,
                        detail=f"{len(issues)} issues")
        save_state(state)

        logger.info(f"{tag} Round {rnd}: Verdict = {verdict}, "
                    f"{len(issues)} issues")

        # ── Gate: accept or minor revision → Stage C ────────────
        if verdict in ("accept", "minor revision"):
            logger.info(f"{tag} STAGE B PASSED at round {rnd}: {verdict.upper()}")
            git_commit(paper_path,
                       f"Stage B ({verdict}, {rnd}R): "
                       f"Oracle review passed", tag=tag)
            update_program_board(state.paper_name, "B-DONE",
                                 f"Oracle: {verdict}, {rnd} rounds")
            state.stage_b_passed = True
            save_state(state)
            return True

        # ── B4: Codex fix issues ─────────────────────────────────
        logger.info(f"{tag} Round {rnd}: B4 — Codex fix")
        issues_text = format_issues_for_codex(issues)
        fix_prompt = build_codex_fix_from_issues_prompt(
            state.paper_dir, issues_text, rnd)
        codex_exec(fix_prompt, work_dir=paper_path,
                   timeout_seconds=1800, model=model, dry_run=dry_run)
        git_stage(paper_path, tag=tag)  # B4 intermediate issues", tag=tag)
        state.log_event("B", "codex_fix", round_num=rnd,
                        committed=False, commit_hash="")
        save_state(state)

        # ── B5: Claude review fixes (independent second opinion) ──
        logger.info(f"{tag} Round {rnd}: B5 — Claude review fixes")
        claude_fix_prompt = textwrap.dedent(f"""\
            Quality check after fixing oracle-reported issues.
            Paper: {state.paper_dir}
            Target: {state.target_journal}

            The following issues were fixed by Codex:
            {issues_text}

            Read the paper and verify:
            1. Each issue was actually addressed
            2. No revision artifacts were introduced
            3. No existing content was broken
            4. LaTeX compiles cleanly

            If you find remaining problems, fix them directly.
            Compile: cd {state.paper_dir} && xelatex -interaction=nonstopmode main.tex
        """)
        claude_exec(claude_fix_prompt, work_dir=paper_path,
                    dry_run=dry_run)
        git_stage(paper_path, tag=tag)  # B5 intermediate fixes", tag=tag)
        state.log_event("B", "claude_review_fixes", round_num=rnd,
                        committed=False, commit_hash="")
        save_state(state)

        logger.info(f"{tag} Round {rnd}/{MAX_STAGE_B_ROUNDS} complete, "
                    f"looping for re-review")

    last_v = state.stage_b_verdicts[-1] if state.stage_b_verdicts else "?"
    logger.warning(f"{tag} Max {MAX_STAGE_B_ROUNDS} rounds exhausted, "
                   f"proceeding with last verdict: {last_v}")
    git_commit(paper_path,
               f"Stage B ({last_v}, {MAX_STAGE_B_ROUNDS}R max): "
               f"Oracle fixes applied", tag=tag)
    update_program_board(state.paper_name, "B-DONE",
                         f"Oracle: {last_v}, {MAX_STAGE_B_ROUNDS} rounds (max)")
    state.stage_b_passed = True
    save_state(state)
    return True


# ═══════════════════════════════════════════════════════════════════════════
# STAGE C: Claude Independent Review (approval-gated loop)
# ═══════════════════════════════════════════════════════════════════════════

def run_stage_c(state: PaperState, *, dry_run: bool = False,
                model: Optional[str] = None) -> bool:
    tag = f"[{state.paper_name}|C]"
    paper_path = Path(state.paper_dir)

    for rnd in range(state.stage_c_rounds + 1, MAX_STAGE_C_ROUNDS + 1):
        state.stage_c_rounds = rnd
        state.current_round = rnd
        save_state(state)

        # ── C1: Claude independent review ────────────────────────
        logger.info(f"{tag} Round {rnd}: C1 — Claude independent review")
        review_prompt = build_claude_independent_review_prompt(
            state.paper_dir, state.target_journal)
        out_c1 = claude_exec(review_prompt, work_dir=paper_path,
                             dry_run=dry_run)
        review_data = parse_json_from_output(out_c1) if not dry_run else {
            "verdict": "revise" if rnd < 2 else "submit",
            "issues": [f"dry run issue R{rnd}"] if rnd < 2 else [],
        }
        verdict = review_data.get("verdict", "revise")
        issues = review_data.get("issues", [])
        state.stage_c_verdicts.append(verdict)
        state.log_event("C", "claude_independent_review", round_num=rnd,
                        verdict=verdict,
                        detail=json.dumps(review_data, ensure_ascii=False)[:10000])
        save_state(state)

        logger.info(f"{tag} Round {rnd}: Claude verdict = {verdict}, "
                    f"{len(issues)} issues")

        # ── Gate: submit → Stage D ───────────────────────────────
        if verdict == "submit" or not issues:
            logger.info(f"{tag} STAGE C PASSED at round {rnd}: READY TO SUBMIT")
            git_commit(paper_path,
                       f"Stage C (submit, {rnd}R): "
                       f"Claude approved for submission", tag=tag)
            update_program_board(state.paper_name, "C-DONE",
                                 f"Claude: submit, {rnd} rounds")
            state.stage_c_passed = True
            save_state(state)
            return True

        # ── C2: Codex fix Claude's issues ────────────────────────
        logger.info(f"{tag} Round {rnd}: C2 — Codex fix Claude issues")
        fix_prompt = build_codex_fix_from_claude_prompt(
            state.paper_dir, issues, rnd)
        codex_exec(fix_prompt, work_dir=paper_path,
                   timeout_seconds=1800, model=model, dry_run=dry_run)
        git_stage(paper_path, tag=tag)  # C2 intermediate claude issues", tag=tag)
        state.log_event("C", "codex_fix_claude", round_num=rnd,
                        committed=False, commit_hash="")
        save_state(state)

        logger.info(f"{tag} Round {rnd}/{MAX_STAGE_C_ROUNDS} complete, "
                    f"looping for re-review")

    logger.warning(f"{tag} Max {MAX_STAGE_C_ROUNDS} rounds exhausted")
    git_commit(paper_path,
               f"Stage C ({MAX_STAGE_C_ROUNDS}R max): "
               f"Claude review exhausted", tag=tag)
    update_program_board(state.paper_name, "C-DONE",
                         f"{MAX_STAGE_C_ROUNDS} rounds (max)")
    state.stage_c_passed = True
    save_state(state)
    return True


# ═══════════════════════════════════════════════════════════════════════════
# STAGE D: Backflow to Main Paper
# ═══════════════════════════════════════════════════════════════════════════

def run_stage_d(state: PaperState, *, dry_run: bool = False,
                model: Optional[str] = None) -> bool:
    tag = f"[{state.paper_name}|D]"
    paper_path = Path(state.paper_dir)
    main_path = Path(state.main_paper_dir) if state.main_paper_dir else None

    if not main_path or not main_path.exists():
        logger.info(f"{tag} No main paper configured — skipping Stage D")
        state.stage_d_passed = True
        save_state(state)
        return True

    # ── D1: Codex checks backflow candidates ─────────────────────
    logger.info(f"{tag} D1 — Codex backflow check")
    prompt_d1 = build_backflow_check_prompt(state.paper_dir,
                                             state.main_paper_dir)
    out_d1 = codex_exec(prompt_d1, work_dir=REPO_ROOT,
                        timeout_seconds=900, model=model, dry_run=dry_run)
    bf_data = parse_json_from_output(out_d1) if not dry_run else {
        "backflow_items": [{"sub_paper_result": "dry run thm",
                            "main_paper_location": "Section 1",
                            "action": "add_reference",
                            "detail": "dry run detail"}],
        "summary": "dry run",
    }
    items = bf_data.get("backflow_items", [])
    state.stage_d_backflow_items = [
        json.dumps(it, ensure_ascii=False) for it in items
    ]
    state.log_event("D", "codex_backflow_check",
                    detail=f"{len(items)} items found")
    save_state(state)

    if not items:
        logger.info(f"{tag} No backflow needed")
        state.stage_d_passed = True
        save_state(state)
        return True

    logger.info(f"{tag} {len(items)} backflow items found")

    # ── D2: Claude reviews backflow proposal ─────────────────────
    logger.info(f"{tag} D2 — Claude review backflow")
    claude_bf_prompt = textwrap.dedent(f"""\
        Review this backflow proposal.
        Sub-paper: {state.paper_dir}
        Main paper: {state.main_paper_dir}

        Proposed changes:
        {json.dumps(items, indent=2, ensure_ascii=False)[:4000]}

        For each item:
        1. Is this change justified?
        2. Will it improve the main paper?
        3. Any risk of breaking existing content?

        Output ONLY:
        ```json
        {{
          "approved": true/false,
          "approved_items": [0, 1, ...],
          "rejected_items": [2, ...],
          "notes": "explanation"
        }}
        ```
    """)
    out_d2 = claude_exec(claude_bf_prompt, work_dir=REPO_ROOT,
                         dry_run=dry_run)
    approval = parse_json_from_output(out_d2) if not dry_run else {
        "approved": True, "approved_items": list(range(len(items))),
    }
    state.log_event("D", "claude_review_backflow",
                    detail=json.dumps(approval, ensure_ascii=False)[:10000])
    save_state(state)

    if not approval.get("approved", False):
        logger.info(f"{tag} Backflow rejected by Claude — skipping")
        state.stage_d_passed = True
        save_state(state)
        return True

    # Filter to approved items only
    approved_idx = set(approval.get("approved_items", range(len(items))))
    approved_items = [it for i, it in enumerate(items) if i in approved_idx]

    # ── D3: Apply backflow to main paper ─────────────────────────
    logger.info(f"{tag} D3 — Apply {len(approved_items)} backflow items")
    apply_prompt = build_backflow_apply_prompt(
        state.paper_dir, state.main_paper_dir, approved_items)
    codex_exec(apply_prompt, work_dir=REPO_ROOT,
               timeout_seconds=1800, model=model, dry_run=dry_run)
    h = git_commit_multi(
        [paper_path, main_path],
        f"stage-D: backflow {len(approved_items)} items to main paper",
        tag=tag)
    state.log_event("D", "apply_backflow",
                    committed=False, commit_hash="")
    save_state(state)

    # ── D4: Claude verification ──────────────────────────────────
    logger.info(f"{tag} D4 — Claude verify main paper")
    verify_prompt = textwrap.dedent(f"""\
        Verify the main paper after backflow changes.
        Main paper: {state.main_paper_dir}

        Check:
        1. New content integrates cleanly with existing text
        2. No duplicate theorems or contradictions
        3. References are correct
        4. LaTeX compiles

        Fix any issues directly. Then compile:
          cd {state.main_paper_dir} && xelatex -interaction=nonstopmode main.tex
    """)
    codex_exec(verify_prompt, work_dir=main_path,
               timeout_seconds=900, model=model, dry_run=dry_run)
    h = git_commit(main_path,
                   f"stage-D: claude verify main paper after backflow",
                   tag=tag)
    state.log_event("D", "claude_verify_main",
                    committed=False, commit_hash="")
    save_state(state)

    # ── D5: Claude quality review of backflow changes ──────────
    logger.info(f"{tag} D5 — Claude review backflow quality")
    d5_prompt = textwrap.dedent(f"""\
        Independent quality review of backflow changes to the main paper.
        Main paper: {state.main_paper_dir}
        Sub-paper source: {state.paper_dir}

        Recent backflow applied {len(approved_items)} items. Review:

        1. Does each backflow item integrate naturally? (no abrupt insertions)
        2. Are new theorems/references mathematically correct?
        3. Is there any broken cross-referencing?
        4. Does the main paper's narrative flow still make sense?
        5. Any content that should NOT have been added?

        ## Output Format (MUST follow exactly)
        ```json
        {{
          "quality_verdict": "<good|needs_fixes>",
          "issues": ["issue1", "issue2", ...],
          "notes": "summary"
        }}
        ```

        quality_verdict = "good" means backflow is clean, no further action.
        quality_verdict = "needs_fixes" means list specific issues to address.
        Do NOT edit files — only output the JSON review.
    """)
    out_d5 = claude_exec(d5_prompt, work_dir=main_path, dry_run=dry_run)
    d5_data = parse_json_from_output(out_d5) if not dry_run else {
        "quality_verdict": "good", "issues": [], "notes": "dry run",
    }
    d5_verdict = d5_data.get("quality_verdict", "good")
    d5_issues = d5_data.get("issues", [])
    state.log_event("D", "claude_review_backflow_quality",
                    verdict=d5_verdict,
                    detail=json.dumps(d5_data, ensure_ascii=False)[:10000])
    save_state(state)

    if d5_verdict == "needs_fixes" and d5_issues:
        logger.info(f"{tag} D5 found {len(d5_issues)} issues — Codex fixing")
        issues_text = "\n".join(f"  {i+1}. {iss}" for i, iss in enumerate(d5_issues))
        fix_prompt = textwrap.dedent(f"""\
            Fix issues found by Claude's quality review of backflow changes.
            Main paper: {state.main_paper_dir}

            ## Issues
            {issues_text}

            Fix each issue directly in the .tex files.
            Compile: cd {state.main_paper_dir} && xelatex -interaction=nonstopmode main.tex
        """)
        codex_exec(fix_prompt, work_dir=main_path,
                   timeout_seconds=900, model=model, dry_run=dry_run)
        h = git_commit(main_path,
                       f"stage-D5: fix {len(d5_issues)} backflow quality issues",
                       tag=tag)
        state.log_event("D", "codex_fix_backflow_quality",
                        committed=False, commit_hash="")
        save_state(state)
        logger.info(f"{tag} D5 fixes applied")
    else:
        logger.info(f"{tag} D5: backflow quality OK")

    state.stage_d_passed = True
    save_state(state)
    logger.info(f"{tag} STAGE D COMPLETE")
    return True


# ═══════════════════════════════════════════════════════════════════════════
# NEW-PAPER PIPELINE (N1 → N2 → N3 → auto-enters Review A→B→C→D)
# ═══════════════════════════════════════════════════════════════════════════

def build_new_research_prompt(topic: str, outline: str,
                               target_journal: str,
                               main_paper_dir: str = "") -> str:
    """N1: Deep original research grounded in the main paper.

    Reads the main paper (theory/2026_golden_ratio_...) to find
    existing results that connect to the new topic, then extends
    them into a new coherent paper.
    """
    outline_section = f"\n## Outline / Notes\n{outline}\n" if outline else ""

    main_paper_section = ""
    if main_paper_dir:
        main_paper_section = textwrap.dedent(f"""

        ## Source: Main Paper
        The main paper is at: {main_paper_dir}

        READ the main paper's .tex files thoroughly. Your new paper must:
        1. Build on existing results from the main paper — cite them, extend them,
           derive consequences, or apply them to new settings
        2. NOT duplicate content that already exists in the main paper
        3. Be self-contained (reader shouldn't need the main paper to understand)
        4. Identify which main-paper theorems/definitions are prerequisites and
           state them as "imported results" in your preliminaries section

        The goal is to produce a paper that EXTENDS the main paper's framework
        into the direction specified by the topic below, discovering genuinely
        new results along the way.
        """)

    return textwrap.dedent(f"""\
        You are a mathematical researcher preparing a paper for "{target_journal}".

        ## Topic
        {topic}
        {outline_section}{main_paper_section}
        ## Task: Deep Original Research

        Conduct deep research on this topic. Produce:
        1. Precise definitions and notation
        2. Main theorems with complete, rigorous proofs
        3. Supporting lemmas as needed
        4. Connections to existing literature (cite properly)

        Requirements:
        - Find genuinely striking, publishable conclusions that extend the
          framework. Push until you reach results with real publication value
          — do not produce incremental filler.
        - Do NOT reproduce reasoning already published by others or already
          in the main paper. You MAY use existing results as building blocks
          — cite them properly.
        - Do NOT include intermediate-process conclusions; only final results.
        - Use rigorous academic language. No colloquialisms.
        - Add all references to references.bib.

        Write your results as .tex content. Create/edit files in the paper directory.
    """)


def build_scaffold_prompt(paper_dir: str, target_journal: str) -> str:
    """N2: Assemble paper skeleton from research output."""
    return textwrap.dedent(f"""\
        You are assembling a paper for "{target_journal}" from research notes.
        Paper directory: {paper_dir}

        ## Task: Create Complete Paper Structure

        Read all existing .tex files and research output. Create a complete paper:

        1. main.tex — master file with \\documentclass, \\input for each section
        2. sections/ — one .tex file per section:
           - introduction.tex (motivation, context, contribution summary)
           - preliminaries.tex (definitions, notation, background)
           - main_results.tex (theorems + proofs, logical order)
           - discussion.tex (implications, connections, open questions)
        3. references.bib — complete bibliography
        4. Any appendices if content warrants it

        Match "{target_journal}" structure conventions:
        - Abstract (150-250 words, precise contribution claims)
        - MSC codes and keywords
        - Proper theorem environments (theorem, lemma, proposition, corollary)

        Compile when done:
          cd {paper_dir} && xelatex -interaction=nonstopmode main.tex
    """)


def build_initial_style_prompt(paper_dir: str, target_journal: str) -> str:
    """N3: Write the complete paper in journal style."""
    return textwrap.dedent(f"""\
        You are a senior author publishing in "{target_journal}".
        Paper directory: {paper_dir}

        ## Task: Write Complete Journal-Quality Paper

        The paper structure and results are in place. Now write the FULL paper
        as a polished submission to "{target_journal}".

        Study recent papers in "{target_journal}" and match:
        - Writing style, word choice, transitions, hedging patterns
        - Introduction framing (problem → context → gap → our contribution)
        - Theorem-proof flow and formatting
        - Body vs. appendix ratio
        - Abstract density and precision
        - Citation density and style

        The result should read as natural expert writing, NOT AI-generated text.
        Vary sentence length. Use the phrasings human authors actually use.

        Edit all .tex files directly. Compile:
          cd {paper_dir} && xelatex -interaction=nonstopmode main.tex

        No revision artifacts. Write as if this is the original submission.
    """)


def build_journal_selection_prompt(topic: str, outline: str) -> str:
    """N0: Select the best-fit journal based on topic/outline content."""
    outline_section = f"\n## Outline / Notes\n{outline[:3000]}\n" if outline else ""
    return textwrap.dedent(f"""\
        You are a senior mathematician advising on journal selection.

        ## Research Topic
        {topic}
        {outline_section}
        ## Task: Select the Best Target Journal

        Based on this topic and any notes provided, recommend the single
        best-fit journal for submission. Consider:

        1. Subject area — which journal's scope most precisely matches?
        2. Depth expectation — flagship vs specialized vs letters
        3. Typical acceptance rate and turnaround
        4. Recent publications on similar topics

        ## Output Format (MUST follow exactly)
        ```json
        {{
          "recommended_journal": "Full Journal Name",
          "fit_score": <1-10>,
          "rationale": "2-3 sentences explaining why",
          "alternatives": [
            {{"name": "Journal 2", "fit_score": <1-10>, "reason": "..."}},
            {{"name": "Journal 3", "fit_score": <1-10>, "reason": "..."}}
          ]
        }}
        ```

        Do NOT edit any files — only output the JSON.
    """)


def run_new_paper_pipeline(
    topic: str,
    *,
    outline: str = "",
    paper_name: str = "",
    target_journal: str = "",
    main_paper_dir: str = "",
    dry_run: bool = False,
    model: Optional[str] = None,
    oracle_timeout: int = 7200,
) -> tuple[bool, PaperState]:
    """Create a new paper from scratch, then auto-enter the review pipeline.

    Flow: N0 (journal selection) → N1 (research) → N2 (scaffold) → N3 (style)
          → auto-enter Review pipeline (F → A → B → C → D)
    """

    # Generate paper directory name
    if not paper_name:
        safe_topic = re.sub(r"[^a-zA-Z0-9]+", "_", topic.lower())[:60].strip("_")
        paper_name = f"2026_{safe_topic}"
    paper_path = THEORY_DIR / paper_name
    paper_path.mkdir(parents=True, exist_ok=True)

    state = PaperState(
        paper_dir=str(paper_path),
        paper_name=paper_name,
        target_journal=target_journal or "(pending N0 selection)",
        current_stage="N",
        started_at=datetime.now().isoformat(),
    )
    if main_paper_dir:
        mp = Path(main_paper_dir)
        if not mp.is_absolute():
            mp = REPO_ROOT / mp
        state.main_paper_dir = str(mp)

    tag = f"[{paper_name}|NEW]"
    logger.info(f"{'='*60}")
    logger.info(f"{tag} New paper pipeline")
    logger.info(f"{tag} Topic: {topic}")
    logger.info(f"{tag} Dir: {paper_path}")
    logger.info(f"{'='*60}")

    # ── N0: Journal selection (if not pre-specified) ─────────────
    if not target_journal:
        logger.info(f"{tag} N0 — Codex journal selection")
        prompt_n0 = build_journal_selection_prompt(topic, outline)
        out_n0 = codex_exec(prompt_n0, work_dir=paper_path,
                            timeout_seconds=600, model=model, dry_run=dry_run)
        j_data = parse_json_from_output(out_n0) if not dry_run else {
            "recommended_journal": "Ergodic Theory and Dynamical Systems",
            "fit_score": 9,
            "rationale": "dry run: topic matches ETDS scope",
            "alternatives": [
                {"name": "Advances in Mathematics", "fit_score": 6,
                 "reason": "broader scope"},
            ],
        }
        selected = j_data.get("recommended_journal", "Advances in Mathematics")
        state.target_journal = selected
        state.log_event("N", "codex_journal_selection",
                        score=j_data.get("fit_score", 0),
                        detail=json.dumps(j_data, ensure_ascii=False)[:10000])
        save_state(state)
        logger.info(f"{tag} N0 selected journal: {selected} "
                    f"(fit={j_data.get('fit_score', '?')})")
    else:
        logger.info(f"{tag} Journal pre-specified: {target_journal}")
        state.target_journal = target_journal

    journal = state.target_journal

    # ── NS: Claude scope definition ─────────────────────────────
    # Claude reads main paper + topic/outline, defines precise scope:
    # what to include, what to exclude, how to cut from main paper,
    # what existing results to build on, target contribution.
    logger.info(f"{tag} NS — Claude scope definition")
    scope_prompt = textwrap.dedent(f"""\
        You are defining the precise scope for a new mathematical paper.

        ## New idea / topic
        {topic}

        {"## Notes / outline" + chr(10) + outline if outline else ""}

        ## Target journal
        {journal}

        ## Main paper (read ALL .tex files)
        {state.main_paper_dir}

        ## Task: Define Paper Scope

        Read the main paper thoroughly. Then define the scope for this new
        paper by answering each question precisely:

        1. **Core contribution**: What is the ONE central new result this
           paper will prove? State it as a precise theorem statement.

        2. **Imported results**: Which existing theorems/definitions from
           the main paper are prerequisites? List them by label/name.

        3. **Scope boundary — INCLUDE**: What sections/topics belong in
           this paper? Be specific (e.g., "Sections 3.1-3.4 of the main
           paper's folding chapter, extended with new convergence results").

        4. **Scope boundary — EXCLUDE**: What must NOT be in this paper?
           (e.g., "All zeta-function material", "Physical applications",
           "Anything from the logic expansion chain").

        5. **Cut strategy**: How does this paper relate to the main paper?
           - Extract + extend (take existing material, add new results)
           - New direction (minimal overlap, new theorems grounded in main paper's definitions)
           - Bridge (connect two existing parts of the main paper)

        6. **Target length**: Estimate page count appropriate for {journal}.

        7. **Key differentiation**: In one sentence, why would a referee
           at {journal} accept this over existing literature?

        ## Output Format (MUST follow exactly)
        ```json
        {{
          "core_theorem": "precise statement of the main new result",
          "imported_results": ["thm:xxx", "def:yyy", ...],
          "include_topics": ["topic1", "topic2", ...],
          "exclude_topics": ["topic1", "topic2", ...],
          "cut_strategy": "extract_extend|new_direction|bridge",
          "target_pages": <number>,
          "differentiation": "one sentence",
          "suggested_title": "paper title"
        }}
        ```
    """)
    scope_out = claude_exec(scope_prompt, work_dir=Path(state.main_paper_dir)
                            if state.main_paper_dir else paper_path,
                            dry_run=dry_run)
    scope_data = parse_json_from_output(scope_out) if not dry_run else {
        "core_theorem": "dry run theorem",
        "imported_results": [],
        "include_topics": ["dry run topic"],
        "exclude_topics": [],
        "cut_strategy": "new_direction",
        "target_pages": 25,
        "differentiation": "dry run",
        "suggested_title": f"On {topic}",
    }
    state.log_event("N", "claude_scope_definition",
                    detail=json.dumps(scope_data, ensure_ascii=False)[:10000])
    save_state(state)

    # Pass scope constraints to N1
    scope_constraints = json.dumps(scope_data, indent=2, ensure_ascii=False)[:5000]
    logger.info(f"{tag} NS scope: {scope_data.get('cut_strategy', '?')}, "
                f"~{scope_data.get('target_pages', '?')} pages, "
                f"core: {str(scope_data.get('core_theorem', ''))[:80]}")

    # ── N1: Deep research (guided by Claude's scope) ─────────────
    logger.info(f"{tag} N1 — Codex deep research (for {journal})")
    prompt_n1 = build_new_research_prompt(topic, outline, journal,
                                          main_paper_dir=state.main_paper_dir)
    # Append Claude's scope constraints to guide codex
    prompt_n1 += f"\n\n## Scope (defined by independent Claude review)\n{scope_constraints}\n"
    codex_exec(prompt_n1, work_dir=paper_path,
               timeout_seconds=3600, model=model, dry_run=dry_run)
    git_stage(paper_path, tag=tag)  # N1 intermediate
    h = ""  #
    state.log_event("N", "codex_deep_research",
                    committed=False, commit_hash="")
    save_state(state)

    # ── N2: Scaffold ─────────────────────────────────────────────
    logger.info(f"{tag} N2 — Codex scaffold (for {journal})")
    prompt_n2 = build_scaffold_prompt(str(paper_path), journal)
    codex_exec(prompt_n2, work_dir=paper_path,
               timeout_seconds=1800, model=model, dry_run=dry_run)
    git_stage(paper_path, tag=tag)  # N2 intermediate
    h = ""
    state.log_event("N", "codex_scaffold",
                    committed=False, commit_hash="")
    save_state(state)

    # ── N3: Initial journal style ────────────────────────────────
    logger.info(f"{tag} N3 — Codex initial journal style (for {journal})")
    prompt_n3 = build_initial_style_prompt(str(paper_path), journal)
    codex_exec(prompt_n3, work_dir=paper_path,
               timeout_seconds=2400, model=model, dry_run=dry_run)
    h = git_commit(paper_path, f"new-paper: {topic[:40]} (research+scaffold+style)", tag=tag)
    state.log_event("N", "codex_initial_style",
                    committed=False, commit_hash="")
    save_state(state)

    logger.info(f"{tag} New-paper pipeline complete → entering Review pipeline")

    # Auto-enter review pipeline at Stage F (fit validation)
    state.current_stage = "F"
    save_state(state)
    return run_paper_pipeline(
        str(paper_path),
        target_journal=journal,
        main_paper_dir=main_paper_dir,
        dry_run=dry_run,
        model=model,
        oracle_timeout=oracle_timeout,
    )


# ═══════════════════════════════════════════════════════════════════════════
# Main pipeline runner (Review: A → B → C → D)
# ═══════════════════════════════════════════════════════════════════════════

STAGE_ORDER = ["F", "A", "B", "C", "D", "DONE"]
STAGE_RUNNERS = {
    "F": run_stage_f,
    "A": run_stage_a,
    "B": run_stage_b,
    "C": run_stage_c,
    "D": run_stage_d,
}


def run_paper_pipeline(
    paper_dir: str,
    *,
    target_journal: str = "Advances in Mathematics",
    main_paper_dir: str = "",
    skip_to: str = "",
    dry_run: bool = False,
    model: Optional[str] = None,
    oracle_timeout: int = 7200,
) -> tuple[bool, PaperState]:
    paper_path = Path(paper_dir)
    if not paper_path.is_absolute():
        paper_path = REPO_ROOT / paper_path
    paper_name = paper_path.name

    state = load_state(paper_name)
    if state is None:
        state = PaperState(
            paper_dir=str(paper_path),
            paper_name=paper_name,
            started_at=datetime.now().isoformat(),
        )

    # Recover round counters from git log if state was reset or started fresh.
    # Prevents redoing Codex/Oracle work already committed in prior sessions.
    rebuild_rounds_from_git(state)

    # Auto-detect target journal: paper metadata > CLI arg > default
    detected = detect_target_journal(str(paper_path))
    if detected:
        state.target_journal = detected
        logger.info(f"[{paper_name}] Auto-detected journal: {detected}")
    else:
        state.target_journal = target_journal
    if main_paper_dir:
        mp = Path(main_paper_dir)
        if not mp.is_absolute():
            mp = REPO_ROOT / mp
        state.main_paper_dir = str(mp)

    if skip_to and skip_to in STAGE_ORDER:
        state.current_stage = skip_to

    tag = f"[{paper_name}]"
    logger.info(f"{'='*60}")
    logger.info(f"{tag} Pipeline start — Stage {state.current_stage}")
    logger.info(f"{tag} Journal: {target_journal}")
    logger.info(f"{tag} Main paper: {state.main_paper_dir or '(none)'}")
    logger.info(f"{'='*60}")

    while state.current_stage != "DONE":
        stage = state.current_stage
        runner = STAGE_RUNNERS.get(stage)
        if not runner:
            break

        logger.info(f"{tag} === STAGE {stage} ===")
        try:
            kwargs = dict(dry_run=dry_run, model=model)
            if stage == "B":
                kwargs["oracle_timeout"] = oracle_timeout
            ok = runner(state, **kwargs)
        except Exception as exc:
            state.error = f"Stage {stage}: {exc}"
            logger.error(f"{tag} {state.error}", exc_info=True)
            save_state(state)
            return False, state

        if not ok:
            logger.error(f"{tag} Stage {stage} failed: {state.error}")
            save_state(state)
            return False, state

        # Advance to next stage
        idx = STAGE_ORDER.index(stage)
        state.current_stage = STAGE_ORDER[idx + 1]
        save_state(state)

    state.completed_at = datetime.now().isoformat()
    save_state(state)
    total = state.stage_a_rounds + state.stage_b_rounds + state.stage_c_rounds
    logger.info(f"{tag} PIPELINE COMPLETE — total {total} rounds "
                f"(A={state.stage_a_rounds}, B={state.stage_b_rounds}, "
                f"C={state.stage_c_rounds})")
    return True, state


# ---------------------------------------------------------------------------
# Rolling parallel dispatcher
# ---------------------------------------------------------------------------

PAPERS_PUB_DIR = PAPERS_PUB_DIR_CONST


def discover_papers(paper_dirs: Optional[list[str]] = None,
                    *, respect_assignment: bool = True) -> list[str]:
    """Discover papers to process.

    Filtering chain (all must pass):
      1. PROGRAM_BOARD.md status — skip 已投/已发表/骨架/待分诊
      2. PROGRAM_BOARD.md registration — skip unregistered (warn)
      3. Machine assignment — only this machine's papers (if respect_assignment)
    """
    if paper_dirs:
        return paper_dirs

    board = _get_board_entries()
    my_papers = get_my_papers() if respect_assignment else []
    papers = []
    skipped_status = []
    skipped_unreg = []

    for base in (PAPERS_PUB_DIR, THEORY_DIR):
        if base.exists():
            for d in sorted(base.iterdir()):
                if not d.is_dir() or not (d / "main.tex").exists():
                    continue

                # 1. Board status filter
                entry = board.get(d.name)
                if entry and _board_skip(entry["status"]):
                    skipped_status.append(
                        f"  {d.name}: {entry['status']}")
                    continue

                # 2. Board registration filter
                if board and entry is None:
                    skipped_unreg.append(d.name)
                    continue

                # 3. Machine assignment filter
                if my_papers and d.name not in my_papers:
                    continue

                papers.append(str(d))

    if skipped_status:
        logger.info(f"Board status filter skipped {len(skipped_status)} papers:\n"
                    + "\n".join(skipped_status))
    if skipped_unreg:
        logger.warning(
            f"Unregistered in PROGRAM_BOARD.md (skipped, add row to process):\n"
            + "\n".join(f"  {n}" for n in skipped_unreg))
    if my_papers:
        logger.info(f"Machine filter ({sys.platform}): "
                    f"{len(papers)} papers to process")
    return papers


def _auto_parallel() -> int:
    """Auto-detect optimal parallelism based on system resources.

    Strategy: Oracle wait is I/O-bound (HTTP poll), Codex/Claude is CPU-bound.
    We want enough workers so that Oracle-blocked threads don't idle the CPU.

    Rule of thumb:
      - CPU cores / 2 for Codex compute headroom
      - +2 for Oracle I/O overlap (browser can only do 1 at a time, but
        we queue multiple and poll concurrently)
      - Cap at 6 to avoid git contention and memory pressure
      - Min 2 (always want at least some overlap)
    """
    try:
        cores = os.cpu_count() or 4
    except Exception:
        cores = 4
    computed = max(2, min(6, cores // 2 + 2))
    return computed


# Track how many workers are currently blocked on Oracle I/O
_oracle_wait_count = 0
_oracle_wait_lock = threading.Lock()


def oracle_wait_enter():
    global _oracle_wait_count
    with _oracle_wait_lock:
        _oracle_wait_count += 1


def oracle_wait_exit():
    global _oracle_wait_count
    with _oracle_wait_lock:
        _oracle_wait_count = max(0, _oracle_wait_count - 1)


def get_oracle_wait_count() -> int:
    with _oracle_wait_lock:
        return _oracle_wait_count


def run_rolling(paper_dirs: list[str], *, parallel: int = 0,
                continuous: bool = False, **kwargs) -> tuple[int, int]:
    """Rolling pipeline with adaptive concurrency.

    parallel=0 (default): auto-detect from CPU cores
    parallel=N: use exactly N workers

    When workers block on Oracle I/O, the pool still has capacity for
    other papers to do Codex/Claude compute work. The pool size is set
    high enough to keep CPUs busy even when multiple workers are polling.
    """
    if parallel <= 0:
        parallel = _auto_parallel()

    succeeded = failed = 0
    queue = list(paper_dirs)

    logger.info(f"Rolling pipeline: {len(queue)} papers, {parallel} workers "
                f"(auto={parallel == _auto_parallel()})")

    with ThreadPoolExecutor(max_workers=parallel,
                            thread_name_prefix="paper") as pool:
        futures: dict[Future, str] = {}

        def _submit():
            if not queue:
                return
            d = queue.pop(0)
            fut = pool.submit(run_paper_pipeline, d, **kwargs)
            futures[fut] = d
            logger.info(f"Dispatched: {Path(d).name} "
                        f"(active={len(futures)}, oracle_wait={get_oracle_wait_count()}, "
                        f"queue={len(queue)})")

        for _ in range(min(parallel, len(queue))):
            _submit()

        while futures:
            done, _ = wait(futures, return_when=FIRST_COMPLETED)
            for fut in done:
                d = futures.pop(fut)
                name = Path(d).name
                try:
                    ok, st = fut.result()
                    if ok:
                        succeeded += 1
                        total = st.stage_a_rounds + st.stage_b_rounds + st.stage_c_rounds
                        logger.info(f"[{name}] SUCCESS — {total} total rounds")
                    else:
                        failed += 1
                        logger.warning(f"[{name}] FAILED — {st.error}")
                except Exception as exc:
                    failed += 1
                    logger.error(f"[{name}] EXCEPTION: {exc}")

                # Push after each paper completes
                with _git_lock:
                    push = run_cmd(["git", "push", "origin",
                                    "dev-automation-integration"], timeout=60)
                    if push.returncode == 0:
                        logger.info(f"Git push OK after {name}")
                    else:
                        logger.warning(f"Git push failed after {name}")

                _submit()

    return succeeded, failed


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _print(msg: str):
    """Windows-safe print (handles Chinese chars in cp1252 console)."""
    if IS_WINDOWS:
        sys.stdout.buffer.write((msg + "\n").encode("utf-8", errors="replace"))
        sys.stdout.buffer.flush()
    else:
        print(msg)

def print_dashboard():
    """Compact one-line-per-paper table showing pipeline progress.

    Columns: paper | stage | F | A(rounds,last-score) | B(rounds,verdict) |
             C(rounds,verdict) | journal | error
    Designed for a 180-char wide terminal; falls back gracefully if narrower.
    """
    _print("Oracle Pipeline Dashboard  "
           f"({datetime.now().strftime('%Y-%m-%d %H:%M')})")
    _print(f"Platform={sys.platform}  Oracle={'UP' if oracle_server_alive() else 'DOWN'}")
    _print("")
    header = (f"{'paper':<55}  {'stage':<6}  {'F':>4}  "
              f"{'A':<14}  {'B':<16}  {'C':<10}  {'journal':<36}")
    _print(header)
    _print("-" * len(header))
    if not STATE_DIR.exists():
        _print("(no pipeline_state/)")
        return
    rows: list[tuple] = []
    for f in sorted(STATE_DIR.glob("*.json")):
        try:
            with open(f, "r", encoding="utf-8") as fh:
                d = json.load(fh)
        except Exception:
            continue
        rows.append((
            d.get("paper_name", f.stem)[:55],
            d.get("current_stage", "?"),
            str(d.get("stage_f_fit_score", "?")),
            f"{d.get('stage_a_rounds', 0)}r "
            f"last={d.get('stage_a_scores', [0])[-1] if d.get('stage_a_scores') else '-'}",
            f"{d.get('stage_b_rounds', 0)}r "
            f"{(d.get('stage_b_verdicts', ['-'])[-1] if d.get('stage_b_verdicts') else '-')[:10]}",
            f"{d.get('stage_c_rounds', 0)}r "
            f"{(d.get('stage_c_verdicts', ['-'])[-1] if d.get('stage_c_verdicts') else '-')[:5]}",
            (d.get("target_journal", "?") or "?")[:36],
        ))
    for row in rows:
        _print(f"{row[0]:<55}  {row[1]:<6}  {row[2]:>4}  "
               f"{row[3]:<14}  {row[4]:<16}  {row[5]:<10}  {row[6]:<36}")
    _print("")
    _print(f"Total: {len(rows)} papers tracked")


def print_review_index():
    """Correlate Oracle review files with the commit that fixed each review.

    For every oracle/done/*.md file, find the next Stage B commit touching
    the corresponding paper directory and print a single linking row.
    Helps audit whether Oracle suggestions actually land in the tree.
    """
    done_dir = SCRIPT_DIR / "oracle" / "done"
    pub_done_dir = PAPERS_PUB_DIR_CONST / "oracle" / "done"
    review_files: list[Path] = []
    for d in (done_dir, pub_done_dir):
        if d.exists():
            review_files.extend(sorted(d.glob("*.md")))
    _print(f"Oracle Review → Fix Index  ({len(review_files)} reviews)")
    _print(f"{'='*80}")
    if not review_files:
        _print("(no reviews found)")
        return

    for rf in review_files:
        try:
            text = rf.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        # Parse timestamp from oracle metadata
        ts_match = re.search(
            r'"timestamp":\s*"([^"]+)"', text[:500])
        model_match = re.search(r'"model":\s*"([^"]+)"', text[:500])
        timestamp = ts_match.group(1) if ts_match else "?"
        model = model_match.group(1) if model_match else "?"

        # Infer paper name from filename
        stem = rf.stem
        paper_key = re.sub(r"_(gate|editorial|review|R\d+|v\d+).*$", "", stem)

        # Find matching stage-B commit touching any file mentioning paper_key
        try:
            with _git_lock:
                after_iso = timestamp.split("T")[0] if "T" in timestamp else "2020-01-01"
                result = subprocess.run(
                    ["git", "log", "--all", "--format=%h %ci %s",
                     f"--since={after_iso}",
                     "--grep", f"stage-B",
                     "-n", "20"],
                    cwd=str(REPO_ROOT), capture_output=True, text=True,
                    timeout=10,
                )
        except Exception:
            result = None
        commit_hash = "-"
        commit_subj = "(no matching fix commit found)"
        if result and result.returncode == 0:
            for line in result.stdout.splitlines():
                if paper_key.lower()[:20] in line.lower():
                    parts = line.split(maxsplit=3)
                    if len(parts) >= 4:
                        commit_hash = parts[0]
                        commit_subj = parts[3][:60]
                        break

        verdict = extract_verdict(text)
        size = len(text)
        valid = "OK " if is_oracle_response_valid(text) else "BAD"
        _print(f"{rf.name[:40]:<40}  {valid}  {size:>6}B  "
               f"{verdict[:15]:<15}  {model[:18]:<18}")
        if valid == "OK ":
            _print(f"    → fix commit: {commit_hash}  {commit_subj}")
    _print("")


def print_status():
    _print(f"Oracle Pipeline v2 — Status")
    _print(f"{'='*60}")
    _print(f"Platform:      {sys.platform}")
    _print(f"Oracle server: {'UP' if oracle_server_alive() else 'DOWN'}")
    _print(f"Codex CLI:     {CODEX_PATH}")
    _print(f"Claude CLI:    {CLAUDE_PATH}")
    my = get_my_papers()
    _print(f"My papers:     {len(my)} assigned to {sys.platform}")
    _print("")
    if not STATE_DIR.exists():
        _print("No pipeline state found.")
        return
    for f in sorted(STATE_DIR.glob("*.json")):
        try:
            with open(f, "r", encoding="utf-8") as fh:
                d = json.load(fh)
        except Exception:
            continue
        name = d.get("paper_name", f.stem)
        stage = d.get("current_stage", "?")
        a_r = d.get("stage_a_rounds", 0)
        b_r = d.get("stage_b_rounds", 0)
        c_r = d.get("stage_c_rounds", 0)
        total = a_r + b_r + c_r
        a_scores = d.get("stage_a_scores", [])
        b_verd = d.get("stage_b_verdicts", [])
        c_verd = d.get("stage_c_verdicts", [])
        err = d.get("error", "")

        f_fit = d.get("stage_f_fit_score", 0)
        f_orig = d.get("stage_f_original_journal", "")
        f_sugg = d.get("stage_f_suggested_journal", "")
        journal = d.get("target_journal", "?")

        status = "DONE" if stage == "DONE" else ("FAILED" if err else f"Stage {stage}")
        _print(f"  {name}")
        _print(f"    Status:  {status}  |  Total rounds: {total}")
        _print(f"    Journal: {journal}"
               + (f" (rerouted from {f_orig})" if f_sugg else ""))
        if f_fit:
            _print(f"    Stage F: fit={f_fit}/10"
                   + (f", suggested={f_sugg}" if f_sugg else ""))
        _print(f"    Stage A: {a_r} rounds, scores={a_scores}")
        _print(f"    Stage B: {b_r} rounds, verdicts={b_verd}")
        _print(f"    Stage C: {c_r} rounds, verdicts={c_verd}")
        if err:
            _print(f"    Error:   {err}")
        _print("")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Oracle Pipeline v2 — new-paper + review automation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
            Two pipelines:
              --new    New paper: N1(research) → N2(scaffold) → N3(style) → Review
              default  Review:   A(quality+style) → B(oracle) → C(claude) → D(backflow)

            Review stages:
              F  Journal fit check (fit >= 6 to keep target; else auto-reroute)
              A  Codex quality review + journal style (score >= 8 to pass)
              B  Oracle (ChatGPT) review (accept/minor revision to pass)
              C  Claude independent review (submit to pass)
              D  Backflow check to main paper

            Examples:
              # New paper from topic:
              oracle_pipeline.py --new --topic "Folding dynamics" --target-journal "Adv. Math."
              # New paper from outline file:
              oracle_pipeline.py --new --outline notes.md --target-journal "JEMS"
              # Review existing paper:
              oracle_pipeline.py --paper theory/2026_xxx/ --target-journal "Adv. Math."
              # All papers, parallel:
              oracle_pipeline.py --all --parallel 2 --continuous
              # Status:
              oracle_pipeline.py --status
        """),
    )
    # New-paper mode
    parser.add_argument("--new", action="store_true",
                        help="Create a new paper (requires --topic or --outline)")
    parser.add_argument("--topic", type=str, default="",
                        help="Topic for new paper (used with --new)")
    parser.add_argument("--outline", type=str, default="",
                        help="Path to outline/notes file (used with --new)")
    parser.add_argument("--paper-name", type=str, default="",
                        help="Override directory name for new paper")

    # Review mode
    parser.add_argument("--paper", type=str, action="append")
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--target-journal", type=str,
                        default="Advances in Mathematics")
    parser.add_argument("--main-paper", type=str, default="",
                        help="Main paper dir for Stage D backflow")
    parser.add_argument("--parallel", "-p", type=int, default=0,
                        help="Worker count (0=auto-detect from CPU cores)")
    parser.add_argument("--continuous", action="store_true")
    parser.add_argument("--skip-to", type=str, default="",
                        choices=["F", "A", "B", "C", "D"])
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--model", type=str, default=None)
    parser.add_argument("--oracle-timeout", type=int, default=7200)
    parser.add_argument("--status", action="store_true")
    parser.add_argument("--dashboard", action="store_true",
                        help="Compact per-paper progress table")
    parser.add_argument("--review-index", action="store_true",
                        help="Correlate Oracle reviews with fix commits")
    parser.add_argument("--reset", type=str, metavar="PAPER_NAME")
    parser.add_argument("--no-assign", action="store_true",
                        help="Ignore machine assignment, process all papers")
    args = parser.parse_args()

    if args.status:
        print_status()
        return 0

    if args.dashboard:
        print_dashboard()
        return 0

    if args.review_index:
        print_review_index()
        return 0

    if args.reset:
        p = _state_file(args.reset)
        if p.exists():
            p.unlink()
            print(f"Reset: {args.reset}")
        return 0

    # ── New-paper mode ─────────────────────────────────────────
    if args.new:
        topic = args.topic
        outline = ""
        if args.outline:
            outline_path = Path(args.outline)
            if outline_path.exists():
                outline = outline_path.read_text(encoding="utf-8")
            else:
                topic = topic or args.outline  # treat as topic if file not found

        if not topic and not outline:
            print("--new requires --topic or --outline", file=sys.stderr)
            return 1

        if not args.dry_run and not oracle_server_alive():
            logger.warning("Oracle server not running — Stage B will fail")

        ok, st = run_new_paper_pipeline(
            topic=topic or "(from outline)",
            outline=outline,
            paper_name=args.paper_name,
            target_journal=args.target_journal,
            main_paper_dir=args.main_paper,
            dry_run=args.dry_run,
            model=args.model,
            oracle_timeout=args.oracle_timeout,
        )
        return 0 if ok else 1

    # ── Pre-flight: sync with remote ───────────────────────────
    if not args.dry_run:
        logger.info("Pre-flight: git pull origin dev-automation-integration")
        sync = run_cmd(["git", "pull", "--rebase", "origin",
                        "dev-automation-integration"], timeout=60)
        if sync.returncode != 0:
            logger.warning(f"Git pull failed (rc={sync.returncode}), "
                           f"continuing with local state")
        else:
            logger.info("Git sync OK")

    # ── Review mode ────────────────────────────────────────────
    paper_dirs = args.paper or (
        discover_papers(respect_assignment=not args.no_assign) if args.all else None
    )
    if not paper_dirs:
        print("Specify --paper or --all", file=sys.stderr)
        return 1

    if not args.dry_run and not oracle_server_alive():
        logger.warning("Oracle server not running — Stage B will fail")
        logger.warning("Start: python3 tools/chatgpt-oracle/oracle_server.py")

    kwargs = dict(
        target_journal=args.target_journal,
        main_paper_dir=args.main_paper,
        skip_to=args.skip_to,
        dry_run=args.dry_run,
        model=args.model,
        oracle_timeout=args.oracle_timeout,
    )

    if len(paper_dirs) == 1 and args.parallel <= 1:
        ok, st = run_paper_pipeline(paper_dirs[0], **kwargs)
        return 0 if ok else 1

    s, f = run_rolling(paper_dirs, parallel=args.parallel,
                       continuous=args.continuous, **kwargs)
    logger.info(f"Done: {s} succeeded, {f} failed")
    return 0 if s > 0 or args.dry_run else 1


if __name__ == "__main__":
    raise SystemExit(main())
