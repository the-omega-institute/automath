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

  Stage A: Scope-driven theoremization（strict audit-gated loop）
    A0: 固定 scope_contract / research_directive
    A1: 全文 theorem inventory
    A2: 纳入、深化、修补、分流数学内容
    A3: 多轮独立 audit
    Gate: audit metrics pass → Stage B; otherwise STOP at Stage A

  Stage B: Oracle 审稿（minor-revision-gated loop）
    B1: 编译 PDF → commit
    B2: Oracle editorial review → EVENT WAIT
    B3: 解析 verdict
    Gate: verdict ∈ {accept, minor revision} → Stage C
    B4: Codex fix issues → commit
    B5: Claude review fixes → commit
    → B1 (max 4 rounds)

  Stage C: Oracle + Claude 联合终审（approval-gated loop）
    C0: 编译最终候选 PDF
    C1: Oracle final confirmation
    C2: Claude independent review
    Gate: Oracle=accept 且 Claude=submit 且无 issue → Stage D
    C3: Codex fix joint issues → commit
    → C0 (max 4 rounds)

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
import contextlib
import hashlib
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
from urllib.parse import quote

# ---------------------------------------------------------------------------
# Paths & constants
# ---------------------------------------------------------------------------

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
THEORY_DIR = REPO_ROOT / "theory"
LOG_DIR = SCRIPT_DIR / "logs"
STATE_DIR = SCRIPT_DIR / "pipeline_state"
CLAUDE_SUPERVISION_DIR = SCRIPT_DIR / "claude_supervision"
RESEARCH_LEDGER_DIR = SCRIPT_DIR / "research_ledger"
RESEARCH_LEDGER_FILE = RESEARCH_LEDGER_DIR / "research_ledger.jsonl"

ORACLE_SERVER = "http://localhost:8765"
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
        # Renamed to match paper titles (2026-04-20)
        "2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa",
        "2026_homological_visibility_gluing_obstructions_state_forcing_apal",
        "2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal",
        "2026_finite_parts_dynamical_zeta_shifts_finite_type_etds",
        "2026_detector_shells_click_record_kms_jphyscomm",
        "2026_prime_languages_finite_state_obstructions_monatshefte",
        "2026_elliptic_normalization_branch_geometry_quartic_spectral",
        "2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists",
        "2026_finite_observation_escape_rates_cyclotomic_resonances_etds",
        "2026_recursive_addressing_prefix_sites_tac",
        "2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst",
        "2026_coefficient_sup_radial_homotopy_monomial_forms_jdde",
        "2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints",
        "2026_deterministic_telescoping_fold_truncation_defects_dynamical_systems",
        "2026_scan_error_prefix_partitions_convergence_rates_etds",
        "2026_finite_window_zeckendorf_fibers_discrete_thermodynamics_tams",
        "2026_single_primitive_universality_hierarchy",
        "2026_chebotarev_quotient_entropy_fold_groupoid_rigidity",
        "2026_joukowsky_elliptic_godel_lorentz_mahler_capacity",
        "2026_window6_spectral_rigidity_hypercube_lumpability_fold_gauge",
        "2026_zeckendorf_stable_arithmetic_fibonacci_congruence_online",
        "2026_sharp_three_window_threshold_fibonacci_conjugacy_dcds",
        "2026_folded_histograms_sampling_certificates_parry_mismatch_etds",
        "2026_projection_ontological_mathematics_core_tams",
        "2026_scan_projection_address_semantics_sigma_nonexpansion_etds",
        "2026_prefix_scan_error_boundary_rates_dynamical_systems",
    ],
}

def get_my_papers() -> list[str]:
    """Return paper dir names assigned to this machine."""
    return MACHINE_ASSIGNMENT.get(sys.platform, [])

_git_lock = threading.RLock()
_state_lock = threading.Lock()


@contextlib.contextmanager
def git_repo_lock():
    """Serialize git/index operations across pipeline processes."""
    lock_path = LOG_DIR / "git_repo.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with _git_lock:
        with open(lock_path, "a+", encoding="utf-8") as fh:
            if os.name == "posix":
                import fcntl
                fcntl.flock(fh.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                if os.name == "posix":
                    fcntl.flock(fh.fileno(), fcntl.LOCK_UN)

# Stage gate thresholds
SCORE_PASS_THRESHOLD = 8
MIN_STAGE_A_AUDIT_ROUNDS = 2
MAX_STAGE_A_AUDIT_ROUNDS = 4
MAX_STAGE_A_FINAL_REPAIR_ROUNDS = 3
STAGE_A_METRIC_THRESHOLDS = {
    "scope_coverage": 8,
    "theorem_completeness": 8,
    "proof_integrity": 8,
    "depth_novelty": 7,
    "journal_fit": 7,
    "split_hygiene": 8,
}
STAGE_A_CODEX_MATH_METRICS = (
    "theorem_completeness",
    "proof_integrity",
    "depth_novelty",
)
STAGE_A_CLAUDE_STRUCTURAL_METRICS = (
    "scope_coverage",
    "journal_fit",
    "split_hygiene",
)

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
MAX_STAGE_A_ROUNDS = 8
MAX_STAGE_B_ROUNDS = 99  # No practical limit — must pass Oracle gate
MAX_STAGE_C_ROUNDS = 99  # No practical limit — must pass Oracle+Claude gate
DEFAULT_TARGET_JOURNAL = "Advances in Mathematics"
CLAUDE_ENABLED = True
PAUSED_ERROR_PREFIX = "PAUSED:"
ORACLE_CANCELLED_RESPONSE = "__ORACLE_TASK_CANCELLED__"
MAX_STAGE_B_ORACLE_TIMEOUT_ATTEMPTS = 2

# Borrowed from outreach pipeline: escalation & early-skip constants
DEEP_MODE_THRESHOLD = 3   # After N consecutive non-pass B rounds, escalate to deep mode
LOW_SCORE_SKIP = 3        # Skip paper in Stage A if score stays below this
LOW_SCORE_STREAK = 3      # Need this many consecutive low rounds to trigger skip

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
    stage_a_scope_done: bool = False
    stage_a_audit_rounds: int = 0
    stage_a_audit_metrics: dict = field(default_factory=dict)
    stage_a_inventory: dict = field(default_factory=dict)
    stage_a_split_candidates: list[dict] = field(default_factory=list)

    # Stage B tracking
    stage_b_rounds: int = 0
    stage_b_verdicts: list[str] = field(default_factory=list)
    stage_b_passed: bool = False
    stage_b_all_issues: list[str] = field(default_factory=list)  # Accumulated Oracle issues across all rounds

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
            "stage_a_scope_done": self.stage_a_scope_done,
            "stage_a_audit_rounds": self.stage_a_audit_rounds,
            "stage_a_audit_metrics": self.stage_a_audit_metrics,
            "stage_a_inventory": self.stage_a_inventory,
            "stage_a_split_candidates": self.stage_a_split_candidates[-50:],
            "stage_b_rounds": self.stage_b_rounds,
            "stage_b_verdicts": self.stage_b_verdicts,
            "stage_b_passed": self.stage_b_passed,
            "stage_b_all_issues": self.stage_b_all_issues[-200:],  # keep last 200 issue strings
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
                     "stage_a_scope_done", "stage_a_audit_rounds",
                     "stage_b_rounds", "stage_b_passed", "stage_c_rounds",
                     "stage_c_passed", "stage_d_passed", "pdf_path",
                     "started_at", "completed_at", "error"):
            if key in data:
                setattr(s, key, data[key])
        s.stage_a_scores = data.get("stage_a_scores", [])
        s.stage_a_audit_metrics = data.get("stage_a_audit_metrics", {})
        s.stage_a_inventory = data.get("stage_a_inventory", {})
        s.stage_a_split_candidates = data.get("stage_a_split_candidates", [])
        s.stage_b_verdicts = data.get("stage_b_verdicts", [])
        s.stage_b_all_issues = data.get("stage_b_all_issues", [])
        s.stage_c_verdicts = data.get("stage_c_verdicts", [])
        s.stage_d_backflow_items = data.get("stage_d_backflow_items", [])
        s.history = data.get("history", [])
        return s
    except Exception:
        return None


def _state_has_stage_a_evidence(state: PaperState) -> bool:
    if state.stage_a_scores or state.stage_a_audit_metrics or state.stage_a_passed:
        return True
    evidence_actions = {
        "theorem_inventory",
        "theoremization",
        "split_hygiene",
        "audit_blocker_revision",
        "substance_check",
        "cross_paper_dedup_commit",
        "audit_gate_passed",
    }
    return any(
        h.get("stage") == "A" and h.get("action") in evidence_actions
        for h in state.history
        if isinstance(h, dict)
    )


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
        with git_repo_lock():
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

    git_max_a = 0
    max_a = state.stage_a_rounds
    max_b = state.stage_b_rounds
    max_c = state.stage_c_rounds
    for line in result.stdout.splitlines():
        m = re.search(r"stage-A\s+R(\d+)", line, re.IGNORECASE)
        if m:
            git_max_a = max(git_max_a, int(m.group(1)))
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
    if (state.current_stage == "A"
        and not state.stage_a_passed
        and state.stage_a_rounds > git_max_a):
        logger.warning(f"[{state.paper_name}] git-rebuild: rolling back "
                       f"incomplete Stage A round counter "
                       f"{state.stage_a_rounds} → {git_max_a}")
        state.stage_a_rounds = git_max_a
        max_a = git_max_a

    can_rebuild_a = _state_has_stage_a_evidence(state)
    if max_a != state.stage_a_rounds and can_rebuild_a:
        logger.info(f"[{state.paper_name}] git-rebuild: stage_a_rounds "
                    f"{state.stage_a_rounds} → {max_a}")
        state.stage_a_rounds = max_a
    elif max_a != state.stage_a_rounds and not can_rebuild_a:
        logger.info(f"[{state.paper_name}] git-rebuild: ignored Stage A "
                    f"round recovery ({max_a}) because no Stage A score/audit "
                    f"state exists")
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
    "research_directive.md", "scope_contract.md", "scope_contract.json",
    "theorem_inventory.md", "theorem_inventory.json",
    "split_candidates.json", "stage_a_audit.json",
    ".pipeline.stop",
)
_ARTIFACT_DIR_NAMES = {
    "split_material",
    "non_submission_artifacts",
    "oracle_reviews",
    "pipeline_artifacts",
}

_PAPER_SOURCE_SUFFIXES = (".tex", ".bib", ".sty")
_CERTIFICATE_SOURCE_SUFFIXES = (".json", ".py")
_CERTIFICATE_SOURCE_DIRS = {"certificates"}


def _is_paper_source_path(path: Path) -> bool:
    if path.name in set(_ARTIFACT_PATTERNS):
        return False
    if any(part in _ARTIFACT_DIR_NAMES for part in path.parts):
        return False
    if path.suffix in _PAPER_SOURCE_SUFFIXES:
        return True
    return (
        path.suffix in _CERTIFICATE_SOURCE_SUFFIXES
        and any(part in _CERTIFICATE_SOURCE_DIRS for part in path.parts)
    )


def _paper_source_files(paper_path: Path) -> list[str]:
    """Return repo-relative paper source paths, including tracked deletions."""
    files: set[str] = set()
    for ext in ("*.tex", "**/*.tex", "*.bib", "**/*.bib", "*.sty",
                "certificates/*.json", "certificates/*.py"):
        for f in paper_path.glob(ext):
            if _is_paper_source_path(f):
                try:
                    files.add(str(f.relative_to(REPO_ROOT)))
                except ValueError:
                    files.add(str(f))

    deleted = run_cmd(["git", "ls-files", "-d", "--", str(paper_path)])
    for raw in deleted.stdout.splitlines():
        p = Path(raw.strip())
        if _is_paper_source_path(p):
            files.add(str(p))
    return sorted(files)


def _staged_paper_source_files(path: Path) -> list[str]:
    result = run_cmd(["git", "diff", "--cached", "--name-only", "--",
                      str(path)])
    files = []
    for raw in result.stdout.splitlines():
        p = Path(raw.strip())
        if _is_paper_source_path(p):
            files.append(str(p))
    return sorted(set(files))


def _snapshot_paper_sources(paper_path: Path) -> dict[str, bytes | None]:
    """Snapshot current paper source bytes before an agent edit attempt."""
    snapshot: dict[str, bytes | None] = {}
    for raw in _paper_source_files(paper_path):
        p = Path(raw)
        if not p.is_absolute():
            p = REPO_ROOT / p
        if not _is_paper_source_path(p):
            continue
        try:
            snapshot[str(p)] = p.read_bytes() if p.exists() else None
        except Exception:
            snapshot[str(p)] = None
    return snapshot


def _restore_paper_sources_snapshot(
    paper_path: Path, snapshot: dict[str, bytes | None]
) -> None:
    """Restore source snapshot and remove new source files from failed edits."""
    expected = set(snapshot)
    for raw in _paper_source_files(paper_path):
        p = Path(raw)
        if not p.is_absolute():
            p = REPO_ROOT / p
        if str(p) in expected or not _is_paper_source_path(p):
            continue
        try:
            if p.exists():
                p.unlink()
        except Exception as exc:
            logger.warning(f"Failed to remove failed-edit file {p}: {exc}")
    for raw, data in snapshot.items():
        p = Path(raw)
        try:
            if data is None:
                if p.exists():
                    p.unlink()
            else:
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_bytes(data)
        except Exception as exc:
            logger.warning(f"Failed to restore failed-edit snapshot {p}: {exc}")


def _add_paper_only(paper_path: Path) -> None:
    """git add only submission source files under paper_path."""
    files = _paper_source_files(paper_path)
    if files:
        run_cmd(["git", "add", "--"] + files)


def _restore_tracked_non_source_changes(path: Path, *, tag: str = "") -> None:
    """Discard tracked non-paper-source side effects under a paper directory."""
    changed: set[str] = set()
    for args in (["git", "diff", "--name-only", "--", str(path)],
                 ["git", "diff", "--cached", "--name-only", "--", str(path)]):
        result = run_cmd(args)
        for raw in result.stdout.splitlines():
            rel = raw.strip()
            if not rel:
                continue
            p = REPO_ROOT / rel
            if not _is_paper_source_path(p):
                changed.add(rel)
    if not changed:
        return
    files = sorted(changed)
    run_cmd(["git", "restore", "--staged", "--"] + files)
    run_cmd(["git", "restore", "--"] + files)
    logger.warning(f"{tag} Restored tracked non-source side effects: "
                   + ", ".join(files[:8]))


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


def _commit_message(*parts: str) -> str:
    body = [p for p in parts if p]
    if CLAUDE_ENABLED:
        body.append("Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>")
    return "\n\n".join(body)


def git_stage(paper_path: Path, *, tag: str = "") -> bool:
    """Stage submission source changes under paper_path."""
    with git_repo_lock():
        _restore_tracked_non_source_changes(paper_path, tag=tag)
        _add_paper_only(paper_path)
        staged = run_cmd(["git", "diff", "--cached", "--name-only",
                          str(paper_path)])
        return bool(staged.stdout.strip())


def git_commit(paper_path: Path, msg: str, *, tag: str = "") -> str:
    """Commit submission source changes under paper_path. Thread-safe.

    Commit message includes a diff summary showing what actually changed.
    """
    with git_repo_lock():
        _restore_tracked_non_source_changes(paper_path, tag=tag)
        _add_paper_only(paper_path)
        staged_files = _staged_paper_source_files(paper_path)
        if not staged_files:
            logger.info(f"{tag} No paper changes to commit")
            return ""
        paper_short = paper_path.name.replace("2026_", "")[:40]
        diff_info = _diff_summary(paper_path)
        body = f"Changes: {diff_info}" if diff_info else ""
        full_msg = _commit_message(f"[{paper_short}] {msg}", body)
        result = run_cmd(["git", "commit", "-m", full_msg, "--"]
                         + staged_files)
        if result.returncode == 0:
            h = run_cmd(["git", "rev-parse", "--short", "HEAD"]).stdout.strip()
            logger.info(f"{tag} Committed: {h} — {msg[:60]}")
            _add_paper_only(paper_path)
            leftover = _staged_paper_source_files(paper_path)
            if leftover:
                follow_msg = _commit_message(
                    f"[{paper_short}] {msg} (source follow-up)",
                    "Changes: commit paper-source changes left staged after "
                    "the primary commit.")
                follow = run_cmd(["git", "commit", "-m", follow_msg, "--"]
                                 + leftover)
                if follow.returncode == 0:
                    h2 = run_cmd(["git", "rev-parse", "--short",
                                  "HEAD"]).stdout.strip()
                    logger.warning(
                        f"{tag} Committed follow-up staged sources: {h2}")
                    return h2
                logger.warning(
                    f"{tag} Follow-up source commit failed: "
                    f"{follow.stderr[:200]}")
            return h
        logger.warning(f"{tag} Commit failed: {result.stderr[:200]}")
        return ""


def git_commit_multi(paths: list[Path], msg: str, *, tag: str = "") -> str:
    """Commit paper source changes across paths. Never commit artifacts."""
    with git_repo_lock():
        for p in paths:
            if p.is_dir():
                _restore_tracked_non_source_changes(p, tag=tag)
                _add_paper_only(p)
            elif _is_paper_source_path(p):
                run_cmd(["git", "add", "--", str(p)])
        staged_files: list[str] = []
        for p in paths:
            staged_files.extend(_staged_paper_source_files(p))
        staged_files = sorted(set(staged_files))
        if not staged_files:
            return ""
        full_msg = _commit_message(msg)
        result = run_cmd(["git", "commit", "-m", full_msg, "--"]
                         + staged_files)
        if result.returncode == 0:
            h = run_cmd(["git", "rev-parse", "--short", "HEAD"]).stdout.strip()
            logger.info(f"{tag} Committed: {h} — {msg[:60]}")
            return h
        return ""


AGENT_CONTEXT_CONTRACTS = {
    "fresh_review": (
        "Clean-room review. Use only the manuscript/PDF and the explicit "
        "instructions in this prompt. Do not rely on prior pipeline history, "
        "previous reviews, stale artifacts, or conversation memory."
    ),
    "scope_bound_review": (
        "Independent review bounded by the stable scope files named in the "
        "prompt. Use the manuscript, research_directive, scope_contract, and "
        "listed inventories if explicitly requested; ignore previous review "
        "verdicts unless the prompt quotes them."
    ),
    "contextual_supervision": (
        "Review-only supervisory pass. Use the supplied history, artifacts, "
        "diff context, and prior decisions to track changes across the "
        "pipeline. Do not edit files."
    ),
    "contextual_execution": (
        "Execution/repair pass. Use the supplied issues, scope contract, prior "
        "round context, and manuscript state to edit files directly while "
        "preserving unrelated work."
    ),
}


def with_agent_context_contract(prompt: str, *,
                                context_mode: str = "",
                                agent_role: str = "") -> str:
    if not context_mode:
        return prompt
    semantics = AGENT_CONTEXT_CONTRACTS.get(
        context_mode,
        "Use only the context explicitly authorized by this prompt.",
    )
    header = textwrap.dedent(f"""\
        ## Agent Context Contract
        context_mode: `{context_mode}`
        agent_role: `{agent_role or "unspecified"}`
        semantics: {semantics}
    """)
    return f"{header}\n\n{prompt}"


# ---------------------------------------------------------------------------
# Oracle (ChatGPT Pro) interface
# ---------------------------------------------------------------------------

def oracle_submit(task_id: str, prompt: str,
                  pdf_path: Optional[Path] = None,
                  model: str = "chatgpt-5.4-pro-extended",
                  context_mode: str = "",
                  agent_role: str = "") -> bool:
    prompt = with_agent_context_contract(
        prompt, context_mode=context_mode, agent_role=agent_role)
    if context_mode:
        logger.info(f"Oracle context: {context_mode}"
                    f"{'/' + agent_role if agent_role else ''}")
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


def oracle_cancel(task_id: str, reason: str) -> bool:
    try:
        http_post(f"{ORACLE_SERVER}/cancel",
                  {"task_id": task_id, "reason": reason}, timeout=30)
        return True
    except Exception as e:
        logger.warning(f"Oracle cancel failed for {task_id}: {e}")
        return False


def oracle_task_status(task_id: str) -> dict:
    try:
        safe_id = quote(task_id, safe="")
        return http_get(f"{ORACLE_SERVER}/task_status/{safe_id}", timeout=10)
    except Exception:
        return {"task_id": task_id, "phase": "unknown"}


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


def is_oracle_final_response_valid(response: str) -> bool:
    if not response:
        return False
    cleaned = response.strip()
    if len(cleaned) < 300:
        return False
    lower = cleaned.lower()
    if "overall verdict" not in lower and "verdict" not in lower:
        return False
    return any(v in lower for v in (
        "accept", "minor revision", "major revision", "reject",
        "resolved", "unresolved", "blocker",
    ))


def oracle_poll(task_id: str, timeout: int = 7200,
                poll_interval: int = 30) -> str:
    """EVENT WAIT — blocks until oracle responds.

    Registers with oracle_wait_enter/exit so the rolling dispatcher
    knows how many workers are I/O-blocked (not consuming CPU).
    The timeout is an active-oracle budget: time spent merely queued
    behind other ChatGPT browser agents does not count against it.
    """
    oracle_wait_enter()
    logger.info(f"EVENT WAIT: oracle {task_id} (max {timeout}s, "
                f"oracle_waiters={get_oracle_wait_count()})")
    wait_start = time.time()
    active_start: Optional[float] = None
    last_log_bucket = -1
    try:
        while True:
            try:
                data = http_get(f"{ORACLE_SERVER}/result/{task_id}", timeout=10)
                if data.get("status") == "completed":
                    r = data.get("response", "")
                    logger.info(f"Oracle response: {task_id} ({len(r)} chars, "
                                f"{int(time.time()-wait_start)}s wall)")
                    return r
                if data.get("status") in {"cancelled", "failed"}:
                    logger.warning(f"Oracle terminal status for {task_id}: "
                                   f"{data.get('status')}")
                    if data.get("status") == "cancelled":
                        return ORACLE_CANCELLED_RESPONSE
                    return ""
            except Exception:
                pass

            phase = oracle_task_status(task_id)
            now = time.time()
            phase_name = phase.get("phase", "unknown")
            if phase_name == "active":
                server_elapsed = phase.get("elapsed")
                if isinstance(server_elapsed, int):
                    active_elapsed = server_elapsed
                    active_start = now - active_elapsed
                else:
                    if active_start is None:
                        active_start = now
                    active_elapsed = int(now - active_start)
                if active_elapsed >= timeout:
                    return ""
                log_elapsed = active_elapsed
                log_state = f"active/{phase.get('agent_id', '?')}"
            elif phase_name == "queued":
                active_start = None
                log_elapsed = int(now - wait_start)
                log_state = f"queued pos={phase.get('position', '?')}/{phase.get('queue_length', '?')}"
            else:
                log_elapsed = int(now - wait_start)
                log_state = phase_name
                if log_elapsed >= 600:
                    logger.warning(f"Oracle task {task_id} not visible to "
                                   f"server after {log_elapsed}s "
                                   f"(phase={phase_name})")
                    return ""

            bucket = log_elapsed // 60
            if bucket > 0 and bucket != last_log_bucket:
                last_log_bucket = bucket
                logger.info(f"  Waiting for {task_id}... ({log_state}, "
                            f"{log_elapsed}s, oracle_waiters={get_oracle_wait_count()})")
            time.sleep(poll_interval)
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
               dry_run: bool = False,
               context_mode: str = "",
               agent_role: str = "") -> str:
    prompt = with_agent_context_contract(
        prompt, context_mode=context_mode, agent_role=agent_role)
    if context_mode:
        logger.info(f"Codex context: {context_mode}"
                    f"{'/' + agent_role if agent_role else ''}")
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
CLAUDE_LIMIT_PATTERNS = (
    "hit your limit",
    "usage limit",
    "rate limit",
    "resets ",
)


def _is_claude_unavailable_text(text: str) -> bool:
    lower = (text or "").lower()
    return any(pat in lower for pat in CLAUDE_LIMIT_PATTERNS)


def claude_health_status(timeout_seconds: int = 45) -> tuple[bool, str]:
    """Return whether Claude is available for required supervision gates."""
    claude_bin = CLAUDE_PATH
    if not Path(claude_bin).exists() and not shutil.which(claude_bin):
        return False, f"Claude CLI not found: {claude_bin}"
    cmd = [claude_bin, "-p", "--dangerously-skip-permissions"]
    try:
        result = subprocess.run(
            cmd,
            input='Return exactly {"valid": true} and nothing else.',
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
            cwd=str(REPO_ROOT),
            shell=IS_WINDOWS and str(claude_bin).endswith(".cmd"),
            encoding="utf-8",
            errors="replace",
        )
    except subprocess.TimeoutExpired:
        return False, f"Claude health check timed out after {timeout_seconds}s"
    text = "\n".join(x for x in (result.stdout, result.stderr) if x).strip()
    excerpt = text.replace("\n", " ")[:300]
    if _is_claude_unavailable_text(text):
        return False, excerpt or "Claude reported a usage limit"
    if result.returncode != 0:
        return False, f"Claude health check failed rc={result.returncode}: {excerpt}"
    if not re.search(r"""["']valid["']\s*:\s*true""", text,
                     re.IGNORECASE):
        return False, f"Claude health check returned unexpected output: {excerpt}"
    return True, "Claude supervision available"


def claude_exec(prompt: str, *, work_dir: Optional[Path] = None,
                timeout_seconds: int = 600,
                dry_run: bool = False,
                context_mode: str = "",
                agent_role: str = "") -> str:
    """Call Claude Code CLI for independent review/verification.

    Uses `claude -p --dangerously-skip-permissions` for non-interactive
    execution. Claude reads the repo, has full context, and provides
    independent judgment separate from Codex.

    Used for: Stage F2, A4, C1, D2 (all verification/review steps).
    """
    prompt = with_agent_context_contract(
        prompt, context_mode=context_mode, agent_role=agent_role)
    if context_mode:
        logger.info(f"Claude context: {context_mode}"
                    f"{'/' + agent_role if agent_role else ''}")
    if dry_run:
        logger.info(f"[DRY RUN] claude_exec:\n{prompt[:200]}...")
        return "(dry run)"
    if not CLAUDE_ENABLED:
        raise RuntimeError("Claude disabled by --no-claude")

    wait_for_memory(tag="[claude]")

    claude_bin = CLAUDE_PATH
    if not Path(claude_bin).exists() and not shutil.which(claude_bin):
        raise RuntimeError(f"Claude CLI not found: {claude_bin}")

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
        raise RuntimeError(f"Claude CLI timed out after {timeout_seconds}s")
    finally:
        elapsed = time.monotonic() - start
        rc = result.returncode if result else "?"
        logger.info(f"Claude CLI: {elapsed:.1f}s (rc={rc})")

    output = result.stdout or ""
    combined = "\n".join(
        x for x in (result.stdout or "", result.stderr or "") if x
    )
    if _is_claude_unavailable_text(combined):
        excerpt = combined.replace("\n", " ")[:300]
        raise RuntimeError(f"Claude CLI unavailable: {excerpt}")
    if result and result.returncode != 0:
        excerpt = combined.replace("\n", " ")[:300]
        logger.warning(f"Claude CLI error: {excerpt}")
        raise RuntimeError(
            f"Claude CLI failed rc={result.returncode}: {excerpt}")

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
               model=model, dry_run=dry_run,
               context_mode="contextual_execution",
               agent_role="compile_repair")
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
    if not CLAUDE_ENABLED:
        logger.info(
            "PROGRAM_BOARD update skipped in --no-claude mode: "
            f"{paper_name} -> {stage}"
        )
        return
    if not PROGRAM_BOARD.exists():
        return
    new_status = f"{stage} ({detail})" if detail else stage
    try:
        with git_repo_lock():
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
                _invalidate_board_cache()
                logger.info(f"PROGRAM_BOARD updated: {paper_name} -> {new_status}")
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
    """Compatibility wrapper for the former A0 prompt.

    Stage A no longer performs automatic theorem demotion.  A0 now fixes the
    paper's scope contract and leaves all theorem/proposition decisions to the
    later inventory, theoremization, and audit gates.
    """
    return build_scope_contract_prompt(paper_dir, target_journal, "")


def build_claude_scope_brief_prompt(paper_dir: str, target_journal: str,
                                    main_paper_dir: str = "") -> str:
    main_section = (
        f"\nMain project paper directory: {main_paper_dir}\n"
        "Read it as the project-level source of definitions, notation, "
        "theorems, constructions, and unfinished interfaces.\n"
        if main_paper_dir else
        "\nNo separate main project directory was provided. Infer the project "
        "context from the current paper and sibling publication papers.\n"
    )
    ledger_section = _format_research_ledger_context(paper_dir)
    return textwrap.dedent(f"""\
        You are Claude acting as the pipeline's independent supervisory
        reviewer.  You do not edit files.  Your role is to set the scope basis
        that Codex must use when it constructs Stage A0.

        Paper directory: {paper_dir}
        Target journal: {target_journal}
        {main_section}
        {ledger_section}
        Read the paper and the stable directive if present:
          {paper_dir}/research_directive.md

        ## Task

        Produce a supervisory scope brief.  This brief is not the final
        scope_contract; Codex will operationalize it in A0.  Your job is to
        define the independent review basis:
        - the article's central role in the project;
        - the scope that should be preserved, not weakened;
        - the project objects and interfaces Codex must bind to the paper;
        - what Codex must include, deepen, externalize, or leave to a split
          pipeline;
        - the language/structure risks that should be watched throughout the
          pipeline;
        - any human decisions that should not be guessed.

        ## Output

        Do not edit files. Output exactly one JSON object:
        ```json
        {{
          "valid": true,
          "supervision_phase": "scope_brief",
          "paper_role": "...",
          "central_scope": "...",
          "must_preserve": [],
          "project_bindings": [],
          "must_include_or_deepen": [],
          "supporting_only": [],
          "split_candidates_to_track": [],
          "language_structure_risks": [],
          "bad_example_mechanisms_to_track": [],
          "human_decisions": [],
          "codex_a0_instructions": []
        }}
        ```
    """)


def build_scope_contract_prompt(paper_dir: str, target_journal: str,
                                main_paper_dir: str = "",
                                claude_scope_brief: str = "") -> str:
    main_section = (
        f"\nMain project paper directory: {main_paper_dir}\n"
        "Read it and bind every relevant definition, notation, theorem, "
        "construction, and unfinished interface to the present article.\n"
        if main_paper_dir else
        "\nNo separate main project directory was provided. Infer project "
        "bindings from the current paper and sibling publication papers.\n"
    )
    ledger_section = _format_research_ledger_context(paper_dir)
    return textwrap.dedent(f"""\
        You are setting the Stage A scope contract for a research paper aimed at
        "{target_journal}".

        Paper directory: {paper_dir}
        {main_section}
        {ledger_section}
        Stable directive file: {paper_dir}/research_directive.md

        ## Claude supervisory scope brief

        Codex must treat the following Claude brief as the independent
        supervisory basis for A0.  Operationalize it into stable artifacts.
        If you disagree with part of the brief, preserve the disagreement in
        `scope_contract.md` under "supervisory notes"; do not silently ignore
        it.

        ```json
        {claude_scope_brief or "{}"}
        ```

        ## Task

        Read the entire paper, the stable directive, and the main project
        context if provided. Write a precise `scope_contract.md` and
        `scope_contract.json` in {paper_dir}. This is a contract for what the
        current article must prove; it is not a referee report and not a
        weakening pass.

        `scope_contract.md` must contain:
        - the central research question of this article;
        - the exact project definitions, notation, theorems, constructions, and
          unfinished interfaces on which the paper depends;
        - the minimal target-journal publication bar;
        - what must be proved inside this paper;
        - what may be used only as cited background or supporting material;
        - what belongs outside this paper and should be considered for a
          separate split-paper pipeline.

        `scope_contract.json` must be a JSON object with exactly these keys:
        ```json
        {{
          "valid": true,
          "research_question": "...",
          "target_journal_bar": "...",
          "main_project_bindings": ["..."],
          "in_scope": ["..."],
          "must_prove_in_this_paper": ["..."],
          "supporting_only": ["..."],
          "out_of_scope": ["..."],
          "split_policy": "...",
          "failure_modes_to_control": ["..."]
        }}
        ```

        ## Hard rules

        1. Do not demote, weaken, delete, or rename theorem environments in
           this stage.
        2. Do not add new mathematical results in this stage.
        3. Do not use conversation-relative phrases such as "latest idea" or
           "current discussion"; all directives must be stable file content.
        4. Whenever cross-resolution objects occur, forbid naive truncation as
           an invariant unless the paper explicitly proves descent through a
           fold-aware gauge, stable inverse system, or equivalent structure.
        5. Treat bad examples structurally: identify which possible failures
           should be forced into classifiable mechanisms such as near-maximal
           fiber concentration, sticky cross-scale behavior, Frostman-type
           non-concentration failure, plate/sector collapse, local solvability
           with nontrivial holonomy, or finite-budget obstruction.

        Output only the two artifact files. Do not edit paper .tex files.
    """)


def build_theorem_inventory_prompt(paper_dir: str, target_journal: str,
                                   main_paper_dir: str = "") -> str:
    main_section = (
        f"\nMain project paper directory: {main_paper_dir}\n"
        if main_paper_dir else "\n"
    )
    ledger_section = _format_research_ledger_context(paper_dir)
    return textwrap.dedent(f"""\
        You are running Stage A theorem inventory for a paper aimed at
        "{target_journal}".

        Paper directory: {paper_dir}
        {main_section}
        {ledger_section}
        First read `scope_contract.md`, `scope_contract.json`, and
        `research_directive.md` in {paper_dir}. Then scan the paper's .tex and
        .bib files, and inspect the main project context if provided.

        ## Task

        Write `theorem_inventory.json` and `theorem_inventory.md` in
        {paper_dir}. The inventory must classify every theorem, proposition,
        lemma, corollary, definition, construction, and unfinished proof
        interface that matters for the paper's scope.

        `theorem_inventory.json` must be a JSON object with exactly these keys:
        ```json
        {{
          "valid": true,
          "in_scope_present": [],
          "missing_in_scope_results": [],
          "weak_in_scope_core_results": [],
          "proof_gaps": [],
          "supporting_appendix_or_background": [],
          "out_of_scope_strong_results": [],
          "split_candidates": [],
          "irrelevant_or_remove": [],
          "naive_truncation_risks": [],
          "journal_style_gaps": []
        }}
        ```

        For every list item use a compact object, not a bare string:
        {{
          "label": "...",
          "location": "...",
          "reason": "...",
          "required_action": "..."
        }}
        For `out_of_scope_strong_results` and `split_candidates`, add these
        fields whenever applicable:
        {{
          "candidate_title": "...",
          "source_contribution": "what Stage A reasoning discovered",
          "scope_mismatch": "why it does not belong in the present article",
          "independent_paper_rationale": "why it may support a new paper",
          "needed_to_split": ["..."]
        }}

        ## Classification rules

        - `missing_in_scope_results`: results required by the scope contract but
          absent from the manuscript.
        - `weak_in_scope_core_results`: results present but too weak for the
          article's stated scope or target journal.
        - `proof_gaps`: missing arguments, unjustified hypotheses, broken
          references, or incomplete interfaces.
        - `out_of_scope_strong_results` and `split_candidates`: mathematically
          interesting material that should be considered by a separate
          split-paper pipeline rather than forced into this article.
        - `naive_truncation_risks`: any place where a cross-resolution quantity
          is treated as invariant without fold-aware/stable-system descent.

        ## Hard rules

        1. Do not edit paper .tex files in this inventory stage.
        2. Do not hide a missing core theorem by recommending demotion.
        3. If a result is classical, classify it as supporting/background and
           specify the citation need; do not present it as new.
        4. If the paper contains a bad example or possible counterexample,
           classify its structural mechanism rather than merely describing it.

        Return the same JSON object in your final answer.
    """)


def build_theoremization_prompt(paper_dir: str, target_journal: str,
                                issue_kind: str, issues_json: str,
                                round_num: int) -> str:
    ledger_section = _format_research_ledger_context(paper_dir)
    return textwrap.dedent(f"""\
        You are performing Stage A2 theoremization round {round_num} for a
        paper aimed at "{target_journal}".

        Paper directory: {paper_dir}
        Issue kind: {issue_kind}

        Scope contract and directive:
        - {paper_dir}/research_directive.md
        - {paper_dir}/scope_contract.md
        - {paper_dir}/scope_contract.json

        Issues to resolve:
        ```json
        {issues_json}
        ```
        {ledger_section}

        ## Task

        Edit the paper directly so the manuscript satisfies the scope contract.
        The default action is to make the mathematics strong enough for the
        stated scope, not to weaken the paper until it becomes safe.

        Depending on the issue kind:
        - `missing_in_scope_results`: add the missing theorem/proposition/lemma,
          all required notation, and a complete proof.
        - `weak_in_scope_core_results`: strengthen the result into a genuine
          theorem chain, rigidity statement, classification, extremal result,
          obstruction theorem, budget lower bound, stability criterion, or
          equivalent high-value conclusion.
        - `proof_gaps`: close the proof with minimal new lemmas and explicit
          hypotheses; remove or quarantine claims that cannot be proved.
        - `audit_blockers`: revise exactly against the Stage A audit blockers.
        - `final_audit_repair`: perform a focused near-pass repair against
          the final Stage A audit.  Prefer source-level fixes: self-contained
          headline hypotheses, split hygiene for root theorem files, removal
          of internal audit macros from submission sources, and journal-facing
          theorem/proof presentation.  Do not spend the repair on README.md,
          scope/inventory JSON, split-candidate ledgers, or other
          non-submission artifacts; if an audit mentions stale artifacts,
          translate that complaint into a source-level paper fix or ignore it
          for the Stage A gate.

        For `missing_in_scope_results` and `weak_in_scope_core_results`, the
        acceptance criterion is explicit: introduce or strengthen at least one
        labelled theorem-like environment (`theorem`, `proposition`, `lemma`,
        or `corollary`) with a complete proof, and connect it to the paper's
        main theorem chain.  A short explanatory paragraph, synonym rewrite, or
        local notation cleanup is a failed edit.  If the issue cannot honestly
        be solved inside this paper, do not pad the manuscript; record it as a
        split-paper candidate instead.

        ## Research route

        Use a bad-example-structure route whenever it fits the paper: isolate
        the worst possible obstruction to the main claim; prove it belongs to a
        small classifiable skeleton; then prove the skeleton theorem,
        decomposition theorem, gluing obstruction, budget lower bound, or
        induction contradiction that closes the article's theorem chain.

        Fold-aware restriction, stable inverse systems, pseudo-invariant
        elimination, sticky near-maximal fibers, high-moment freezing, escort
        concentration, Cech gluing obstruction, discrete holonomy, curvature
        certificates, boundary/Walsh-Stokes/Euler certificates, oracle capacity,
        prime-registers, external ledgers, and finite-budget lower bounds may
        be used only when they are genuinely bound to this paper's definitions
        and proof interfaces.

        ## Hard rules

        1. No synonym restatement, relabelling, or old-result shell game.
        2. No unsupported theorem. Every new or strengthened result must have a
           complete proof or be removed.
        3. Known external results may be used only as cited tools.
        4. Do not treat naive truncations as invariants unless descent through
           a fold-aware gauge, stable inverse system, or equivalent structure is
           proved in the paper.
        5. If a result becomes strong but no longer belongs to this paper's
           scope, do not force it into the manuscript; mark it for the split
           pipeline instead.
        6. No revision logs, no author notes, no "we fixed" artifacts.

        Compile after editing:
          cd {paper_dir} && xelatex -interaction=nonstopmode main.tex
    """)


def build_split_hygiene_prompt(paper_dir: str, target_journal: str,
                               candidates_json: str, round_num: int) -> str:
    return textwrap.dedent(f"""\
        You are performing Stage A split hygiene round {round_num} for a paper
        aimed at "{target_journal}".

        Paper directory: {paper_dir}

        Candidate material:
        ```json
        {candidates_json}
        ```

        ## Task

        Decide which candidate results are outside the current article's scope
        but potentially strong enough for an independent paper. Write
        `split_candidates.json` in {paper_dir} with:
        ```json
        {{
          "candidates": [
            {{
              "title": "...",
              "source_labels": ["..."],
              "independent_paper_potential": "low|medium|high",
              "source_contribution": "what was discovered while improving this paper",
              "scope_mismatch": "why it should not be forced into this paper",
              "reason": "...",
              "needed_to_split": ["..."],
              "current_paper_action": "cite_only|appendix_only|remove|keep_as_tool"
            }}
          ]
        }}
        ```

        Then edit the current paper so the main line stays coherent:
        - keep only material required by the scope contract;
        - cite or relegate supporting material when appropriate;
        - remove material that distracts from the article's theorem chain;
        - do not create the new paper here.

        Compile after editing:
          cd {paper_dir} && xelatex -interaction=nonstopmode main.tex
    """)


def build_stage_a_audit_prompt(paper_dir: str, target_journal: str,
                               audit_round: int) -> str:
    return textwrap.dedent(f"""\
        You are the Codex mathematical gate for Stage A of a paper aimed at
        "{target_journal}". This is audit round {audit_round}.

        Paper directory: {paper_dir}

        Read:
        - the full paper;
        - `research_directive.md`;
        - `scope_contract.md` and `scope_contract.json`;
        - `theorem_inventory.json`;
        - `split_candidates.json` if it exists.

        ## Mathematical gate

        Do not duplicate Claude's role.  Your job is theorem-level mathematics:
        whether the in-scope results are present, nontrivial, and proved.

        Gate boundary: score the durable submission source, namely the
        paper's theorem/proof content in `.tex`, `.bib`, and `.sty` files.
        README files, scope artifacts, theorem inventories, split ledgers, and
        non_submission_artifacts are diagnostic context only.  Stale or
        inconsistent artifacts may reveal a source-level mathematical problem,
        but artifact staleness itself must not lower a metric, create
        `split_required`, or block `ready_for_oracle_review`.

        Score only these metrics from 1 to 10:
        - `theorem_completeness`: every in-scope mature theorem that belongs in
          this article is present and integrated.
        - `proof_integrity`: proofs are complete, hypotheses are explicit, and
          no interface is left unresolved.
        - `depth_novelty`: the article contains publishable mathematical
          conclusions rather than repackaged standard facts.

        Treat naive truncation, fake theoremization, unsupported descent,
        duplicated sibling-paper statements, and unproved bad-example
        classification as mathematical blockers.

        ## Output

        Do not edit files. Output exactly one JSON object:
        ```json
        {{
          "metrics": {{
            "theorem_completeness": 0,
            "proof_integrity": 0,
            "depth_novelty": 0
          }},
          "verdict": "pass|revise|block",
          "blockers": [],
          "required_revisions": [],
          "split_required": false,
          "split_reasons": [],
          "ready_for_oracle_review": false
        }}
        ```
    """)


def build_claude_stage_a_structural_audit_prompt(
    paper_dir: str, target_journal: str, audit_round: int
) -> str:
    return textwrap.dedent(f"""\
        You are the Claude structural, language, and system audit gate for
        Stage A of a paper aimed at "{target_journal}". This is audit round
        {audit_round}.

        Paper directory: {paper_dir}

        Read:
        - the full paper;
        - `research_directive.md`;
        - `scope_contract.md` and `scope_contract.json`;
        - `theorem_inventory.json`;
        - `split_candidates.json` if it exists.

        ## Role

        Do not duplicate Codex's theorem-proof audit.  Your job is the work
        Claude is best suited for:
        - decompose remaining work into actionable packages;
        - check that scope, inventory, paper text, and split decisions are
          systemically consistent;
        - check language, journal register, narrative flow, and section
          architecture;
        - detect local/global contamination, dangling interfaces, revision
          artifacts, and misplaced split candidates.

        Gate boundary: Stage A can only make durable paper-source commits.
        Therefore, block or lower metrics only for problems visible in the
        committed submission source package: `.tex`, `.bib`, `.sty`, and
        theorem-bearing root source files that would travel with the article.
        README.md, scope_contract files, theorem_inventory files,
        split_candidates files, research ledgers, and non_submission_artifacts
        are diagnostic context.  Do not mark `split_required`, reduce
        `split_hygiene`, or fail `ready_for_oracle_review` solely because such
        artifacts are stale or internally inconsistent.  If an artifact points
        to a real source problem, cite the source file that must change.

        Score only these metrics from 1 to 10:
        - `scope_coverage`: the article implements the stable scope contract
          and uses the relevant project objects consistently.
        - `journal_fit`: language, exposition density, section structure,
          references, and theorem/proof presentation fit "{target_journal}".
        - `split_hygiene`: strong out-of-scope material is externalized,
          indexed, or marked for the split-paper pipeline without polluting
          the current article.

        ## Work decomposition

        If the paper does not pass, return `work_packages`. Each package must
        be actionable and assigned to exactly one owner:
        - `codex_math`: theorem/proof repair or theoremization.
        - `codex_editorial`: prose, structure, references, notation cleanup.
        - `split_pipeline`: independent-paper candidate handling.
        - `stage_d_backflow`: item that should later be considered for main
          paper backflow.
        - `human_decision`: scope or journal decision that should not be
          guessed by the pipeline.

        ## Output

        Do not edit files. Output exactly one JSON object:
        ```json
        {{
          "metrics": {{
            "scope_coverage": 0,
            "journal_fit": 0,
            "split_hygiene": 0
          }},
          "verdict": "pass|revise|block",
          "blockers": [],
          "required_revisions": [],
          "work_packages": [
            {{
              "owner": "codex_math|codex_editorial|split_pipeline|stage_d_backflow|human_decision",
              "priority": "blocker|high|medium|low",
              "location": "...",
              "task": "...",
              "acceptance_criterion": "..."
            }}
          ],
          "split_required": false,
          "split_reasons": [],
          "ready_for_oracle_review": false
        }}
        ```
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

        If a proof genuinely requires finite exact certificate data referenced
        by the manuscript, you may create or update paper-local files under
        certificates/ with suffix .json or .py. Do not create any other
        non-submission artifacts.
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

        If a proof genuinely requires finite exact certificate data referenced
        by the manuscript, you may create or update paper-local files under
        certificates/ with suffix .json or .py. Do not create any other
        non-submission artifacts.

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
        3. **Issue table** (literal pipe-delimited Markdown table; no empty cells):
           | ID | Section | Severity (BLOCKER/MEDIUM/LOW) | Description | Suggested fix |
           Every issue row must be on its own line and must start with a pipe,
           e.g. `| B1 | §2 | BLOCKER | ... | ... |`.
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
                                        round_num: int,
                                        prior_issues: str = "",
                                        deep_mode: bool = False) -> str:
    # When prior_issues are supplied, include them so Codex knows what was
    # already flagged and fixed (prevents regressions).
    history_block = ""
    if prior_issues:
        history_block = textwrap.dedent(f"""\

        ## Prior Oracle issues (already flagged in earlier rounds — do NOT regress)
        {prior_issues}

        IMPORTANT: The above issues were raised in previous review rounds.
        Ensure your fixes do NOT reintroduce any of them. If a prior issue
        is repeated in the current round, it means the previous fix was
        insufficient — apply a MORE thorough fix this time.
        """)

    deep_block = ""
    if deep_mode:
        deep_block = textwrap.dedent("""\

        ## DEEP MODE ACTIVATED (paper stuck in review loop)
        Previous patch-level fixes were insufficient. Escalate your approach:
        1. RESTRUCTURE problematic sections, don't just patch sentences
        2. Rewrite proofs from scratch if they are flagged repeatedly
        3. Add new lemmas or intermediate steps where arguments are weak
        4. Consider reorganizing section order if flow is criticized
        5. Be aggressive — incremental patches have failed.
        """)

    return textwrap.dedent(f"""\
        You are fixing referee issues in the paper at: {paper_dir}
        Fix round {round_num}.

        ## Issues to fix (severity-sorted)
        {issues_text}
        {history_block}{deep_block}
        ## Instructions
        1. Fix BLOCKER issues first, then MEDIUM, then LOW
        2. For mathematical gaps: add missing proof steps or lemmas
        3. For unclear arguments: rewrite with explicit reasoning
        4. For missing references: add to references.bib and cite
        5. Do NOT delete existing theorems — improve them
        6. Do NOT add revision notes or "fixed per reviewer" language
        7. Keep all \\leanverified annotations intact
        8. Compile: cd {paper_dir} && xelatex -interaction=nonstopmode main.tex

        Only edit .tex/.bib paper sources inside {paper_dir}. If a fix
        genuinely requires finite exact certificate data referenced by the
        manuscript, you may create or update paper-local certificates/*.json
        or certificates/*.py. Do not create any other artifacts.
    """)


def build_claude_independent_review_prompt(paper_dir: str,
                                            target_journal: str,
                                            stage_c_memory: str = "") -> str:
    memory_block = ""
    if stage_c_memory:
        memory_block = textwrap.dedent(f"""\

        ## Stage C Memory

        Use this memory to track whether previous final-review issues were
        actually resolved and whether new regressions were introduced.  You are
        still reviewing the current manuscript directly; do not rubber-stamp a
        previous verdict.

        ```json
        {stage_c_memory}
        ```
        """)
    return textwrap.dedent(f"""\
        Systematic pre-submission review for "{target_journal}".
        Paper directory: {paper_dir}

        Read ALL .tex files. Do not simply assign an independent score.  Use
        Claude's strengths: language, structure, consistency, and work
        decomposition. Evaluate as the final systems gatekeeper before
        submission.

        Check:
        1. Language and journal register are natural, precise, and non-AI-like.
        2. Section architecture, theorem ordering, and narrative flow are
           coherent for "{target_journal}".
        3. Scope, abstract, introduction, and conclusion describe the same
           contribution.
        4. No revision artifacts ("we fixed", "as suggested", changelogs).
        5. References, labels, citations, and cross-references are coherent.
        6. Local notation does not leak into global statements.
        7. Any remaining work is decomposed into actionable packages.

        You may mention proof gaps if you see them, but do not spend the
        review duplicating Codex's theorem-level audit.
        {memory_block}

        ## Output Format (MUST follow exactly)
        ```json
        {{
          "verdict": "<submit|revise>",
          "issues": ["issue1", "issue2", ...],
          "work_packages": [
            {{
              "owner": "codex_math|codex_editorial|human_decision",
              "priority": "blocker|high|medium|low",
              "location": "...",
              "task": "...",
              "acceptance_criterion": "..."
            }}
          ],
          "quality_notes": "free text summary"
        }}
        ```

        verdict = "submit" means ready for journal submission.
        verdict = "revise" means more work needed — list issues precisely.
        Do NOT edit files — only output the JSON review.
    """)


def build_codex_fix_from_claude_prompt(paper_dir: str,
                                        issues: list[str],
                                        round_num: int,
                                        stage_c_memory: str = "") -> str:
    issues_text = "\n".join(f"  {i+1}. {iss}" for i, iss in enumerate(issues))
    memory_block = ""
    if stage_c_memory:
        memory_block = textwrap.dedent(f"""\

        ## Stage C Memory

        The following memory records prior final-review verdicts, issues, and
        fixes.  Use it to avoid repeating superficial patches.  If an issue
        reappears, treat the previous fix as insufficient and make a deeper
        structural correction.

        ```json
        {stage_c_memory}
        ```
        """)
    return textwrap.dedent(f"""\
        Fix issues found by the Stage C final gate.
        Paper: {paper_dir}
        Fix round {round_num}.

        ## Issues
        {issues_text}
        {memory_block}

        ## Instructions
        1. Read the relevant .tex files
        2. Fix each issue directly
        3. No revision notes, no changelogs
        4. Compile: cd {paper_dir} && xelatex -interaction=nonstopmode main.tex

        Only edit .tex and .bib files inside {paper_dir}.
    """)


def build_backflow_check_prompt(paper_dir: str, main_paper_dir: str) -> str:
    return textwrap.dedent(f"""\
        You are building a layered backflow dossier from a sub-paper into the
        main project paper.

        Sub-paper (just improved): {paper_dir}
        Main paper: {main_paper_dir}

        Read the sub-paper, the main paper, and these Stage A artifacts if
        present in the sub-paper directory:
        - research_directive.md
        - scope_contract.md / scope_contract.json
        - theorem_inventory.md / theorem_inventory.json
        - split_candidates.json
        - stage_a_audit.json

        ## Task

        Identify every result, definition, notation change, proof interface,
        obstruction, bad example, certificate, or citation relation produced or
        stabilized by the sub-paper that has value for the main paper.

        Classify each item into exactly one tier:
        - GLOBAL_CORE: general, stable, reusable theorem-level content that can
          enter the main paper's central theorem chain.
        - FRAMEWORK_INTERFACE: definitions, notation, gauges, certificates,
          obstruction interfaces, or reusable proof APIs that belong in the
          main paper's framework layer.
        - LOCAL_MODULE: locally useful material that should be indexed in a
          module registry, example ledger, or applications appendix, but not
          promoted into the main theorem chain.
        - BAD_EXAMPLE_CERTIFICATE: a local obstruction, boundary example,
          failure mode, holonomy/curvature certificate, or budget witness that
          clarifies the boundary of the main framework.
        - CITATION_ONLY: the main paper should cite the sub-paper or record a
          one-sentence relation, but not import the result.
        - SPLIT_CANDIDATE: valuable material that should be handled by the
          separate split-paper pipeline rather than imported into the main
          paper.
        - NO_BACKFLOW: nothing should be changed in the main paper.

        ## Output Format (MUST follow exactly)
        ```json
        {{
          "backflow_items": [
            {{
              "sub_paper_result": "Theorem 3.2 (improved bound)",
              "source_label": "thm:...",
              "backflow_class": "GLOBAL_CORE|FRAMEWORK_INTERFACE|LOCAL_MODULE|BAD_EXAMPLE_CERTIFICATE|CITATION_ONLY|SPLIT_CANDIDATE|NO_BACKFLOW",
              "main_paper_tier": "main_theorem_chain|framework_layer|module_registry|example_ledger|obstruction_section|applications_appendix|citation_registry|none",
              "main_paper_location": "Section 4, after Proposition 4.1",
              "action": "update_statement|incorporate_result|add_interface|add_ledger_entry|add_obstruction_example|add_reference|citation_only|no_change",
              "stability_basis": "why this is stable enough for the chosen tier",
              "locality_risk": "what local hypotheses prevent stronger backflow, if any",
              "detail": "exact description of what should change"
            }}
          ],
          "summary": "one paragraph overview"
        }}
        ```

        ## Rules

        1. Only GLOBAL_CORE may enter the main theorem chain.
        2. Local but useful content must be preserved through registry,
           examples, obstruction sections, appendix, or citations rather than
           being discarded.
        3. SPLIT_CANDIDATE items must not be imported into the main text; use
           citation_registry only if the main paper needs a relation note.
        4. Do not import notation that is local to the sub-paper unless it is
           normalized to the main paper's notation.
        5. If nothing needs to flow back, return an empty backflow_items array.

        Do NOT edit any files — only output the JSON analysis.
    """)


def build_backflow_placement_prompt(paper_dir: str, main_paper_dir: str,
                                     items: list[dict]) -> str:
    """D1.5: Explicit placement analysis — Codex proposes WHERE each backflow
    item belongs in the main paper, with section-level precision.
    Borrowed from outreach pipeline's two-step backflow pattern."""
    items_summary = ""
    for i, item in enumerate(items, 1):
        items_summary += (
            f"  {i}. {item.get('sub_paper_result', '')}\n"
            f"     Class: {item.get('backflow_class', '')}\n"
            f"     Main tier: {item.get('main_paper_tier', '')}\n"
            f"     Action: {item.get('action', '')}\n"
            f"     Stability: {item.get('stability_basis', '')}\n"
            f"     Locality risk: {item.get('locality_risk', '')}\n"
            f"     Detail: {item.get('detail', '')}\n"
        )
    return textwrap.dedent(f"""\
        You are deciding exactly WHERE in the main paper each backflow item
        should be placed.

        Sub-paper: {paper_dir}
        Main paper: {main_paper_dir}

        ## Backflow items to place
        {items_summary}

        ## Instructions
        1. Read the main paper structure:
           - `ls {main_paper_dir}` to see all .tex files
           - Read main.tex and key section files to understand structure
        2. For EACH item, determine:
           - Which .tex file to modify
           - Which section/subsection it belongs in
           - After which existing theorem/proposition/paragraph
           - Whether it belongs in the main theorem chain, framework layer,
             module registry, example ledger, obstruction section,
             applications appendix, citation registry, or should be skipped

        ## Output Format (MUST follow exactly)
        ```json
        {{
          "placements": [
            {{
              "item_index": 1,
              "target_file": "sec_main_results.tex",
              "target_section": "Section 3.2",
              "insert_after": "Proposition 3.5",
              "placement_type": "main_theorem_chain|framework_interface|module_registry|example_ledger|obstruction_section|applications_appendix|citation_only|skip",
              "rationale": "why this location (1 sentence)"
            }}
          ]
        }}
        ```

        Do NOT edit any files — only output the JSON placement plan.
    """)


def build_backflow_apply_prompt(paper_dir: str, main_paper_dir: str,
                                 items: list[dict],
                                 placements: list[dict] | None = None) -> str:
    items_text = ""
    # Build a lookup from item_index to placement info
    placement_map: dict[int, dict] = {}
    if placements:
        for p in placements:
            try:
                idx = int(p.get("item_index", 0))
            except Exception:
                idx = 0
            if idx:
                placement_map[idx] = p

    for i, item in enumerate(items, 1):
        original_index = item.get("_item_index", i)
        items_text += (
            f"  {i}. [{item.get('action','')}] "
            f"{item.get('sub_paper_result','')}\n"
            f"     Original item index: {original_index}\n"
            f"     Class: {item.get('backflow_class','')}\n"
            f"     Main tier: {item.get('main_paper_tier','')}\n"
            f"     Location: {item.get('main_paper_location','')}\n"
            f"     Stability: {item.get('stability_basis','')}\n"
            f"     Locality risk: {item.get('locality_risk','')}\n"
            f"     Detail: {item.get('detail','')}\n"
        )
        # Append explicit placement guidance if available
        pl = placement_map.get(original_index) or placement_map.get(i)
        if pl:
            items_text += (
                f"     >>> PLACEMENT: file={pl.get('target_file', '?')}, "
                f"section={pl.get('target_section', '?')}, "
                f"after={pl.get('insert_after', '?')}, "
                f"type={pl.get('placement_type', '?')}\n"
            )

    return textwrap.dedent(f"""\
        Apply backflow changes from sub-paper to main paper.

        Sub-paper: {paper_dir}
        Main paper: {main_paper_dir}

        ## Changes to apply (with explicit placement guidance)
        {items_text}

        ## Instructions
        1. Read the main paper's .tex files
        2. For each item, use the PLACEMENT guidance to locate the exact insertion point
        3. Apply each change at the specified tier:
           - GLOBAL_CORE only if placement_type=main_theorem_chain
           - FRAMEWORK_INTERFACE in the framework/definitions/interface layer
           - LOCAL_MODULE in a registry, example ledger, or appendix
           - BAD_EXAMPLE_CERTIFICATE in an obstruction/boundary example section
           - CITATION_ONLY as a citation or relation note only
           - SPLIT_CANDIDATE only as a citation-registry pointer if explicitly approved
        4. Update references.bib if new citations are needed
        5. Keep all existing content intact — only add/update as specified
        6. Compile: cd {main_paper_dir} && xelatex -interaction=nonstopmode main.tex

        Only edit .tex and .bib files in {main_paper_dir}. Do not write
        reports, logs, markdown artifacts, JSON artifacts, or changelogs.
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
                                      "scores", "issues", "valid", "metrics",
                                      "in_scope_present", "placements",
                                      "approved", "quality_verdict",
                                      "system_verdict", "work_packages",
                                      "codex_work_packages", "candidates")):
                return d
        except json.JSONDecodeError:
            continue
    return {}


def parse_oracle_issues(review_text: str) -> list[dict]:
    """Extract structured issues from oracle review."""
    issues = []
    # Table rows: ID | Section | BLOCKER | desc | fix
    rows = re.findall(
        r"^\s*\|?\s*([A-Z]{0,4}\d+)\s*\|\s*([^|]+)\|\s*"
        r"(BLOCKER|MEDIUM|LOW|HIGH|CRITICAL)\s*\|\s*([^|]+?)"
        r"(?:\|\s*(.+?))?\s*\|?\s*$",
        review_text, re.MULTILINE | re.IGNORECASE,
    )
    for row in rows:
        issues.append({
            "id": row[0].strip(), "section": row[1].strip(),
            "severity": row[2].strip().upper(),
            "description": row[3].strip(),
            "suggested_fix": row[4].strip() if len(row) > 4 and row[4] else "",
        })
    # Fallback: ChatGPT sometimes strips Markdown pipes and collapses the whole
    # issue table into one line:
    #   IDSectionSeverity...Suggested fixB1§3 BLOCKER...B2§4 MEDIUM...
    if not issues:
        section = review_text
        m = re.search(
            r"Issue table\s*(.*?)(?:\n\s*(?:Proof audit|Conditional hypothesis map|"
            r"Theorem-by-theorem|Missing references|Concrete fixes)\b|\Z)",
            review_text, re.DOTALL | re.IGNORECASE,
        )
        if m:
            section = m.group(1)
        section = re.sub(
            r"^\s*ID\s*Section\s*Severity\s*\([^)]*\)\s*Description\s*Suggested\s*fix\s*",
            "",
            section.strip(),
            flags=re.IGNORECASE,
        )
        row_re = re.compile(
            r"(?P<id>[A-Z]{1,4}\d+)"
            r"(?P<section>.{1,180}?)"
            r"(?P<severity>BLOCKER|CRITICAL|HIGH|MEDIUM|LOW)"
            r"(?P<body>.*?)(?="
            r"[A-Z]{1,4}\d+.{1,180}?"
            r"(?:BLOCKER|CRITICAL|HIGH|MEDIUM|LOW)|\Z)",
            re.DOTALL | re.IGNORECASE,
        )
        for m2 in row_re.finditer(section):
            body = re.sub(r"\s+", " ", m2.group("body")).strip()
            issues.append({
                "id": m2.group("id").strip(),
                "section": re.sub(r"\s+", " ", m2.group("section")).strip(),
                "severity": m2.group("severity").upper(),
                "description": body[:1200],
                "suggested_fix": "",
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
            {"name": DEFAULT_TARGET_JOURNAL, "fit_score": 5,
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
    elif not CLAUDE_ENABLED:
        logger.info(f"{tag} F2 skipped (--no-claude, ambiguous fit="
                    f"{fit_score}); using Codex recommendation")
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
        _record_claude_supervision(
            state, "stage_f_journal_fit_review", claude_data, raw=out2)
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


def _stage_a_json_artifact(paper_path: Path, filename: str) -> Path:
    return paper_path / filename


def _read_json_artifact(paper_path: Path, filename: str) -> dict:
    path = _stage_a_json_artifact(paper_path, filename)
    if not path.exists():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _write_json_artifact(paper_path: Path, filename: str, data: dict) -> None:
    path = _stage_a_json_artifact(paper_path, filename)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False),
                    encoding="utf-8")


def _record_claude_supervision(state: PaperState, phase: str,
                               data: dict | None = None,
                               raw: str = "",
                               context_mode: str = "",
                               agent_role: str = "") -> None:
    """Append Claude's independent supervision record outside paper commits."""
    try:
        CLAUDE_SUPERVISION_DIR.mkdir(parents=True, exist_ok=True)
        safe = re.sub(r"[^a-zA-Z0-9_-]", "_", state.paper_name)
        path = CLAUDE_SUPERVISION_DIR / f"{safe}.jsonl"
        record = {
            "timestamp": datetime.now().isoformat(),
            "paper_name": state.paper_name,
            "paper_dir": state.paper_dir,
            "current_stage": state.current_stage,
            "current_round": state.current_round,
            "phase": phase,
            "context_mode": context_mode,
            "agent_role": agent_role,
            "data": data or {},
            "raw_excerpt": (raw or "")[:8000],
        }
        with open(path, "a", encoding="utf-8") as f:
            f.write(json.dumps(record, ensure_ascii=False) + "\n")
        state.log_event("CLAUDE", phase,
                        detail=json.dumps(data or {},
                                          ensure_ascii=False)[:15000])
    except Exception as exc:
        logger.warning(f"[{state.paper_name}] Failed to record Claude "
                       f"supervision ({phase}): {exc}")


def _coerce_items(value) -> list:
    if isinstance(value, list):
        return [v for v in value if v]
    if isinstance(value, dict):
        return [value] if value else []
    if isinstance(value, str) and value.strip():
        return [{"reason": value.strip()}]
    return []


def _scope_memory(paper_path: Path) -> dict:
    data = _read_json_artifact(paper_path, "scope_contract.json")
    if not data:
        return {}
    keys = ("research_question", "in_scope", "must_prove_in_this_paper",
            "out_of_scope", "split_policy")
    return {k: data.get(k) for k in keys if data.get(k)}


def _ledger_existing_fingerprints() -> set[str]:
    if not RESEARCH_LEDGER_FILE.exists():
        return set()
    seen: set[str] = set()
    try:
        for line in RESEARCH_LEDGER_FILE.read_text(
            encoding="utf-8", errors="replace"
        ).splitlines():
            try:
                data = json.loads(line)
            except Exception:
                continue
            fp = data.get("fingerprint")
            if fp:
                seen.add(str(fp))
    except Exception:
        return seen
    return seen


def _record_research_ledger_items(
    state: PaperState, phase: str, items: list
) -> None:
    """Persist useful out-of-scope findings for later paper initialization."""
    if not items:
        return
    try:
        RESEARCH_LEDGER_DIR.mkdir(parents=True, exist_ok=True)
        paper_path = Path(state.paper_dir)
        scope = _scope_memory(paper_path)
        seen = _ledger_existing_fingerprints()
        written = 0
        with open(RESEARCH_LEDGER_FILE, "a", encoding="utf-8") as fh:
            for raw in items:
                item = raw if isinstance(raw, dict) else {"reason": str(raw)}
                record = {
                    "timestamp": datetime.now().isoformat(),
                    "source_paper": state.paper_name,
                    "source_dir": state.paper_dir,
                    "target_journal": state.target_journal,
                    "phase": phase,
                    "category": item.get("ledger_category", "candidate"),
                    "scope_memory": scope,
                    "item": item,
                    "source_contribution": item.get("source_contribution", ""),
                    "scope_mismatch": item.get("scope_mismatch", ""),
                    "independent_paper_rationale": item.get(
                        "independent_paper_rationale", ""),
                    "why_recorded": (
                        item.get("reason")
                        or item.get("required_action")
                        or item.get("needed_to_split")
                        or "out-of-scope but potentially useful result"
                    ),
                    "promotion_status": "candidate_seed",
                    "status": "todo",
                }
                fp_src = json.dumps(
                    {
                        "source_paper": record["source_paper"],
                        "category": record["category"],
                        "item": record["item"],
                    },
                    sort_keys=True, ensure_ascii=False,
                )
                record["fingerprint"] = hashlib.sha1(
                    fp_src.encode("utf-8")).hexdigest()
                if record["fingerprint"] in seen:
                    continue
                seen.add(record["fingerprint"])
                fh.write(json.dumps(record, ensure_ascii=False) + "\n")
                written += 1
        if not written:
            return
        state.log_event("A", "research_ledger_recorded",
                        detail=f"{written} candidate item(s)")
        save_state(state)
    except Exception as exc:
        logger.warning(f"[{state.paper_name}] research ledger write failed: {exc}")


def _format_research_ledger_context(paper_dir: str, max_items: int = 8) -> str:
    if not RESEARCH_LEDGER_FILE.exists():
        return ""
    try:
        rows = []
        for line in RESEARCH_LEDGER_FILE.read_text(
            encoding="utf-8", errors="replace"
        ).splitlines()[-200:]:
            try:
                data = json.loads(line)
            except Exception:
                continue
            if data.get("source_dir") == paper_dir:
                continue
            rows.append(data)
        if not rows:
            return ""
        rows = rows[-max_items:]
        return textwrap.dedent(f"""\

            ## Prior Research Ledger Context

            The following items were produced by earlier Stage A reasoning but
            recorded as out-of-scope or split-paper candidates. They are
            background memory only: use them to avoid rediscovery, to preserve
            attribution of prior pipeline contributions, and to decide whether
            a result belongs in this paper or in a future paper.

            ```json
            {json.dumps(rows, indent=2, ensure_ascii=False)[:6000]}
            ```
        """)
    except Exception:
        return ""


def _format_stage_c_memory(state: PaperState,
                           current_oracle_verdict: str = "",
                           current_oracle_issues: Optional[list] = None,
                           max_events: int = 18) -> str:
    """Compact final-gate memory for Claude supervision and Codex fixes."""
    c_events = [
        {
            "round": h.get("round_num"),
            "action": h.get("action"),
            "verdict": h.get("verdict", ""),
            "committed": h.get("committed", False),
            "commit_hash": h.get("commit_hash", ""),
            "detail": str(h.get("detail", ""))[:2500],
        }
        for h in state.history
        if isinstance(h, dict) and h.get("stage") == "C"
    ][-max_events:]
    payload = {
        "paper_name": state.paper_name,
        "target_journal": state.target_journal,
        "stage_c_rounds_completed": state.stage_c_rounds,
        "stage_c_verdict_history": state.stage_c_verdicts[-20:],
        "current_oracle_verdict": current_oracle_verdict,
        "current_oracle_issues": current_oracle_issues or [],
        "prior_stage_b_verdicts": state.stage_b_verdicts[-10:],
        "prior_oracle_issues": state.stage_b_all_issues[-30:],
        "recent_stage_c_events": c_events,
    }
    return json.dumps(payload, ensure_ascii=False, indent=2)[:12000]


def _ensure_research_directive(paper_path: Path, target_journal: str,
                               *, dry_run: bool = False) -> bool:
    path = paper_path / "research_directive.md"
    if path.exists():
        try:
            if len(path.read_text(encoding="utf-8", errors="replace")) > 400:
                return True
        except Exception:
            pass
    if dry_run:
        return True
    text = textwrap.dedent(f"""\
        # Research Directive

        This file is the stable Stage A directive for the paper in this
        directory.  It replaces conversation-relative instructions and must be
        read before every scope, inventory, theoremization, split, and audit
        step.

        The publication goal is to make the current article suitable for
        submission to {target_journal}.  All mature theorems, definitions,
        notation, constructions, and unfinished proof interfaces that are
        genuinely in scope for this article must be integrated into the
        manuscript with complete proofs and proper references.  The pipeline
        should strengthen and close the article's theorem chain rather than
        weaken the scope merely to obtain a safe review.

        Results that are mathematically interesting but outside the current
        article's central scope must be recorded for a separate split-paper
        pipeline.  The current article may retain such material only as a
        cited tool, appendix support, or brief pointer when that is necessary
        for the paper's own theorem chain.

        Stage A should prefer structural, publishable conclusions: rigidity,
        classification, dichotomy, extremal, obstruction, budget lower bound,
        stability criterion, phase transition, local-to-global failure, and
        multiscale induction closure theorems.  Bad examples should be used as
        structure drivers: isolate the worst obstruction, prove it falls into
        a small classifiable skeleton, and close the argument through the
        appropriate decomposition, gluing obstruction, curvature certificate,
        finite-budget lower bound, or induction contradiction.

        Cross-resolution quantities must not be treated as genuine invariants
        by naive truncation.  Such quantities require descent through a
        fold-aware gauge, a stable inverse system, or an explicitly proved
        equivalent mechanism.
    """)
    path.write_text(text, encoding="utf-8")
    return True


def _strip_tex_for_contract(text: str, limit: int = 700) -> str:
    text = re.sub(r"%.*", "", text)
    text = re.sub(r"\\(label|ref|cite|eqref)\{[^}]*\}", "", text)
    text = re.sub(r"\\[a-zA-Z]+\*?(?:\[[^\]]*\])?(?:\{([^{}]*)\})?",
                  lambda m: m.group(1) or "", text)
    text = re.sub(r"\s+", " ", text).strip()
    return text[:limit]


def _read_stage_a_source_text(paper_path: Path, max_chars: int = 80000) -> str:
    parts = []
    preferred = [paper_path / "main.tex"]
    preferred.extend(sorted(paper_path.glob("sec*.tex")))
    preferred.extend(sorted(paper_path.glob("*.tex")))
    seen: set[Path] = set()
    for path in preferred:
        if path in seen or not path.exists() or path.name.endswith(".bak"):
            continue
        seen.add(path)
        try:
            parts.append(path.read_text(encoding="utf-8", errors="replace"))
        except Exception:
            continue
        if sum(len(p) for p in parts) >= max_chars:
            break
    return "\n\n".join(parts)[:max_chars]


def _bootstrap_scope_contract_from_paper(
    paper_path: Path, target_journal: str, main_paper_dir: str = ""
) -> tuple[bool, str]:
    """Create a deterministic no-Claude scope contract from existing source."""
    text = _read_stage_a_source_text(paper_path)
    if len(text.strip()) < 1000:
        return False, "paper source too small for scope bootstrap"

    title_match = re.search(r"\\title(?:\[[^\]]*\])?\{(.+?)\}",
                            text, re.DOTALL)
    title = _strip_tex_for_contract(title_match.group(1), 240) if title_match else paper_path.name
    abstract_match = re.search(
        r"\\begin\{abstract\}(.+?)\\end\{abstract\}",
        text, re.DOTALL | re.IGNORECASE,
    )
    abstract = (
        _strip_tex_for_contract(abstract_match.group(1), 900)
        if abstract_match else
        "The current manuscript source determines the article scope."
    )

    env_re = re.compile(
        r"\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}"
        r"(?:\[[^\]]*\])?(.+?)\\end\{\1\}",
        re.DOTALL | re.IGNORECASE,
    )
    theorem_items = []
    for kind, body in env_re.findall(text):
        item = f"{kind.title()}: {_strip_tex_for_contract(body, 520)}"
        if item not in theorem_items:
            theorem_items.append(item)
        if len(theorem_items) >= 12:
            break
    if not theorem_items:
        theorem_items = [
            "All theorem, proposition, lemma, definition, and proof "
            "interfaces already present in the manuscript source."
        ]

    bindings = []
    if main_paper_dir:
        bindings.append(
            "Main project interface: "
            f"{Path(main_paper_dir).name}; only use definitions, notation, "
            "and theorems that the current paper explicitly imports or needs."
        )
    else:
        bindings.append(
            "No separate main project directory configured; infer bindings "
            "from the manuscript source and local bibliography."
        )

    data = {
        "valid": True,
        "research_question": f"Establish the theorem chain of '{title}'. {abstract}",
        "target_journal_bar": (
            f"A submission to {target_journal} must have a coherent central "
            "scope, complete proofs for all in-scope claims, and notation "
            "compatible with the journal's standards."
        ),
        "main_project_bindings": bindings,
        "in_scope": [
            "The definitions, notation, constructions, and theorem statements "
            "already present in the manuscript.",
            "Any proof interfaces required to make the displayed theorem "
            "chain complete inside this article.",
        ],
        "must_prove_in_this_paper": theorem_items,
        "supporting_only": [
            "Background material and external literature may be used only as "
            "tools, references, or short context unless required by an "
            "in-scope proof."
        ],
        "out_of_scope": [
            "Results not needed for the article's central theorem chain; "
            "record strong such results as split-paper candidates."
        ],
        "split_policy": (
            "Do not weaken or delete the current article's central claims to "
            "pass review. Externalize only genuinely independent results."
        ),
        "failure_modes_to_control": [
            "naive truncation mistaken for an invariant",
            "unclosed proof interfaces",
            "scope creep into split-paper material",
            "local constructions that fail to glue globally",
            "finite-budget obstructions hidden as notation",
        ],
    }

    md = textwrap.dedent(f"""\
        # Scope Contract

        This contract was bootstrapped deterministically in `--no-claude`
        mode from the existing manuscript source.  It is a temporary but
        stable contract for Codex+ChatGPT testing until Claude supervision
        becomes available.

        ## Central Research Question

        {data["research_question"]}

        ## Target Journal Bar

        {data["target_journal_bar"]}

        ## Main Project Bindings

        {chr(10).join(f"- {x}" for x in data["main_project_bindings"])}

        ## In Scope

        {chr(10).join(f"- {x}" for x in data["in_scope"])}

        ## Must Prove In This Paper

        {chr(10).join(f"- {x}" for x in data["must_prove_in_this_paper"])}

        ## Supporting Only

        {chr(10).join(f"- {x}" for x in data["supporting_only"])}

        ## Out Of Scope

        {chr(10).join(f"- {x}" for x in data["out_of_scope"])}

        ## Split Policy

        {data["split_policy"]}

        ## Failure Modes To Control

        {chr(10).join(f"- {x}" for x in data["failure_modes_to_control"])}
    """)
    (paper_path / "scope_contract.md").write_text(md, encoding="utf-8")
    _write_json_artifact(paper_path, "scope_contract.json", data)
    return True, "bootstrapped from existing manuscript source"


def _deterministic_theorem_inventory(paper_path: Path) -> dict:
    """Lightweight theorem inventory for --no-claude smoke testing."""
    text = _read_stage_a_source_text(paper_path)
    env_re = re.compile(
        r"\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}"
        r"(?:\[[^\]]*\])?(.+?)\\end\{\1\}",
        re.DOTALL | re.IGNORECASE,
    )
    present = []
    for idx, (kind, body) in enumerate(env_re.findall(text), 1):
        present.append({
            "kind": kind.lower(),
            "index": idx,
            "statement": _strip_tex_for_contract(body, 700),
            "source": "deterministic_tex_inventory",
        })

    gap_patterns = (
        r"\bTODO\b",
        r"\bTBD\b",
        r"proof\s+(?:is\s+)?omitted",
        r"details\s+(?:are\s+)?omitted",
        r"we\s+omit\s+the\s+proof",
        r"left\s+to\s+the\s+reader",
        r"to\s+be\s+completed",
        r"we\s+leave\s+.*?(?:proof|verification|argument)",
    )
    proof_gaps = []
    for pat in gap_patterns:
        m = re.search(pat, text, re.IGNORECASE | re.DOTALL)
        if m:
            pos = m.start()
            proof_gaps.append({
                "pattern": pat,
                "context": _strip_tex_for_contract(text[max(0, pos - 180):pos + 240]),
            })
    if not present:
        missing = [{
            "reason": "No theorem-like environments were found by deterministic inventory.",
            "required_action": "create explicit theorem/proposition structure",
        }]
    else:
        missing = []

    return {
        "valid": True,
        "mode": "no_claude_deterministic_inventory",
        "in_scope_present": present,
        "missing_in_scope_results": missing,
        "weak_in_scope_core_results": [],
        "proof_gaps": proof_gaps,
        "supporting_appendix_or_background": [],
        "out_of_scope_strong_results": [],
        "split_candidates": [],
        "irrelevant_or_remove": [],
        "naive_truncation_risks": [
            {
                "reason": "Deterministic smoke-test inventory cannot certify "
                          "fold-aware descent; Oracle and later Claude review "
                          "must check cross-resolution claims."
            }
        ],
        "journal_style_gaps": [],
    }


def _deterministic_no_claude_stage_a_audit(
    state: PaperState, audit_round: int, paper_path: Path
) -> dict:
    inventory = _read_json_artifact(paper_path, "theorem_inventory.json")
    proof_gaps = _coerce_items(inventory.get("proof_gaps")) if inventory else []
    missing = _coerce_items(
        inventory.get("missing_in_scope_results")) if inventory else []
    blockers = []
    required_revisions = []
    metrics = {
        "theorem_completeness": 8,
        "proof_integrity": 8,
        "depth_novelty": 7,
        "scope_coverage": 8,
        "journal_fit": 7,
        "split_hygiene": 8,
    }
    if missing:
        metrics["theorem_completeness"] = 5
        blockers.extend(missing)
    if proof_gaps:
        metrics["proof_integrity"] = 6
        required_revisions.extend(proof_gaps)
    gate_pass = (
        not blockers
        and not required_revisions
        and all(metrics[k] >= v for k, v in STAGE_A_METRIC_THRESHOLDS.items())
    )
    return {
        "metrics": metrics,
        "verdict": "pass" if gate_pass else "revise",
        "audit_unparseable": False,
        "blockers": blockers,
        "required_revisions": required_revisions,
        "work_packages": [],
        "split_required": False,
        "split_reasons": [],
        "ready_for_oracle_review": gate_pass,
        "mode": "no_claude_deterministic_audit",
        "audit_round": audit_round,
        "note": (
            "Provisional Stage A smoke-test audit. Claude supervision must "
            "resume later before this is treated as final editorial approval."
        ),
    }


def _scope_contract_valid(paper_path: Path) -> tuple[bool, str]:
    md = paper_path / "scope_contract.md"
    if not md.exists():
        return False, "scope_contract.md missing"
    try:
        md_text = md.read_text(encoding="utf-8", errors="replace")
    except Exception as exc:
        return False, f"scope_contract.md unreadable: {exc}"
    if len(md_text.strip()) < 500:
        return False, "scope_contract.md too short"

    data = _read_json_artifact(paper_path, "scope_contract.json")
    required = (
        "research_question", "target_journal_bar",
        "main_project_bindings", "in_scope", "must_prove_in_this_paper",
        "supporting_only", "out_of_scope", "split_policy",
        "failure_modes_to_control",
    )
    if not data:
        return False, "scope_contract.json missing or invalid"
    if data.get("valid") is not True:
        return False, "scope_contract.json valid flag is not true"
    missing = [k for k in required if k not in data]
    if missing:
        return False, f"scope_contract.json missing keys: {missing}"
    if not _coerce_items(data.get("in_scope")):
        return False, "scope_contract.json has empty in_scope"
    if not _coerce_items(data.get("must_prove_in_this_paper")):
        return False, "scope_contract.json has empty must_prove_in_this_paper"
    return True, "ok"


def _inventory_valid(inventory: dict) -> tuple[bool, str]:
    required = (
        "in_scope_present", "missing_in_scope_results",
        "weak_in_scope_core_results", "proof_gaps",
        "supporting_appendix_or_background", "out_of_scope_strong_results",
        "split_candidates", "irrelevant_or_remove",
        "naive_truncation_risks", "journal_style_gaps",
    )
    if not inventory:
        return False, "theorem_inventory.json missing or unparseable"
    if inventory.get("valid") is not True:
        return False, "inventory valid flag is not true"
    missing = [k for k in required if k not in inventory]
    if missing:
        return False, f"inventory missing keys: {missing}"
    return True, "ok"


def _inventory_action(inventory: dict) -> tuple[str, list]:
    ordered = (
        ("missing_in_scope_results", "missing_in_scope_results"),
        ("weak_in_scope_core_results", "weak_in_scope_core_results"),
        ("proof_gaps", "proof_gaps"),
    )
    for action, key in ordered:
        items = _coerce_items(inventory.get(key))
        if items:
            return action, items

    split_items = (
        _coerce_items(inventory.get("out_of_scope_strong_results"))
        + _coerce_items(inventory.get("split_candidates"))
    )
    if split_items:
        return "split_candidates", split_items

    return "", []


def _metric_int(value) -> int:
    try:
        return max(0, min(10, int(round(float(value)))))
    except Exception:
        return 0


def _audit_metrics(data: dict, keys=None) -> dict[str, int]:
    raw = data.get("metrics", {}) if isinstance(data, dict) else {}
    if not isinstance(raw, dict):
        return {}
    wanted = tuple(keys or STAGE_A_METRIC_THRESHOLDS.keys())
    return {k: _metric_int(raw.get(k, 0)) for k in wanted if k in raw}


def _combine_stage_a_audits(codex_data: dict, claude_data: dict) -> dict:
    missing = []
    structural_auditor = "claude" if CLAUDE_ENABLED else "structural_fallback"
    codex_metrics = _audit_metrics(codex_data, STAGE_A_CODEX_MATH_METRICS)
    claude_metrics = _audit_metrics(
        claude_data, STAGE_A_CLAUDE_STRUCTURAL_METRICS)
    if set(codex_metrics) != set(STAGE_A_CODEX_MATH_METRICS):
        missing.append("codex_math")
    if set(claude_metrics) != set(STAGE_A_CLAUDE_STRUCTURAL_METRICS):
        missing.append(
            "claude_structural" if CLAUDE_ENABLED else "structural_fallback")

    combined_metrics: dict[str, int] = {
        **codex_metrics,
        **claude_metrics,
    }

    blockers = []
    required_revisions = []
    work_packages = []
    split_reasons = []
    split_required = False
    all_pass = not missing
    for name, data in (("codex", codex_data),
                       (structural_auditor, claude_data)):
        verdict = str(data.get("verdict", "")).lower()
        if verdict != "pass":
            all_pass = False
        for item in _coerce_items(data.get("blockers")):
            blockers.append({"auditor": name, **item}
                            if isinstance(item, dict)
                            else {"auditor": name, "reason": str(item)})
        for item in _coerce_items(data.get("required_revisions")):
            required_revisions.append({"auditor": name, **item}
                                      if isinstance(item, dict)
                                      else {"auditor": name, "reason": str(item)})
        for item in _coerce_items(data.get("work_packages")):
            work_packages.append({"auditor": name, **item}
                                 if isinstance(item, dict)
                                 else {"auditor": name, "task": str(item)})
        if bool(data.get("split_required")):
            split_required = True
        for item in _coerce_items(data.get("split_reasons")):
            split_reasons.append({"auditor": name, **item}
                                 if isinstance(item, dict)
                                 else {"auditor": name, "reason": str(item)})

    for name in missing:
        blockers.append({
            "auditor": name,
            "reason": "audit JSON was empty or missing required metrics",
        })
        all_pass = False

    threshold_pass = bool(combined_metrics) and all(
        combined_metrics.get(k, 0) >= v
        for k, v in STAGE_A_METRIC_THRESHOLDS.items()
    )
    gate_pass = (
        all_pass
        and threshold_pass
        and not blockers
        and not split_required
    )

    return {
        "metrics": combined_metrics,
        "verdict": "pass" if gate_pass else "revise",
        "audit_unparseable": bool(missing),
        "blockers": blockers,
        "required_revisions": required_revisions,
        "work_packages": work_packages,
        "split_required": split_required,
        "split_reasons": split_reasons,
        "ready_for_oracle_review": gate_pass,
        "codex": codex_data,
        "claude": claude_data,
    }


def stage_a_audit_passes(audit: dict) -> bool:
    if not audit or not isinstance(audit, dict):
        return False
    metrics = audit.get("metrics", {})
    if not isinstance(metrics, dict) or not metrics:
        return False
    if audit.get("verdict") != "pass":
        return False
    if audit.get("audit_unparseable"):
        return False
    if audit.get("blockers"):
        return False
    if audit.get("split_required"):
        return False
    if not audit.get("ready_for_oracle_review"):
        return False
    return all(
        _metric_int(metrics.get(k, 0)) >= v
        for k, v in STAGE_A_METRIC_THRESHOLDS.items()
    )


def stage_a_ready_for_b(state: PaperState) -> bool:
    if state.stage_a_audit_metrics.get("mode") == "no_claude_deterministic_audit":
        return False
    return bool(state.stage_a_passed
                and stage_a_audit_passes(state.stage_a_audit_metrics))


def _stage_a_audit_has_actionable_issues(audit: dict) -> bool:
    return bool(
        audit.get("blockers")
        or audit.get("required_revisions")
        or audit.get("work_packages")
        or audit.get("split_required")
        or audit.get("split_reasons")
    )


def _stage_a_score_from_audit(audit: dict) -> int:
    metrics = audit.get("metrics", {}) if isinstance(audit, dict) else {}
    vals = [_metric_int(metrics.get(k, 0)) for k in STAGE_A_METRIC_THRESHOLDS]
    return min(vals) if vals else 0


def _stage_a_block(state: PaperState, reason: str, *,
                   dry_run: bool = False, tag: str = "") -> bool:
    state.stage_a_passed = False
    state.error = f"Stage A blocked: {reason}"
    logger.error(f"{tag} {state.error}")
    state.log_event("A", "blocked", detail=reason)
    if not dry_run:
        update_program_board(state.paper_name, "A-BLOCKED", reason[:120])
    save_state(state)
    return False


def _stage_a_pause(state: PaperState, reason: str, *,
                   tag: str = "") -> bool:
    """Pause for infrastructure/tooling issues without blaming the paper."""
    state.stage_a_passed = False
    state.error = f"Stage A paused: {reason}"
    logger.error(f"{tag} {state.error}")
    state.log_event("A", "paused", detail=reason)
    save_state(state)
    return False


def _run_stage_a_inventory(state: PaperState, *,
                           model: Optional[str] = None,
                           dry_run: bool = False,
                           tag: str = "") -> dict:
    paper_path = Path(state.paper_dir)
    if dry_run:
        inventory = {
            "valid": True,
            "in_scope_present": [],
            "missing_in_scope_results": [],
            "weak_in_scope_core_results": [],
            "proof_gaps": [],
            "supporting_appendix_or_background": [],
            "out_of_scope_strong_results": [],
            "split_candidates": [],
            "irrelevant_or_remove": [],
            "naive_truncation_risks": [],
            "journal_style_gaps": [],
        }
    else:
        for stale_name in ("theorem_inventory.json", "theorem_inventory.md"):
            try:
                (paper_path / stale_name).unlink(missing_ok=True)
            except Exception:
                pass
        prompt = build_theorem_inventory_prompt(
            state.paper_dir, state.target_journal, state.main_paper_dir)
        out = codex_exec(prompt, work_dir=paper_path, timeout_seconds=1800,
                         model=model, dry_run=dry_run,
                         context_mode="scope_bound_review",
                         agent_role="stage_a_theorem_inventory")
        inventory = _read_json_artifact(paper_path, "theorem_inventory.json")
        if not inventory:
            inventory = parse_json_from_output(out)
            if inventory:
                _write_json_artifact(paper_path, "theorem_inventory.json",
                                     inventory)

    valid, reason = _inventory_valid(inventory)
    state.stage_a_inventory = inventory if valid else {}
    state.log_event("A", "theorem_inventory",
                    detail=reason if not valid else json.dumps(
                        {k: len(_coerce_items(inventory.get(k)))
                         for k in inventory
                         if isinstance(inventory.get(k), list)},
                        ensure_ascii=False))
    save_state(state)
    if not valid:
        logger.error(f"{tag} A1 inventory invalid: {reason}")
        return {}
    ledger_items = []
    for category in ("out_of_scope_strong_results", "split_candidates"):
        for item in _coerce_items(inventory.get(category)):
            item_copy = dict(item) if isinstance(item, dict) else {"reason": str(item)}
            item_copy["ledger_category"] = category
            ledger_items.append(item_copy)
    _record_research_ledger_items(state, "stage_a_inventory", ledger_items)
    return inventory


def _run_stage_a_audit_once(state: PaperState, audit_round: int, *,
                            model: Optional[str] = None,
                            dry_run: bool = False,
                            tag: str = "") -> dict:
    paper_path = Path(state.paper_dir)
    use_deterministic_no_claude_audit = False
    if use_deterministic_no_claude_audit and not CLAUDE_ENABLED and not dry_run:
        logger.info(f"{tag} A3 audit round {audit_round}: "
                    "deterministic --no-claude smoke audit")
        audit = _deterministic_no_claude_stage_a_audit(
            state, audit_round, paper_path)
        _write_json_artifact(paper_path, "stage_a_audit.json", audit)
        state.stage_a_audit_metrics = audit
        state.stage_a_audit_rounds = audit_round
        score = _stage_a_score_from_audit(audit)
        state.stage_a_scores.append(score)
        state.log_event("A", "stage_a_audit", round_num=audit_round,
                        score=score, verdict=audit.get("verdict", ""),
                        detail=json.dumps(audit,
                                          ensure_ascii=False)[:15000])
        save_state(state)
        return audit

    audit_label = (
        "Codex math + Claude structural"
        if CLAUDE_ENABLED or dry_run
        else "Codex math + Codex structural fallback (--no-claude)"
    )
    logger.info(f"{tag} A3 audit round {audit_round}: {audit_label}")

    def _codex_audit() -> dict:
        prompt = build_stage_a_audit_prompt(
            state.paper_dir, state.target_journal, audit_round)
        for attempt in range(1, 3):
            out = codex_exec(prompt, work_dir=paper_path,
                             timeout_seconds=900, model=model,
                             dry_run=dry_run,
                             context_mode="scope_bound_review",
                             agent_role="stage_a_codex_math_audit")
            data = parse_json_from_output(out) if not dry_run else {
                "metrics": {k: 8 for k in STAGE_A_CODEX_MATH_METRICS},
                "verdict": "pass",
                "blockers": [],
                "required_revisions": [],
                "split_required": False,
                "split_reasons": [],
                "ready_for_oracle_review": True,
            }
            if set(_audit_metrics(data, STAGE_A_CODEX_MATH_METRICS)) == set(
                STAGE_A_CODEX_MATH_METRICS
            ):
                return data
            logger.warning(f"{tag} Codex math audit attempt {attempt} "
                           f"empty/unparseable, retrying")
        return {}

    def _claude_audit() -> dict:
        prompt = build_claude_stage_a_structural_audit_prompt(
            state.paper_dir, state.target_journal, audit_round)
        for attempt in range(1, 3):
            if not CLAUDE_ENABLED and not dry_run:
                out = codex_exec(
                    prompt + textwrap.dedent("""\

                    Claude is unavailable and the pipeline is running in
                    --no-claude test mode. Act only as a temporary structural
                    auditor for this smoke test. Preserve the same JSON schema;
                    do not edit files and do not claim independent Claude
                    approval.
                    """),
                    work_dir=paper_path, timeout_seconds=900,
                    model=model, dry_run=dry_run,
                    context_mode="scope_bound_review",
                    agent_role="stage_a_structural_audit_fallback")
            else:
                out = claude_exec(prompt, work_dir=paper_path,
                                  timeout_seconds=900, dry_run=dry_run,
                                  context_mode="scope_bound_review",
                                  agent_role="stage_a_claude_structural_audit")
            data = parse_json_from_output(out) if not dry_run else {
                "metrics": {k: 8 for k in STAGE_A_CLAUDE_STRUCTURAL_METRICS},
                "verdict": "pass",
                "blockers": [],
                "required_revisions": [],
                "work_packages": [],
                "split_required": False,
                "split_reasons": [],
                "ready_for_oracle_review": True,
            }
            if set(_audit_metrics(
                data, STAGE_A_CLAUDE_STRUCTURAL_METRICS
            )) == set(STAGE_A_CLAUDE_STRUCTURAL_METRICS):
                return data
            auditor_label = (
                "Claude structural audit"
                if CLAUDE_ENABLED or dry_run
                else "Structural audit fallback"
            )
            logger.warning(f"{tag} {auditor_label} attempt {attempt} "
                           f"empty/unparseable, retrying")
        return {}

    with ThreadPoolExecutor(max_workers=2) as ex:
        f_codex = ex.submit(_codex_audit)
        f_claude = ex.submit(_claude_audit)
        codex_data = f_codex.result()
        claude_data = f_claude.result()

    supervision_phase = (
        f"stage_a_structural_audit_R{audit_round}"
        if CLAUDE_ENABLED
        else f"stage_a_structural_audit_codex_fallback_R{audit_round}"
    )
    _record_claude_supervision(
        state, supervision_phase, claude_data,
        context_mode="scope_bound_review",
        agent_role=(
            "stage_a_claude_structural_audit"
            if CLAUDE_ENABLED
            else "stage_a_structural_audit_fallback"
        ))
    audit = _combine_stage_a_audits(codex_data, claude_data)
    if not dry_run:
        _write_json_artifact(paper_path, "stage_a_audit.json", audit)
    state.stage_a_audit_metrics = audit
    state.stage_a_audit_rounds = audit_round
    score = _stage_a_score_from_audit(audit)
    state.stage_a_scores.append(score)
    state.log_event("A", "stage_a_audit", round_num=audit_round,
                    score=score, verdict=audit.get("verdict", ""),
                    detail=json.dumps(audit, ensure_ascii=False)[:15000])
    save_state(state)
    return audit


def run_stage_a(state: PaperState, *, dry_run: bool = False,
                model: Optional[str] = None) -> bool:
    tag = f"[{state.paper_name}|A]"
    paper_path = Path(state.paper_dir)

    # Snapshot theorems at Stage A start for content change summary
    _stage_a_pre_theorems = extract_theorem_statements(paper_path)

    # Old state files may contain Stage A rounds reconstructed from git but no
    # actual score/audit evidence.  Treat that as stale bookkeeping and rerun A.
    if (state.stage_a_rounds
        and not _state_has_stage_a_evidence(state)):
        logger.warning(f"{tag} Resetting stale Stage A round counter "
                       f"({state.stage_a_rounds}) with no score/audit state")
        state.stage_a_rounds = 0
        state.current_round = 0
        save_state(state)

    if not state.stage_a_passed and state.stage_a_audit_rounds:
        logger.warning(f"{tag} Resetting stale Stage A audit counters before "
                       "fresh audit rerun")
        state.stage_a_audit_rounds = 0
        state.stage_a_audit_metrics = {}
        state.stage_a_scores = []
        save_state(state)

    if state.stage_a_passed and not stage_a_ready_for_b(state):
        logger.warning(f"{tag} Clearing legacy Stage A pass without audit gate")
        state.stage_a_passed = False
        if state.stage_a_audit_metrics.get("mode") == "no_claude_deterministic_audit":
            logger.warning(f"{tag} Resetting deterministic Stage A audit "
                           "state before Codex audit rerun")
            state.stage_a_audit_rounds = 0
            state.stage_a_audit_metrics = {}
            state.stage_a_scores = []
        save_state(state)

    _ensure_research_directive(paper_path, state.target_journal,
                               dry_run=dry_run)

    # ── A0: Scope contract (one-shot, no theorem demotion) ─────────
    scope_ok, scope_reason = _scope_contract_valid(paper_path)
    if not state.stage_a_scope_done or not scope_ok:
        if CLAUDE_ENABLED:
            logger.info(f"{tag} A0-C — Claude supervisory scope brief")
        else:
            logger.info(f"{tag} A0-S — Codex scope seed (--no-claude)")
        if dry_run:
            claude_scope_data = {
                "valid": True,
                "supervision_phase": "scope_brief",
                "paper_role": "dry-run",
                "central_scope": "dry-run",
                "must_preserve": [],
                "project_bindings": [],
                "must_include_or_deepen": [],
                "supporting_only": [],
                "split_candidates_to_track": [],
                "language_structure_risks": [],
                "bad_example_mechanisms_to_track": [],
                "human_decisions": [],
                "codex_a0_instructions": [],
            }
            claude_scope_out = ""
        elif not CLAUDE_ENABLED:
            claude_scope_data = {
                "valid": True,
                "supervision_phase": "scope_brief",
                "supervision_mode": "codex_chatgpt_test",
                "paper_role": "pending Codex scope contract",
                "central_scope": "Use Codex A0 to derive the scope contract "
                                 "from the paper and main-paper context.",
                "must_preserve": [],
                "project_bindings": [],
                "must_include_or_deepen": [],
                "supporting_only": [],
                "split_candidates_to_track": [],
                "language_structure_risks": [],
                "bad_example_mechanisms_to_track": [],
                "human_decisions": [],
                "codex_a0_instructions": [
                    "Claude is unavailable in --no-claude test mode.",
                    "Build scope_contract.md/json directly from the paper, "
                    "the main-paper interface, and the research directive.",
                    "Do not demote theorem scope merely to pass the gate.",
                ],
            }
            claude_scope_out = ""
        else:
            claude_scope_prompt = build_claude_scope_brief_prompt(
                state.paper_dir, state.target_journal,
                state.main_paper_dir)
            claude_scope_out = claude_exec(
                claude_scope_prompt, work_dir=paper_path,
                timeout_seconds=900, dry_run=dry_run,
                context_mode="contextual_supervision",
                agent_role="stage_a_scope_brief")
            claude_scope_data = parse_json_from_output(claude_scope_out)
            if not claude_scope_data:
                return _stage_a_pause(
                    state, "Claude scope brief missing or unparseable",
                    tag=tag)
        _record_claude_supervision(
            state, "stage_a_scope_brief", claude_scope_data,
            raw=claude_scope_out,
            context_mode="contextual_supervision",
            agent_role="stage_a_scope_brief")
        save_state(state)

        if dry_run:
            state.stage_a_scope_done = True
            scope_ok, scope_reason = True, "dry-run"
        elif not CLAUDE_ENABLED:
            logger.info(f"{tag} A0-B — bootstrap scope contract "
                        "from existing manuscript (--no-claude)")
            scope_ok, scope_reason = _bootstrap_scope_contract_from_paper(
                paper_path, state.target_journal, state.main_paper_dir)
            state.stage_a_scope_done = scope_ok
        else:
            logger.info(f"{tag} A0 — Codex scope contract from Claude brief")
            claude_scope_json = json.dumps(
                claude_scope_data, indent=2, ensure_ascii=False)
            prompt_a0 = build_scope_contract_prompt(
                state.paper_dir, state.target_journal, state.main_paper_dir,
                claude_scope_brief=claude_scope_json)
            out = codex_exec(prompt_a0, work_dir=paper_path,
                             timeout_seconds=2400, model=model,
                             dry_run=dry_run,
                             context_mode="contextual_execution",
                             agent_role="stage_a_scope_contract")
            # If the model returned JSON but forgot the file, persist the JSON
            # artifact so the gate can inspect it.
            data = _read_json_artifact(paper_path, "scope_contract.json")
            if not data:
                data = parse_json_from_output(out)
                if data:
                    _write_json_artifact(paper_path, "scope_contract.json",
                                         data)
            scope_ok, scope_reason = _scope_contract_valid(paper_path)
            state.stage_a_scope_done = scope_ok
        state.log_event("A", "scope_contract", detail=scope_reason)
        save_state(state)
        if not scope_ok:
            return _stage_a_block(state, scope_reason, dry_run=dry_run,
                                  tag=tag)

    for rnd in range(state.stage_a_rounds + 1, MAX_STAGE_A_ROUNDS + 1):
        state.stage_a_rounds = rnd
        state.current_round = rnd
        save_state(state)

        logger.info(f"{tag} Round {rnd}: A1 — theorem inventory")
        inventory = _run_stage_a_inventory(
            state, model=model, dry_run=dry_run, tag=tag)
        if not inventory:
            return _stage_a_pause(state, "theorem_inventory_invalid",
                                  tag=tag)

        action, items = _inventory_action(inventory)

        if action in (
            "missing_in_scope_results",
            "weak_in_scope_core_results",
            "proof_gaps",
        ):
            logger.info(f"{tag} Round {rnd}: A2 — {action} "
                        f"({len(items)} item(s))")
            issues_json = json.dumps(items[:12], indent=2,
                                     ensure_ascii=False)
            prompt = build_theoremization_prompt(
                state.paper_dir, state.target_journal, action, issues_json,
                rnd)
            pre_theorems = extract_theorem_statements(paper_path)
            edit_snapshot = _snapshot_paper_sources(paper_path)
            codex_out = codex_exec(
                prompt, work_dir=paper_path,
                timeout_seconds=3600, model=model, dry_run=dry_run,
                context_mode="contextual_execution",
                agent_role="stage_a_theoremization")
            compiled = compile_gate(paper_path, model=model,
                                    dry_run=dry_run, tag=f"{tag} A2")
            if not compiled:
                _restore_paper_sources_snapshot(paper_path, edit_snapshot)
                state.log_event("A", "compile_failed", round_num=rnd,
                                detail=f"after A2 action={action}")
                save_state(state)
                return _stage_a_pause(
                    state, f"compile_failed_after_{action}", tag=tag)

            detail = f"{action}; {len(items)} item(s); compiled={compiled}"
            if (not dry_run
                and action in ("missing_in_scope_results",
                               "weak_in_scope_core_results")):
                substantive, reason = verify_substantive_change(
                    paper_path, pre_theorems)
                state.log_event("A", "substance_check", round_num=rnd,
                                detail=reason)
                if not substantive:
                    _restore_paper_sources_snapshot(paper_path, edit_snapshot)
                    save_state(state)
                    if not str(codex_out).strip():
                        return _stage_a_pause(
                            state,
                            f"codex_empty_after_{action}",
                            tag=tag)
                    return _stage_a_block(
                        state,
                        f"A2 produced no substantive theorem change: {reason}",
                        dry_run=dry_run, tag=tag)

            h = git_commit(paper_path, f"stage-A R{rnd}: {action}",
                           tag=tag)
            state.stage_a_audit_rounds = 0
            state.stage_a_audit_metrics = {}
            state.log_event("A", "theoremization", round_num=rnd,
                            committed=bool(h), commit_hash=h,
                            detail=detail)
            save_state(state)

            if action in ("missing_in_scope_results",
                          "weak_in_scope_core_results"):
                run_stage_a_dedup(state, round_num=rnd, model=model,
                                  dry_run=dry_run, tag=tag)
                h2 = git_commit(paper_path,
                                f"stage-A R{rnd}: cross-paper dedup",
                                tag=tag)
                if h2:
                    state.log_event("A", "cross_paper_dedup_commit",
                                    round_num=rnd, committed=True,
                                    commit_hash=h2)
                    save_state(state)
            continue

        if action == "split_candidates":
            logger.info(f"{tag} Round {rnd}: A-SPLIT — "
                        f"{len(items)} candidate(s)")
            candidates_json = json.dumps(items[:15], indent=2,
                                         ensure_ascii=False)
            prompt = build_split_hygiene_prompt(
                state.paper_dir, state.target_journal, candidates_json, rnd)
            edit_snapshot = _snapshot_paper_sources(paper_path)
            codex_exec(prompt, work_dir=paper_path,
                       timeout_seconds=2400, model=model, dry_run=dry_run,
                       context_mode="contextual_execution",
                       agent_role="stage_a_split_hygiene")
            compiled = compile_gate(paper_path, model=model,
                                    dry_run=dry_run, tag=f"{tag} A-SPLIT")
            if not compiled:
                _restore_paper_sources_snapshot(paper_path, edit_snapshot)
                state.log_event("A", "compile_failed", round_num=rnd,
                                detail="after A-SPLIT")
                save_state(state)
                return _stage_a_pause(
                    state, "compile_failed_after_split_hygiene", tag=tag)
            split_data = _read_json_artifact(paper_path,
                                             "split_candidates.json")
            state.stage_a_split_candidates = _coerce_items(
                split_data.get("candidates", []))
            ledger_items = []
            for item in state.stage_a_split_candidates:
                item_copy = dict(item) if isinstance(item, dict) else {
                    "reason": str(item)
                }
                item_copy["ledger_category"] = "split_hygiene_candidate"
                ledger_items.append(item_copy)
            _record_research_ledger_items(
                state, "stage_a_split_hygiene", ledger_items)
            h = git_commit(paper_path, f"stage-A R{rnd}: split hygiene",
                           tag=tag)
            state.stage_a_audit_rounds = 0
            state.stage_a_audit_metrics = {}
            state.log_event("A", "split_hygiene", round_num=rnd,
                            committed=bool(h), commit_hash=h,
                            detail=f"{len(items)} candidate(s); "
                                   f"compiled={compiled}")
            save_state(state)
            continue

        logger.info(f"{tag} Round {rnd}: A3 — audit gate")
        while state.stage_a_audit_rounds < MAX_STAGE_A_AUDIT_ROUNDS:
            audit_round = state.stage_a_audit_rounds + 1
            audit = _run_stage_a_audit_once(
                state, audit_round, model=model, dry_run=dry_run, tag=tag)
            score = _stage_a_score_from_audit(audit)
            logger.info(f"{tag} A3 audit round {audit_round}: "
                        f"score={score}, verdict={audit.get('verdict')}")

            if stage_a_audit_passes(audit):
                if audit_round < MIN_STAGE_A_AUDIT_ROUNDS:
                    logger.info(f"{tag} A3 pass but needs "
                                f"{MIN_STAGE_A_AUDIT_ROUNDS} audit rounds; "
                                f"running another audit")
                    continue
                compile_snapshot = _snapshot_paper_sources(paper_path)
                compiled_pass = compile_gate(paper_path, model=model,
                                             dry_run=dry_run,
                                             tag=f"{tag} A3-PASS")
                if not compiled_pass:
                    _restore_paper_sources_snapshot(paper_path,
                                                    compile_snapshot)
                    state.log_event("A", "compile_failed",
                                    round_num=audit_round,
                                    detail="before Stage A audit pass")
                    save_state(state)
                    return _stage_a_pause(
                        state, "compile_failed_before_stage_a_pass",
                        tag=tag)
                content_summary = summarize_content_changes(
                    paper_path, _stage_a_pre_theorems)
                h = git_commit(
                    paper_path,
                    f"Stage A audit-pass ({score}/10, {rnd}R): "
                    f"{content_summary}",
                    tag=tag)
                if not dry_run:
                    update_program_board(
                        state.paper_name, "A-DONE",
                        f"audit {score}/10, {rnd} rounds, "
                        f"{audit_round} A3")
                state.stage_a_passed = True
                state.error = ""
                state.log_event("A", "audit_gate_passed",
                                round_num=audit_round, score=score,
                                committed=bool(h), commit_hash=h,
                                detail=json.dumps(
                                    {
                                        "metrics": audit.get("metrics", {}),
                                        "compiled": compiled_pass,
                                    },
                                    ensure_ascii=False))
                save_state(state)
                return True

            actionable = _stage_a_audit_has_actionable_issues(audit)
            if audit.get("audit_unparseable") and not actionable:
                return _stage_a_pause(state, "stage_a_audit_unparseable",
                                      tag=tag)

            if actionable:
                issues = {
                    "audit_round": audit_round,
                    "metrics": audit.get("metrics", {}),
                    "blockers": audit.get("blockers", []),
                    "required_revisions": audit.get("required_revisions", []),
                    "work_packages": audit.get("work_packages", []),
                    "split_required": audit.get("split_required", False),
                    "split_reasons": audit.get("split_reasons", []),
                }
                logger.info(f"{tag} A3 failed; returning to A2 revision")
                prompt = build_theoremization_prompt(
                    state.paper_dir, state.target_journal, "audit_blockers",
                    json.dumps(issues, indent=2, ensure_ascii=False), rnd)
                edit_snapshot = _snapshot_paper_sources(paper_path)
                codex_exec(prompt, work_dir=paper_path,
                           timeout_seconds=3600, model=model,
                           dry_run=dry_run,
                           context_mode="contextual_execution",
                           agent_role="stage_a_audit_blocker_revision")
                compiled = compile_gate(paper_path, model=model,
                                        dry_run=dry_run,
                                        tag=f"{tag} A2-AUDIT")
                if not compiled:
                    _restore_paper_sources_snapshot(paper_path, edit_snapshot)
                    state.log_event("A", "compile_failed", round_num=rnd,
                                    detail="after A2 audit blocker revision")
                    save_state(state)
                    return _stage_a_pause(
                        state, "compile_failed_after_audit_blocker_revision",
                        tag=tag)
                h = git_commit(paper_path,
                               f"stage-A R{rnd}: audit blocker revision",
                               tag=tag)
                state.stage_a_audit_rounds = 0
                state.stage_a_audit_metrics = {}
                state.log_event("A", "audit_blocker_revision",
                                round_num=rnd, committed=bool(h),
                                commit_hash=h,
                                detail=f"compiled={compiled}; "
                                       f"score={score}")
                save_state(state)
                break

            return _stage_a_block(state, "stage_a_audit_failed_without_plan",
                                  dry_run=dry_run, tag=tag)

        else:
            return _stage_a_block(state, "stage_a_audit_failed_max_rounds",
                                  dry_run=dry_run, tag=tag)

    if state.stage_a_rounds >= MAX_STAGE_A_ROUNDS:
        logger.info(f"{tag} A3-FINAL — max theoremization rounds reached; "
                    "running final audit before blocking")
        while state.stage_a_audit_rounds < MAX_STAGE_A_AUDIT_ROUNDS:
            audit_round = state.stage_a_audit_rounds + 1
            audit = _run_stage_a_audit_once(
                state, audit_round, model=model, dry_run=dry_run, tag=tag)
            score = _stage_a_score_from_audit(audit)
            logger.info(f"{tag} A3 final audit round {audit_round}: "
                        f"score={score}, verdict={audit.get('verdict')}")

            if stage_a_audit_passes(audit):
                if audit_round < MIN_STAGE_A_AUDIT_ROUNDS:
                    logger.info(f"{tag} A3 final pass but needs "
                                f"{MIN_STAGE_A_AUDIT_ROUNDS} audit rounds; "
                                "running another audit")
                    continue
                compile_snapshot = _snapshot_paper_sources(paper_path)
                compiled_pass = compile_gate(paper_path, model=model,
                                             dry_run=dry_run,
                                             tag=f"{tag} A3-FINAL-PASS")
                if not compiled_pass:
                    _restore_paper_sources_snapshot(paper_path,
                                                    compile_snapshot)
                    state.log_event("A", "compile_failed",
                                    round_num=audit_round,
                                    detail="before final Stage A audit pass")
                    save_state(state)
                    return _stage_a_pause(
                        state, "compile_failed_before_final_stage_a_pass",
                        tag=tag)
                content_summary = summarize_content_changes(
                    paper_path, _stage_a_pre_theorems)
                h = git_commit(
                    paper_path,
                    f"Stage A audit-pass ({score}/10, "
                    f"{state.stage_a_rounds}R): {content_summary}",
                    tag=tag)
                if not dry_run:
                    update_program_board(
                        state.paper_name, "A-DONE",
                        f"audit {score}/10, {state.stage_a_rounds} rounds, "
                        f"{audit_round} final A3")
                state.stage_a_passed = True
                state.error = ""
                state.log_event("A", "audit_gate_passed",
                                round_num=audit_round, score=score,
                                committed=bool(h), commit_hash=h,
                                detail=json.dumps(
                                    {
                                        "metrics": audit.get("metrics", {}),
                                        "compiled": compiled_pass,
                                        "final_after_max_rounds": True,
                                    },
                                    ensure_ascii=False))
                save_state(state)
                return True

            actionable = _stage_a_audit_has_actionable_issues(audit)
            if audit.get("audit_unparseable") and not actionable:
                return _stage_a_pause(state, "stage_a_final_audit_unparseable",
                                      tag=tag)

            if actionable:
                detail = json.dumps(
                    {
                        "score": score,
                        "metrics": audit.get("metrics", {}),
                        "blockers": audit.get("blockers", []),
                        "required_revisions": audit.get(
                            "required_revisions", []),
                        "work_packages": audit.get("work_packages", []),
                        "split_required": audit.get("split_required", False),
                        "split_reasons": audit.get("split_reasons", []),
                    },
                    ensure_ascii=False,
                )[:8000]
                state.log_event("A", "final_audit_failed_after_max_rounds",
                                round_num=audit_round, score=score,
                                detail=detail)
                save_state(state)
                final_repair_count = max(
                    0, state.stage_a_rounds - MAX_STAGE_A_ROUNDS)
                if final_repair_count < MAX_STAGE_A_FINAL_REPAIR_ROUNDS:
                    repair_round = state.stage_a_rounds + 1
                    issues = {
                        "audit_round": audit_round,
                        "final_repair_round": final_repair_count + 1,
                        "max_final_repair_rounds":
                            MAX_STAGE_A_FINAL_REPAIR_ROUNDS,
                        "metrics": audit.get("metrics", {}),
                        "blockers": audit.get("blockers", []),
                        "required_revisions": audit.get(
                            "required_revisions", []),
                        "work_packages": audit.get("work_packages", []),
                        "split_required": audit.get("split_required", False),
                        "split_reasons": audit.get("split_reasons", []),
                    }
                    logger.info(
                        f"{tag} A3-FINAL failed; running final repair "
                        f"round {repair_round} "
                        f"({final_repair_count + 1}/"
                        f"{MAX_STAGE_A_FINAL_REPAIR_ROUNDS})")
                    prompt = build_theoremization_prompt(
                        state.paper_dir, state.target_journal,
                        "final_audit_repair",
                        json.dumps(issues, indent=2, ensure_ascii=False),
                        repair_round)
                    edit_snapshot = _snapshot_paper_sources(paper_path)
                    codex_exec(prompt, work_dir=paper_path,
                               timeout_seconds=3600, model=model,
                               dry_run=dry_run,
                               context_mode="contextual_execution",
                               agent_role="stage_a_final_audit_repair")
                    compiled = compile_gate(
                        paper_path, model=model, dry_run=dry_run,
                        tag=f"{tag} A3-FINAL-REPAIR")
                    if not compiled:
                        _restore_paper_sources_snapshot(
                            paper_path, edit_snapshot)
                        state.log_event(
                            "A", "compile_failed",
                            round_num=repair_round,
                            detail="after final Stage A audit repair")
                        save_state(state)
                        return _stage_a_pause(
                            state,
                            "compile_failed_after_final_audit_repair",
                            tag=tag)
                    h = git_commit(
                        paper_path,
                        f"stage-A R{repair_round}: final audit repair",
                        tag=tag)
                    state.stage_a_rounds = repair_round
                    state.current_round = repair_round
                    state.stage_a_audit_rounds = 0
                    state.stage_a_audit_metrics = {}
                    state.log_event(
                        "A", "final_audit_repair",
                        round_num=repair_round, committed=bool(h),
                        commit_hash=h,
                        detail=f"compiled={compiled}; prior_score={score}; "
                               f"repair={final_repair_count + 1}/"
                               f"{MAX_STAGE_A_FINAL_REPAIR_ROUNDS}")
                    save_state(state)
                    return run_stage_a(
                        state, dry_run=dry_run, model=model)
                return _stage_a_block(
                    state,
                    f"max Stage A rounds exhausted; final audit failed "
                    f"(score={score})",
                    dry_run=dry_run, tag=tag)

            return _stage_a_block(
                state,
                "max Stage A rounds exhausted; final audit failed without plan",
                dry_run=dry_run, tag=tag)

        return _stage_a_block(
            state,
            "max Stage A rounds exhausted; final audit failed max audit rounds",
            dry_run=dry_run, tag=tag)

    return _stage_a_block(
        state,
        f"max Stage A theoremization rounds exhausted ({MAX_STAGE_A_ROUNDS})",
        dry_run=dry_run,
        tag=tag)


# ═══════════════════════════════════════════════════════════════════════════
# STAGE B: Oracle Review (minor-revision-gated loop)
# ═══════════════════════════════════════════════════════════════════════════

def run_stage_b(state: PaperState, *, dry_run: bool = False,
                model: Optional[str] = None,
                oracle_timeout: int = 7200) -> bool:
    tag = f"[{state.paper_name}|B]"
    paper_path = Path(state.paper_dir)

    if not stage_a_ready_for_b(state):
        reason = "missing Stage A audit pass; rerun Stage A"
        state.current_stage = "A"
        state.stage_a_passed = False
        state.error = f"Stage B blocked: {reason}"
        logger.error(f"{tag} {state.error}")
        state.log_event("B", "pre_b_gate_blocked", detail=reason)
        if not dry_run:
            update_program_board(state.paper_name, "A-BLOCKED", reason)
        save_state(state)
        return False

    # Track consecutive non-pass rounds for deep mode escalation
    consecutive_nonpass = 0
    # Count how many verdicts at end of existing list are non-pass (resume)
    for v in reversed(state.stage_b_verdicts):
        if v in ("accept", "minor revision"):
            break
        consecutive_nonpass += 1

    for rnd in range(state.stage_b_rounds + 1, MAX_STAGE_B_ROUNDS + 1):
        state.current_round = rnd
        save_state(state)

        # Deep mode: escalate after DEEP_MODE_THRESHOLD consecutive non-pass rounds
        deep_mode = consecutive_nonpass >= DEEP_MODE_THRESHOLD
        if deep_mode:
            logger.info(f"{tag} Round {rnd}: DEEP MODE active "
                        f"({consecutive_nonpass} consecutive non-pass rounds)")

        # ── B1: Compile PDF ──────────────────────────────────────
        logger.info(f"{tag} Round {rnd}: B1 — Compile PDF")
        pdf = compile_pdf(paper_path, dry_run=dry_run)
        if not pdf:
            logger.warning(f"{tag} B1 compile failed; invoking compile gate")
            if not compile_gate(paper_path, model=model, dry_run=dry_run,
                                tag=f"{tag} B1"):
                state.error = f"Stage B round {rnd}: PDF compile failed"
                save_state(state)
                return False
            h_compile = git_commit(
                paper_path,
                f"stage-B R{rnd}: repair compilation before Oracle review",
                tag=tag)
            if h_compile:
                state.log_event("B", "compile_repair", round_num=rnd,
                                committed=True, commit_hash=h_compile)
            pdf = compile_pdf(paper_path, dry_run=dry_run)
            if not pdf:
                state.error = f"Stage B round {rnd}: no PDF after compile gate"
                save_state(state)
                return False
        if pdf:
            state.pdf_path = str(pdf)
        git_stage(paper_path, tag=tag)  # B1 intermediate, tag=tag)
        state.log_event("B", "compile_pdf", round_num=rnd,
                        committed=False, commit_hash="")
        save_state(state)

        # ── B2: Oracle editorial review (EVENT WAIT) ─────────────
        # Sanitize paper_name to ASCII for URL safety (中文 in task_id breaks polling)
        safe_name = re.sub(r"[^a-zA-Z0-9_-]", "_", state.paper_name)[:80]
        # Use a per-round task id.  Reusing a stable paper-level id lets the
        # oracle server return a cached old review immediately, which traps
        # Stage B in a fake re-review loop.
        task_id_base = f"review_{safe_name}_B{rnd}_{time.time_ns()}"
        task_id = f"{task_id_base}_a1"
        # Always use first-review prompt: Oracle has no history across rounds
        prompt = build_oracle_review_prompt(state.target_journal)

        logger.info(f"{tag} Round {rnd}: B2 — Oracle review")

        if dry_run:
            response = ("Overall verdict: Major revision\n"
                        "1 | Section 3 | MEDIUM | simulated issue | fix it"
                        if rnd < 2 else "Overall verdict: Minor revision")
        else:
            # Submit one unique task per attempt, then poll until a valid
            # response arrives.  If ChatGPT extraction returns page garbage,
            # the retry must get a new task id; otherwise /result/<id> keeps
            # serving the cached bad response.
            pdf_path = Path(state.pdf_path) if state.pdf_path else None
            attempt = 1
            logger.info(f"{tag} B2 oracle submit (task={task_id})")
            if not oracle_submit(
                task_id, prompt, pdf_path,
                context_mode="fresh_review",
                agent_role="stage_b_oracle_referee",
            ):
                state.error = "Oracle submit failed"
                return False
            save_state(state)
            response = ""
            deadline = time.time() + oracle_timeout
            # Poll with validation: retry only after a completed but invalid
            # extraction.  A true timeout means the active browser task must be
            # cancelled before any later rerun, otherwise stale ChatGPT jobs
            # occupy every oracle worker while fresh tasks pile up in queue.
            while time.time() < deadline:
                remaining = max(1, int(deadline - time.time()))
                raw = oracle_poll(task_id, timeout=remaining)
                if raw == ORACLE_CANCELLED_RESPONSE:
                    state.error = (f"{PAUSED_ERROR_PREFIX} Oracle task "
                                   f"{task_id} was cancelled; rerun after "
                                   "pre-Oracle Stage A repair")
                    logger.info(f"{tag} {state.error}")
                    state.log_event("B", "oracle_cancelled",
                                    round_num=rnd, detail=state.error)
                    if not dry_run:
                        update_program_board(
                            state.paper_name, "B-PAUSED",
                            "oracle task cancelled for Stage A rerun")
                    save_state(state)
                    return False
                if is_oracle_response_valid(raw):
                    response = raw
                    break
                if raw:
                    bad_dir = SCRIPT_DIR / "oracle" / "bad"
                    bad_dir.mkdir(parents=True, exist_ok=True)
                    ts = int(time.time())
                    (bad_dir / f"{task_id}_{ts}.md").write_text(
                        raw, encoding="utf-8")
                    logger.warning(f"{tag} Oracle returned garbage "
                                   f"({len(raw)} chars), waiting 5min then re-submitting")
                else:
                    oracle_cancel(task_id, f"{state.paper_name} B{rnd} poll timeout")
                    state.log_event("B", "oracle_timeout",
                                    round_num=rnd, detail=task_id)
                    if attempt < MAX_STAGE_B_ORACLE_TIMEOUT_ATTEMPTS:
                        attempt += 1
                        task_id = f"{task_id_base}_a{attempt}"
                        logger.warning(
                            f"{tag} Oracle poll timeout; cancelled old task "
                            f"and re-submitting B{rnd} attempt {attempt}/"
                            f"{MAX_STAGE_B_ORACLE_TIMEOUT_ATTEMPTS} "
                            f"(task={task_id})")
                        if not oracle_submit(
                            task_id, prompt, pdf_path,
                            context_mode="fresh_review",
                            agent_role="stage_b_oracle_referee_timeout_retry",
                        ):
                            state.error = (
                                f"Oracle timeout re-submit failed B{rnd} "
                                f"attempt {attempt}")
                            return False
                        save_state(state)
                        deadline = time.time() + oracle_timeout
                        continue
                    logger.warning(f"{tag} Oracle poll timeout; cancelled "
                                   f"{task_id} and exhausted B{rnd} attempts")
                    break

                remaining = deadline - time.time()
                if remaining <= 300:
                    logger.warning(f"{tag} Oracle retry budget exhausted after "
                                   f"invalid response")
                    break
                # Wait before re-submitting to avoid spin loop after a completed
                # but invalid extraction.  Completed tasks already freed their
                # browser slot on the server.
                time.sleep(300)
                attempt += 1
                task_id = f"{task_id_base}_a{attempt}"
                if not oracle_submit(
                    task_id, prompt, pdf_path,
                    context_mode="fresh_review",
                    agent_role="stage_b_oracle_referee_retry",
                ):
                    state.error = f"Oracle re-submit failed B{rnd} attempt {attempt}"
                    return False
            if not response:
                state.error = (
                    f"{PAUSED_ERROR_PREFIX} Stage B Oracle infra pause at "
                    f"B{rnd}: no valid response after {attempt} attempt(s); "
                    "rerun will re-submit this same review round"
                )
                logger.warning(f"{tag} {state.error}")
                state.log_event("B", "oracle_infra_pause",
                                round_num=rnd, detail=state.error)
                if not dry_run:
                    update_program_board(
                        state.paper_name, "B-PAUSED",
                        f"Oracle infra retry needed at B{rnd}")
                save_state(state)
                return False

        # Save oracle response (only substantive ones reach done/)
        done_dir = SCRIPT_DIR / "oracle" / "done"
        done_dir.mkdir(parents=True, exist_ok=True)
        (done_dir / f"{task_id}.md").write_text(response, encoding="utf-8")

        # ── B3: Parse verdict ────────────────────────────────────
        verdict = extract_verdict(response)
        issues = parse_oracle_issues(response)
        state.stage_b_verdicts.append(verdict)

        # Accumulate ALL Oracle issues across rounds (optimization #1)
        issues_text_this_round = format_issues_for_codex(issues)
        if issues_text_this_round.strip():
            state.stage_b_all_issues.append(
                f"=== Round {rnd} (verdict: {verdict}) ===\n"
                f"{issues_text_this_round}")

        state.log_event("B", "oracle_review", round_num=rnd,
                        verdict=verdict,
                        detail=f"{len(issues)} issues")
        save_state(state)

        logger.info(f"{tag} Round {rnd}: Verdict = {verdict}, "
                    f"{len(issues)} issues "
                    f"(total accumulated: {len(state.stage_b_all_issues)} rounds)")

        # ── Gate: accept or minor revision → Stage C ────────────
        if verdict in ("accept", "minor revision"):
            logger.info(f"{tag} STAGE B PASSED at round {rnd}: {verdict.upper()}")
            git_commit(paper_path,
                       f"Stage B ({verdict}, {rnd}R): "
                       f"Oracle review passed", tag=tag)
            update_program_board(state.paper_name, "B-DONE",
                                 f"Oracle: {verdict}, {rnd} rounds")
            state.stage_b_rounds = rnd
            state.stage_b_passed = True
            consecutive_nonpass = 0
            save_state(state)
            return True

        # Update consecutive non-pass counter
        consecutive_nonpass += 1

        # ── B4: Codex fix issues ─────────────────────────────────
        # Build prior issues summary from all accumulated rounds
        prior_issues_text = ""
        if len(state.stage_b_all_issues) > 1:
            # Include all prior rounds except the current one (last entry)
            prior_issues_text = "\n\n".join(state.stage_b_all_issues[:-1])
            # Cap at 6000 chars to fit in prompt context
            if len(prior_issues_text) > 6000:
                prior_issues_text = prior_issues_text[-6000:]

        # Deep mode escalation: double timeout, activate aggressive fix mode
        b4_timeout = 3600 if deep_mode else 1800

        logger.info(f"{tag} Round {rnd}: B4 — Codex fix "
                    f"(deep_mode={deep_mode}, timeout={b4_timeout}s, "
                    f"prior_rounds={len(state.stage_b_all_issues) - 1})")
        issues_text = format_issues_for_codex(issues)
        if not issues_text.strip():
            issues_text = (
                f"Oracle verdict: {verdict}\n\n"
                "The structured issue parser found no table rows. Use the "
                "following raw review excerpt as the issue source:\n\n"
                f"{response[:6000]}"
            )
        fix_prompt = build_codex_fix_from_issues_prompt(
            state.paper_dir, issues_text, rnd,
            prior_issues=prior_issues_text,
            deep_mode=deep_mode)
        if not CLAUDE_ENABLED and issues:
            item_timeout = 1200 if deep_mode else 900
            for issue_idx, issue in enumerate(issues, 1):
                single_issue_text = format_issues_for_codex([issue])
                if not single_issue_text.strip():
                    single_issue_text = str(issue)[:3000]
                logger.info(f"{tag} Round {rnd}: B4.{issue_idx}/"
                            f"{len(issues)} — Codex focused issue fix "
                            f"(timeout={item_timeout}s)")
                single_prompt = build_codex_fix_from_issues_prompt(
                    state.paper_dir,
                    single_issue_text,
                    rnd,
                    prior_issues=prior_issues_text,
                    deep_mode=deep_mode,
                )
                codex_exec(single_prompt, work_dir=paper_path,
                           timeout_seconds=item_timeout, model=model,
                           dry_run=dry_run,
                           context_mode="contextual_execution",
                           agent_role="stage_b_focused_oracle_fix")
        else:
            codex_exec(fix_prompt, work_dir=paper_path,
                       timeout_seconds=b4_timeout, model=model,
                       dry_run=dry_run,
                       context_mode="contextual_execution",
                       agent_role="stage_b_oracle_fix")
        compiled_b4 = compile_gate(paper_path, model=model,
                                   dry_run=dry_run, tag=f"{tag} B4")
        if not compiled_b4:
            state.error = f"Stage B round {rnd}: compile failed after Codex fix"
            save_state(state)
            return False
        h_b4 = git_commit(paper_path,
                          f"stage-B R{rnd}: codex referee fixes",
                          tag=tag)
        state.stage_b_rounds = rnd
        state.log_event("B", "codex_fix", round_num=rnd,
                        committed=bool(h_b4), commit_hash=h_b4,
                        detail=f"compiled={compiled_b4}")
        save_state(state)

        if not CLAUDE_ENABLED:
            logger.info(f"{tag} Round {rnd}: B5 skipped (--no-claude); "
                        "returning directly to Oracle re-review")
            state.log_event("B", "claude_supervision_skipped",
                            round_num=rnd,
                            detail="--no-claude codex+chatgpt test mode")
            save_state(state)
            continue

        # ── B5: Claude supervisory review (review-only) ───────────
        logger.info(f"{tag} Round {rnd}: B5 — Claude supervision")
        claude_fix_prompt = textwrap.dedent(f"""\
            Systematic quality check after Codex fixed oracle-reported issues.
            Paper: {state.paper_dir}
            Target: {state.target_journal}

            The following issues were fixed by Codex:
            {issues_text}

            You are the independent supervising reviewer, not the executing
            editor. Do not edit files. Use Claude's strengths:
            1. Verify that each Oracle issue was addressed at the level of
               manuscript structure and exposition.
            2. Detect language, transition, reference, label, and local-notation
               problems.
            3. Detect revision artifacts.
            4. Decompose any remaining mathematical, structural, or language
               work into precise Codex work packages.

            Output exactly one JSON object in your final answer:
            ```json
            {{
              "system_verdict": "good|needs_codex|block",
              "language_structure_findings": [],
              "remaining_issues": [],
              "codex_work_packages": [
                {{
                  "owner": "codex_math|codex_editorial",
                  "priority": "blocker|high|medium|low",
                  "location": "...",
                  "task": "...",
                  "acceptance_criterion": "..."
                }}
              ]
            }}
            ```
        """)
        out_b5 = claude_exec(claude_fix_prompt, work_dir=paper_path,
                             dry_run=dry_run,
                             context_mode="contextual_supervision",
                             agent_role="stage_b_post_codex_review")
        b5_data = parse_json_from_output(out_b5) if not dry_run else {
            "system_verdict": "good",
            "language_structure_findings": [],
            "remaining_issues": [],
            "codex_work_packages": [],
        }
        _record_claude_supervision(
            state, f"stage_b_post_codex_review_R{rnd}", b5_data,
            raw=out_b5,
            context_mode="contextual_supervision",
            agent_role="stage_b_post_codex_review")
        b5_packages = list(_coerce_items(b5_data.get("codex_work_packages", [])))
        for issue in _coerce_items(b5_data.get("remaining_issues", [])):
            b5_packages.append({
                "owner": "codex_editorial",
                "priority": "medium",
                "location": "",
                "task": issue.get("reason", str(issue)) if isinstance(issue, dict)
                        else str(issue),
                "acceptance_criterion": "issue resolved in manuscript",
            })
        if b5_data.get("system_verdict") == "block" and not b5_packages:
            state.error = (f"Stage B round {rnd}: Claude supervision blocked "
                           f"without executable Codex packages")
            save_state(state)
            return False
        if b5_packages:
            package_issues = []
            for pkg in b5_packages:
                if isinstance(pkg, dict):
                    package_issues.append(
                        f"[{pkg.get('owner', 'codex_editorial')}/"
                        f"{pkg.get('priority', 'medium')}] "
                        f"{pkg.get('location', '')}: {pkg.get('task', '')} "
                        f"(acceptance: {pkg.get('acceptance_criterion', '')})"
                    )
                else:
                    package_issues.append(str(pkg))
            logger.info(f"{tag} Round {rnd}: B5 handed "
                        f"{len(package_issues)} package(s) back to Codex")
            codex_exec(
                build_codex_fix_from_claude_prompt(
                    state.paper_dir, package_issues, rnd),
                work_dir=paper_path, timeout_seconds=1800,
                model=model, dry_run=dry_run,
                context_mode="contextual_execution",
                agent_role="stage_b_claude_package_fix")
        compiled_b5 = compile_gate(paper_path, model=model,
                                   dry_run=dry_run, tag=f"{tag} B5")
        if not compiled_b5:
            state.error = (f"Stage B round {rnd}: compile failed after "
                           f"Claude-supervised Codex follow-up")
            save_state(state)
            return False
        h_b5 = git_commit(paper_path,
                          f"stage-B R{rnd}: claude-supervised follow-up fixes",
                          tag=tag)
        state.log_event("B", "claude_review_fixes", round_num=rnd,
                        committed=bool(h_b5), commit_hash=h_b5,
                        detail=json.dumps({
                            "compiled": compiled_b5,
                            "claude_system_review": b5_data,
                        }, ensure_ascii=False)[:10000])
        save_state(state)

        logger.info(f"{tag} Round {rnd}/{MAX_STAGE_B_ROUNDS} complete, "
                    f"looping for re-review")

    last_v = state.stage_b_verdicts[-1] if state.stage_b_verdicts else "?"
    logger.error(f"{tag} {MAX_STAGE_B_ROUNDS} rounds without Oracle acceptance "
                 f"(last verdict: {last_v}). Halting — needs human review.")
    update_program_board(state.paper_name, "B-STUCK",
                         f"Oracle: {last_v}, {state.stage_b_rounds} rounds — needs human review")
    save_state(state)
    return False


# ═══════════════════════════════════════════════════════════════════════════
# STAGE C: Oracle + Claude Final Review (memory-bearing approval loop)
# ═══════════════════════════════════════════════════════════════════════════

def run_stage_c(state: PaperState, *, dry_run: bool = False,
                model: Optional[str] = None,
                oracle_timeout: int = 7200) -> bool:
    tag = f"[{state.paper_name}|C]"
    paper_path = Path(state.paper_dir)

    for rnd in range(state.stage_c_rounds + 1, MAX_STAGE_C_ROUNDS + 1):
        state.stage_c_rounds = rnd
        state.current_round = rnd
        save_state(state)

        # ── C0: Compile current final candidate ──────────────────
        logger.info(f"{tag} Round {rnd}: C0 — Compile final candidate")
        pdf = compile_pdf(paper_path, dry_run=dry_run)
        if not pdf:
            if not compile_gate(paper_path, model=model, dry_run=dry_run,
                                tag=f"{tag} C0"):
                state.error = f"Stage C round {rnd}: PDF compile failed"
                save_state(state)
                return False
            h_compile = git_commit(
                paper_path,
                f"stage-C R{rnd}: repair compilation before final review",
                tag=tag)
            if h_compile:
                state.log_event("C", "compile_repair", round_num=rnd,
                                committed=True, commit_hash=h_compile)
            pdf = compile_pdf(paper_path, dry_run=dry_run)
            if not pdf:
                state.error = f"Stage C round {rnd}: no PDF after compile gate"
                save_state(state)
                return False
        if pdf:
            state.pdf_path = str(pdf)
        save_state(state)

        # ── C1: Oracle final confirmation ────────────────────────
        logger.info(f"{tag} Round {rnd}: C1 — Oracle final confirmation")
        if dry_run:
            oracle_response = (
                "Overall verdict: Major revision\n"
                "| C1 | Final | MEDIUM | dry run issue | fix it |"
                if rnd < 2 else "Overall verdict: Accept\nNo blockers."
            )
        else:
            safe_name = re.sub(r"[^a-zA-Z0-9_-]", "_", state.paper_name)[:80]
            task_id = f"final_{safe_name}_C{rnd}_{time.time_ns()}_a1"
            pdf_path = Path(state.pdf_path) if state.pdf_path else None
            prompt = build_oracle_re_review_prompt(state.target_journal)
            if not oracle_submit(
                task_id, prompt, pdf_path,
                context_mode="fresh_review",
                agent_role="stage_c_oracle_final",
            ):
                state.error = f"Stage C round {rnd}: Oracle submit failed"
                save_state(state)
                return False
            raw = oracle_poll(task_id, timeout=oracle_timeout)
            if raw == ORACLE_CANCELLED_RESPONSE:
                state.error = (f"{PAUSED_ERROR_PREFIX} Stage C Oracle task "
                               f"{task_id} was cancelled")
                logger.info(f"{tag} {state.error}")
                state.log_event("C", "oracle_cancelled",
                                round_num=rnd, detail=state.error)
                save_state(state)
                return False
            if not is_oracle_final_response_valid(raw):
                state.error = (
                    f"{PAUSED_ERROR_PREFIX} Stage C Oracle infra pause at "
                    f"C{rnd}: no valid final-review response; rerun will "
                    "re-submit this same final gate"
                )
                logger.warning(f"{tag} {state.error}")
                state.log_event("C", "oracle_infra_pause",
                                round_num=rnd, detail=state.error)
                save_state(state)
                return False
            oracle_response = raw
            done_dir = SCRIPT_DIR / "oracle" / "done"
            done_dir.mkdir(parents=True, exist_ok=True)
            (done_dir / f"{task_id}.md").write_text(
                oracle_response, encoding="utf-8")

        oracle_verdict = extract_verdict(oracle_response)
        oracle_issues = parse_oracle_issues(oracle_response)
        oracle_pass = oracle_verdict == "accept"
        state.log_event("C", "oracle_final_review", round_num=rnd,
                        verdict=oracle_verdict,
                        detail=oracle_response[:12000])
        save_state(state)
        stage_c_memory = _format_stage_c_memory(
            state, current_oracle_verdict=oracle_verdict,
            current_oracle_issues=oracle_issues)

        issues: list = []
        if not CLAUDE_ENABLED and not dry_run:
            claude_verdict = "pending"
            claude_pass = False
            state.stage_c_verdicts.append(
                f"oracle:{oracle_verdict};claude:pending")
            if oracle_pass and not oracle_issues:
                state.error = (
                    f"{PAUSED_ERROR_PREFIX} Stage C pending final Claude "
                    "review after Oracle accepted the manuscript"
                )
                logger.info(f"{tag} {state.error}")
                state.log_event("C", "pending_final_claude_review",
                                round_num=rnd, verdict=oracle_verdict,
                                detail=state.error)
                save_state(state)
                return False
            logger.info(f"{tag} Round {rnd}: C2 skipped (--no-claude); "
                        "Oracle has not accepted yet, so Codex will fix "
                        "Oracle final-review issues")
        else:
            # ── C2: Claude independent review ────────────────────
            logger.info(f"{tag} Round {rnd}: C2 — Claude independent review")
            review_prompt = build_claude_independent_review_prompt(
                state.paper_dir, state.target_journal,
                stage_c_memory=stage_c_memory)
            out_c1 = claude_exec(review_prompt, work_dir=paper_path,
                                 dry_run=dry_run,
                                 context_mode="contextual_supervision",
                                 agent_role="stage_c_claude_final")
            review_data = parse_json_from_output(out_c1) if not dry_run else {
                "verdict": "revise" if rnd < 2 else "submit",
                "issues": [f"dry run issue R{rnd}"] if rnd < 2 else [],
            }
            _record_claude_supervision(
                state, f"stage_c_presubmission_review_R{rnd}",
                review_data, raw=out_c1,
                context_mode="contextual_supervision",
                agent_role="stage_c_claude_final")
            claude_verdict = str(review_data.get("verdict", "revise")).lower()
            issues = list(_coerce_items(review_data.get("issues", [])))
            work_packages = review_data.get("work_packages", [])
            if work_packages:
                issues = list(issues) + [
                    f"[{wp.get('owner', 'codex_editorial')}/"
                    f"{wp.get('priority', 'medium')}] "
                    f"{wp.get('location', '')}: {wp.get('task', '')} "
                    f"(acceptance: {wp.get('acceptance_criterion', '')})"
                    if isinstance(wp, dict) else str(wp)
                    for wp in work_packages
                ]
            claude_pass = claude_verdict == "submit"
            state.stage_c_verdicts.append(
                f"oracle:{oracle_verdict};claude:{claude_verdict}")
            state.log_event("C", "claude_independent_review", round_num=rnd,
                            verdict=claude_verdict,
                            detail=json.dumps(
                                review_data, ensure_ascii=False)[:10000])
            save_state(state)

        logger.info(f"{tag} Round {rnd}: Oracle verdict = {oracle_verdict}, "
                    f"Claude verdict = {claude_verdict}; "
                    f"{len(oracle_issues)} oracle issue(s), "
                    f"{len(issues)} Claude issue(s)")

        # ── Gate: submit → Stage D ───────────────────────────────
        if oracle_pass and claude_pass and not oracle_issues and not issues:
            logger.info(f"{tag} STAGE C PASSED at round {rnd}: "
                        "Oracle + Claude approved")
            git_commit(paper_path,
                       f"Stage C (joint pass, {rnd}R): "
                       f"Oracle and Claude approved for submission", tag=tag)
            update_program_board(state.paper_name, "C-DONE",
                                 f"Oracle+Claude: pass, {rnd} rounds")
            state.stage_c_passed = True
            save_state(state)
            return True

        # ── C3: Codex fixes joint final-review issues ────────────
        logger.info(f"{tag} Round {rnd}: C3 — Codex fix joint final-review issues")
        combined_issues: list[str] = []
        oracle_issue_text = format_issues_for_codex(oracle_issues)
        if oracle_issue_text.strip():
            combined_issues.append("Oracle final-review issues:\n"
                                   + oracle_issue_text)
        elif not oracle_pass:
            combined_issues.append(
                "Oracle final-review verdict was not pass:\n"
                + oracle_response[:6000])
        for issue in issues:
            combined_issues.append(str(issue))
        if not combined_issues:
            combined_issues.append(
                "Final gate did not pass. Reconcile Oracle and Claude "
                "verdicts, improve the manuscript conservatively, and compile.")
        fix_prompt = build_codex_fix_from_claude_prompt(
            state.paper_dir, combined_issues, rnd,
            stage_c_memory=stage_c_memory)
        codex_exec(fix_prompt, work_dir=paper_path,
                   timeout_seconds=1800, model=model, dry_run=dry_run,
                   context_mode="contextual_execution",
                   agent_role="stage_c_joint_final_fix")
        compiled_c3 = compile_gate(paper_path, model=model,
                                   dry_run=dry_run, tag=f"{tag} C3")
        if not compiled_c3:
            state.error = f"Stage C round {rnd}: compile failed after Codex fix"
            save_state(state)
            return False
        h_c3 = git_commit(paper_path,
                          f"stage-C R{rnd}: codex joint final-review fixes",
                          tag=tag)
        state.log_event("C", "codex_fix_joint_final_review", round_num=rnd,
                        committed=bool(h_c3), commit_hash=h_c3,
                        detail=f"compiled={compiled_c3}")
        save_state(state)

        logger.info(f"{tag} Round {rnd}/{MAX_STAGE_C_ROUNDS} complete, "
                    f"looping for re-review")

    state.error = f"Stage C stuck: joint Oracle+Claude gate exhausted {MAX_STAGE_C_ROUNDS} rounds"
    logger.warning(f"{tag} {state.error}")
    update_program_board(state.paper_name, "C-STUCK",
                         f"Oracle+Claude exhausted {MAX_STAGE_C_ROUNDS} rounds")
    state.stage_c_passed = False
    save_state(state)
    return False


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
                        timeout_seconds=900, model=model, dry_run=dry_run,
                        context_mode="scope_bound_review",
                        agent_role="stage_d_backflow_discovery")
    bf_data = parse_json_from_output(out_d1) if not dry_run else {
        "backflow_items": [{"sub_paper_result": "dry run thm",
                            "main_paper_location": "Section 1",
                            "action": "add_reference",
                            "detail": "dry run detail"}],
        "summary": "dry run",
    }
    items = bf_data.get("backflow_items", [])
    items = [
        it for it in items
        if str(it.get("backflow_class", "")).upper() != "NO_BACKFLOW"
        and str(it.get("action", "")).lower() != "no_change"
    ]
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

    # ── D1.5: Codex explicit placement analysis (two-step backflow) ──
    # Borrowed from outreach pipeline: separate "where" from "what" for
    # more precise backflow. Codex first proposes exact file/section
    # placement, then Claude reviews the plan before applying.
    logger.info(f"{tag} D1.5 — Codex placement analysis")
    placement_prompt = build_backflow_placement_prompt(
        state.paper_dir, state.main_paper_dir, items)
    out_d15 = codex_exec(placement_prompt, work_dir=REPO_ROOT,
                         timeout_seconds=600, model=model, dry_run=dry_run,
                         context_mode="contextual_supervision",
                         agent_role="stage_d_placement_analysis")
    placement_data = parse_json_from_output(out_d15) if not dry_run else {
        "placements": [{"item_index": i + 1,
                        "target_file": "main.tex",
                        "target_section": "Section 1",
                        "insert_after": "Theorem 1.1",
                        "placement_type": "citation_only",
                        "rationale": "dry run placement"}
                       for i in range(len(items))],
    }
    placements = placement_data.get("placements", [])
    state.log_event("D", "codex_placement_analysis",
                    detail=f"{len(placements)} placements proposed")
    save_state(state)

    if not CLAUDE_ENABLED and not dry_run:
        state.error = (f"{PAUSED_ERROR_PREFIX} Stage D waiting for Claude "
                       "admissibility audit after Codex placement analysis")
        logger.info(f"{tag} {state.error}")
        state.log_event("D", "paused", detail=state.error)
        save_state(state)
        return False

    # ── D2: Claude reviews admissibility + placement plan ─────────
    logger.info(f"{tag} D2 — Claude main-paper admissibility audit")
    claude_bf_prompt = textwrap.dedent(f"""\
        Review this layered backflow proposal and its placement plan.
        Sub-paper: {state.paper_dir}
        Main paper: {state.main_paper_dir}

        ## Proposed backflow items
        {json.dumps(items, indent=2, ensure_ascii=False)[:4000]}

        ## Proposed placements
        {json.dumps(placements, indent=2, ensure_ascii=False)[:3000]}

        For each item:
        1. Is the item admissible to the main paper at the proposed tier?
        2. Is the result general, stable, and reusable enough for that tier?
        3. If local, is it kept in a registry/example/obstruction/citation
           layer rather than contaminating the main theorem chain?
        4. Does it depend on sub-paper notation that must be normalized?
        5. Is the proposed placement (file, section, position) correct?

        Output ONLY:
        ```json
        {{
          "approved": true/false,
          "approved_items": [0, 1, ...],
          "rejected_items": [2, ...],
          "revised_placements": [],
          "item_decisions": [
            {{
              "item_index": 1,
              "approved": true,
              "approved_tier": "main_theorem_chain|framework_layer|module_registry|example_ledger|obstruction_section|applications_appendix|citation_registry|none",
              "rationale": "..."
            }}
          ],
          "notes": "explanation"
        }}
        ```
        Use zero-based indices in approved_items and rejected_items.
        If any placement is wrong, include the corrected placement in
        revised_placements (same format as the placements input).
    """)
    out_d2 = claude_exec(claude_bf_prompt, work_dir=REPO_ROOT,
                         dry_run=dry_run,
                         context_mode="contextual_supervision",
                         agent_role="stage_d_backflow_admissibility")
    approval = parse_json_from_output(out_d2) if not dry_run else {
        "approved": True, "approved_items": list(range(len(items))),
    }
    _record_claude_supervision(
        state, "stage_d_backflow_admissibility", approval, raw=out_d2,
        context_mode="contextual_supervision",
        agent_role="stage_d_backflow_admissibility")
    state.log_event("D", "claude_review_backflow",
                    detail=json.dumps(approval, ensure_ascii=False)[:10000])
    save_state(state)

    # Apply any revised placements from Claude
    revised = approval.get("revised_placements", [])
    if revised:
        # Merge revisions into placements by item_index
        rev_map = {}
        for r in revised:
            if not isinstance(r, dict):
                continue
            try:
                rev_map[int(r.get("item_index"))] = r
            except Exception:
                continue
        for i, p in enumerate(placements):
            try:
                idx = int(p.get("item_index", i + 1))
            except Exception:
                idx = i + 1
            if idx in rev_map:
                placements[i] = rev_map[idx]
        logger.info(f"{tag} D2: Claude revised {len(revised)} placements")

    raw_approved = approval.get("approved_items", None)
    if raw_approved is None and approval.get("approved", False):
        raw_approved = list(range(len(items)))
    if raw_approved is None:
        raw_approved = []
    approved_numbers = []
    for idx in raw_approved:
        try:
            approved_numbers.append(int(idx))
        except Exception:
            pass
    # Prefer the documented zero-based convention.  If a model returns
    # one-based indices, normalize them rather than silently dropping all items.
    if (approved_numbers and 0 not in approved_numbers
        and max(approved_numbers) <= len(items)):
        approved_numbers = [i - 1 for i in approved_numbers]

    if not approved_numbers:
        logger.info(f"{tag} Backflow rejected by Claude — skipping")
        state.stage_d_passed = True
        save_state(state)
        return True

    # Filter to approved items only
    approved_idx = set(approved_numbers)
    approved_items = []
    for i, it in enumerate(items):
        if i not in approved_idx:
            continue
        cls = str(it.get("backflow_class", "")).upper()
        tier = str(it.get("main_paper_tier", "")).lower()
        action = str(it.get("action", "")).lower()
        split_citation = (
            cls == "SPLIT_CANDIDATE"
            and tier == "citation_registry"
            and action in ("add_reference", "citation_only")
        )
        if cls in ("NO_BACKFLOW",):
            continue
        if cls == "SPLIT_CANDIDATE" and not split_citation:
            continue
        item_copy = dict(it)
        item_copy["_item_index"] = i + 1
        approved_items.append(item_copy)

    if not approved_items:
        logger.info(f"{tag} No admissible approved backflow items after tier filter")
        state.stage_d_passed = True
        save_state(state)
        return True

    # ── D3: Apply backflow with explicit placement guidance ──────
    logger.info(f"{tag} D3 — Apply {len(approved_items)} backflow items "
                f"with {len(placements)} placement guides")
    apply_prompt = build_backflow_apply_prompt(
        state.paper_dir, state.main_paper_dir, approved_items,
        placements=placements)
    codex_exec(apply_prompt, work_dir=REPO_ROOT,
               timeout_seconds=1800, model=model, dry_run=dry_run,
               context_mode="contextual_execution",
               agent_role="stage_d_apply_backflow")
    compiled_d3 = compile_gate(main_path, model=model,
                               dry_run=dry_run, tag=f"{tag} D3")
    if not compiled_d3:
        state.error = "Stage D: main paper compile failed after backflow apply"
        save_state(state)
        return False
    h = git_commit_multi(
        [main_path],
        f"stage-D: backflow {len(approved_items)} items to main paper",
        tag=tag)
    state.log_event("D", "apply_backflow",
                    committed=bool(h), commit_hash=h,
                    detail=f"compiled={compiled_d3}")
    save_state(state)

    # ── D4: Main-paper verification ──────────────────────────────
    logger.info(f"{tag} D4 — Verify main paper integration")
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
               timeout_seconds=900, model=model, dry_run=dry_run,
               context_mode="contextual_execution",
               agent_role="stage_d_verify_main")
    compiled_d4 = compile_gate(main_path, model=model,
                               dry_run=dry_run, tag=f"{tag} D4")
    if not compiled_d4:
        state.error = "Stage D: main paper compile failed after verification"
        save_state(state)
        return False
    h = git_commit(main_path,
                   f"stage-D: verify main paper after backflow",
                   tag=tag)
    state.log_event("D", "claude_verify_main",
                    committed=bool(h), commit_hash=h,
                    detail=f"compiled={compiled_d4}")
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
    out_d5 = claude_exec(
        d5_prompt, work_dir=main_path, dry_run=dry_run,
        context_mode="contextual_supervision",
        agent_role="stage_d_backflow_quality")
    d5_data = parse_json_from_output(out_d5) if not dry_run else {
        "quality_verdict": "good", "issues": [], "notes": "dry run",
    }
    _record_claude_supervision(
        state, "stage_d_backflow_quality", d5_data, raw=out_d5,
        context_mode="contextual_supervision",
        agent_role="stage_d_backflow_quality")
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
                   timeout_seconds=900, model=model, dry_run=dry_run,
                   context_mode="contextual_execution",
                   agent_role="stage_d_backflow_quality_fix")
        compiled_d5 = compile_gate(main_path, model=model,
                                   dry_run=dry_run, tag=f"{tag} D5")
        if not compiled_d5:
            state.error = "Stage D: main paper compile failed after D5 fixes"
            save_state(state)
            return False
        h = git_commit(main_path,
                       f"stage-D5: fix {len(d5_issues)} backflow quality issues",
                       tag=tag)
        state.log_event("D", "codex_fix_backflow_quality",
                        committed=bool(h), commit_hash=h,
                        detail=f"compiled={compiled_d5}")
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
                {"name": DEFAULT_TARGET_JOURNAL, "fit_score": 6,
                 "reason": "broader scope"},
            ],
        }
        selected = j_data.get("recommended_journal", DEFAULT_TARGET_JOURNAL)
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
    scope_work_dir = Path(state.main_paper_dir) if state.main_paper_dir else paper_path
    if not CLAUDE_ENABLED and not dry_run:
        scope_out = codex_exec(
            scope_prompt + "\n\nClaude is disabled by --no-claude; provide "
            "a temporary Codex scope definition for smoke testing.",
            work_dir=scope_work_dir, timeout_seconds=900,
            model=model, dry_run=dry_run)
    else:
        scope_out = claude_exec(scope_prompt, work_dir=scope_work_dir,
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
    scope_event = (
        "claude_scope_definition"
        if CLAUDE_ENABLED else "codex_fallback_scope_definition"
    )
    state.log_event("N", scope_event,
                    detail=json.dumps(scope_data, ensure_ascii=False)[:10000])
    _record_claude_supervision(
        state,
        "new_paper_scope_definition"
        if CLAUDE_ENABLED else "new_paper_scope_definition_codex_fallback",
        scope_data, raw=scope_out)
    save_state(state)

    # Pass scope constraints to N1
    scope_constraints = json.dumps(scope_data, indent=2, ensure_ascii=False)[:5000]
    logger.info(f"{tag} NS scope: {scope_data.get('cut_strategy', '?')}, "
                f"~{scope_data.get('target_pages', '?')} pages, "
                f"core: {str(scope_data.get('core_theorem', ''))[:80]}")

    # ── N1: Deep research (guided by scope constraints) ──────────
    logger.info(f"{tag} N1 — Codex deep research (for {journal})")
    prompt_n1 = build_new_research_prompt(topic, outline, journal,
                                          main_paper_dir=state.main_paper_dir)
    scope_label = (
        "defined by independent Claude review"
        if CLAUDE_ENABLED else "temporary Codex fallback, --no-claude"
    )
    prompt_n1 += f"\n\n## Scope ({scope_label})\n{scope_constraints}\n"
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
    target_journal: str = "",
    main_paper_dir: str = "",
    skip_to: str = "",
    stop_after: str = "",
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
    elif state.error:
        logger.info(f"[{paper_name}] Clearing previous pipeline error: "
                    f"{state.error[:200]}")
        state.error = ""
        save_state(state)

    # Recover round counters from git log if state was reset or started fresh.
    # Prevents redoing Codex/Oracle work already committed in prior sessions.
    rebuild_rounds_from_git(state)

    # Auto-detect target journal: paper metadata/board > explicit CLI arg >
    # existing state > conservative default.
    detected = detect_target_journal(str(paper_path))
    if detected:
        state.target_journal = detected
        logger.info(f"[{paper_name}] Auto-detected journal: {detected}")
    elif target_journal:
        state.target_journal = target_journal
        logger.info(f"[{paper_name}] CLI target journal: {target_journal}")
    elif state.target_journal:
        logger.info(f"[{paper_name}] Reusing state target journal: "
                    f"{state.target_journal}")
    else:
        state.target_journal = DEFAULT_TARGET_JOURNAL
        logger.info(f"[{paper_name}] No journal metadata found; defaulting to "
                    f"{DEFAULT_TARGET_JOURNAL}")
    if main_paper_dir:
        mp = Path(main_paper_dir)
        if not mp.is_absolute():
            mp = REPO_ROOT / mp
        state.main_paper_dir = str(mp)

    if skip_to and skip_to in STAGE_ORDER:
        state.current_stage = skip_to

    if state.current_stage in ("B", "C", "D") and not stage_a_ready_for_b(state):
        logger.warning(f"[{paper_name}] Later-stage state lacks strict "
                       f"Stage A audit pass; routing back to Stage A")
        state.current_stage = "A"
        state.stage_a_passed = False
        if state.stage_a_audit_metrics.get("mode") == "no_claude_deterministic_audit":
            logger.warning(f"[{paper_name}] Resetting deterministic Stage A "
                           "audit counters before rerun")
            state.stage_a_audit_rounds = 0
            state.stage_a_audit_metrics = {}
            state.stage_a_scores = []
        save_state(state)

    tag = f"[{paper_name}]"
    logger.info(f"{'='*60}")
    logger.info(f"{tag} Pipeline start — Stage {state.current_stage}")
    logger.info(f"{tag} Journal: {state.target_journal}")
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
            if stage in ("B", "C"):
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

        # Advance to next stage.  stop_after lets supervised batches push
        # papers to a precise gate, e.g. A/B complete and ready for C, without
        # consuming final-review or backflow resources prematurely.
        idx = STAGE_ORDER.index(stage)
        state.current_stage = STAGE_ORDER[idx + 1]
        save_state(state)
        if stop_after and stage == stop_after:
            logger.info(f"{tag} STOP-AFTER {stop_after}: "
                        f"parked at Stage {state.current_stage}")
            return True, state

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


MAX_ORACLE_WAIT_OVERSUBSCRIPTION = 3


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
    pool_workers = min(
        len(queue),
        parallel + MAX_ORACLE_WAIT_OVERSUBSCRIPTION,
    ) or parallel

    logger.info(f"Rolling pipeline: {len(queue)} papers, {parallel} workers "
                f"(pool={pool_workers}, auto={parallel == _auto_parallel()})")

    with ThreadPoolExecutor(max_workers=pool_workers,
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

        def _target_active() -> int:
            return min(
                pool_workers,
                parallel + min(get_oracle_wait_count(),
                               MAX_ORACLE_WAIT_OVERSUBSCRIPTION),
            )

        def _fill_available_slots():
            while queue and len(futures) < _target_active():
                _submit()

        _fill_available_slots()

        while futures:
            done, _ = wait(futures, timeout=30, return_when=FIRST_COMPLETED)
            if not done:
                _fill_available_slots()
                continue
            for fut in done:
                d = futures.pop(fut)
                name = Path(d).name
                try:
                    ok, st = fut.result()
                    if ok:
                        succeeded += 1
                        total = st.stage_a_rounds + st.stage_b_rounds + st.stage_c_rounds
                        logger.info(f"[{name}] SUCCESS — {total} total rounds")
                    elif str(st.error).startswith(PAUSED_ERROR_PREFIX):
                        failed += 1
                        logger.warning(f"[{name}] PAUSED — {st.error}")
                    else:
                        failed += 1
                        logger.warning(f"[{name}] FAILED — {st.error}")
                except Exception as exc:
                    failed += 1
                    logger.error(f"[{name}] EXCEPTION: {exc}")

                # Push after each paper completes
                with git_repo_lock():
                    push = run_cmd(["git", "push", "origin",
                                    "dev-automation-integration"], timeout=60)
                    if push.returncode == 0:
                        logger.info(f"Git push OK after {name}")
                    else:
                        logger.warning(f"Git push failed after {name}")

                _fill_available_slots()

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
        audit = d.get("stage_a_audit_metrics", {})
        metrics = audit.get("metrics", {}) if isinstance(audit, dict) else {}
        audit_score = min((_metric_int(v) for v in metrics.values()),
                          default=None)
        a_last = audit_score if audit_score is not None else (
            d.get("stage_a_scores", [0])[-1] if d.get("stage_a_scores") else "-")
        err = str(d.get("error", ""))
        stage_cell = d.get("current_stage", "?")
        if err.startswith(PAUSED_ERROR_PREFIX):
            stage_cell = "PAUSED"
        elif err:
            stage_cell = "FAILED"
        rows.append((
            d.get("paper_name", f.stem)[:55],
            stage_cell,
            str(d.get("stage_f_fit_score", "?")),
            f"{d.get('stage_a_rounds', 0)}r "
            f"audit={a_last}",
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
            with git_repo_lock():
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
        a_audit = d.get("stage_a_audit_metrics", {})
        a_metrics = a_audit.get("metrics", {}) if isinstance(a_audit, dict) else {}
        a_audit_rounds = d.get("stage_a_audit_rounds", 0)
        b_verd = d.get("stage_b_verdicts", [])
        c_verd = d.get("stage_c_verdicts", [])
        err = d.get("error", "")

        f_fit = d.get("stage_f_fit_score", 0)
        f_orig = d.get("stage_f_original_journal", "")
        f_sugg = d.get("stage_f_suggested_journal", "")
        journal = d.get("target_journal", "?")

        if stage == "DONE":
            status = "DONE"
        elif str(err).startswith(PAUSED_ERROR_PREFIX):
            status = "PAUSED"
        elif err:
            status = "FAILED"
        else:
            status = f"Stage {stage}"
        _print(f"  {name}")
        _print(f"    Status:  {status}  |  Total rounds: {total}")
        _print(f"    Journal: {journal}"
               + (f" (rerouted from {f_orig})" if f_sugg else ""))
        if f_fit:
            _print(f"    Stage F: fit={f_fit}/10"
                   + (f", suggested={f_sugg}" if f_sugg else ""))
        _print(f"    Stage A: {a_r} rounds, scores={a_scores}")
        if a_metrics:
            metric_text = ", ".join(
                f"{k}={v}" for k, v in sorted(a_metrics.items()))
            _print(f"             audit_rounds={a_audit_rounds}, "
                   f"{metric_text}")
        _print(f"    Stage B: {b_r} rounds, verdicts={b_verd}")
        _print(f"    Stage C: {c_r} rounds, verdicts={c_verd}")
        if err:
            _print(f"    Error:   {err}")
        _print("")


def main() -> int:
    global CLAUDE_ENABLED
    parser = argparse.ArgumentParser(
        description="Oracle Pipeline v2 — new-paper + review automation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
            Two pipelines:
              --new    New paper: N1(research) → N2(scaffold) → N3(style) → Review
              default  Review:   A(scope+theoremization) → B(oracle) → C(final joint gate) → D(backflow)

            Review stages:
              F  Journal fit check (fit >= 6 to keep target; else auto-reroute)
              A  Codex quality review + journal style (score >= 8 to pass)
              B  Oracle (ChatGPT) review (accept/minor revision to pass)
              C  Oracle final loop + Claude memory-bearing review (submit to pass)
              D  Backflow check to main paper, Claude-gated before apply

            Examples:
              # New paper from topic:
              oracle_pipeline.py --new --topic "Folding dynamics" --target-journal "Adv. Math."
              # New paper from outline file:
              oracle_pipeline.py --new --outline notes.md --target-journal "JEMS"
              # Review existing paper:
              oracle_pipeline.py --paper theory/2026_xxx/ --target-journal "Adv. Math."
              # Push all current drafts through A/B only:
              oracle_pipeline.py --all --parallel 2 --no-claude --stop-after B
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
    parser.add_argument("--target-journal", type=str, default="",
                        help=("Explicit target journal override. In review "
                              "mode, omitted means board/paper metadata wins."))
    parser.add_argument("--main-paper", type=str, default="",
                        help="Main paper dir for Stage D backflow")
    parser.add_argument("--parallel", "-p", type=int, default=0,
                        help="Worker count (0=auto-detect from CPU cores)")
    parser.add_argument("--continuous", action="store_true")
    parser.add_argument("--skip-to", type=str, default="",
                        choices=["F", "A", "B", "C", "D"])
    parser.add_argument("--stop-after", type=str, default="",
                        choices=["F", "A", "B", "C", "D"],
                        help=("Stop after the named stage succeeds and park "
                              "the paper at the next stage. Use "
                              "`--stop-after B` for A/B-only batches."))
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--no-claude", action="store_true",
                        help=("Disable Claude gates for Codex+ChatGPT smoke "
                              "testing. Stage C keeps fixing Oracle issues "
                              "and pauses when final Claude approval or "
                              "Stage D backflow approval is required."))
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
    CLAUDE_ENABLED = not args.no_claude

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

    if not args.dry_run and CLAUDE_ENABLED:
        claude_ok, claude_msg = claude_health_status()
        if not claude_ok:
            logger.error("Claude supervision unavailable; refusing to start "
                         f"pipeline: {claude_msg}")
            logger.error("No paper status was changed. Restart after Claude "
                         "availability recovers, or run --dry-run for a "
                         "non-mutating smoke test.")
            return 2
    elif not args.dry_run:
        logger.warning("Claude gates disabled by --no-claude; running "
                       "Codex+ChatGPT smoke-test mode")

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
        stop_after=args.stop_after,
        dry_run=args.dry_run,
        model=args.model,
        oracle_timeout=args.oracle_timeout,
    )

    if len(paper_dirs) == 1 and args.parallel <= 1:
        ok, st = run_paper_pipeline(paper_dirs[0], **kwargs)
        return 0 if ok else 1

    if args.continuous:
        cycle = 0
        while True:
            cycle += 1
            logger.info(f"=== Continuous cycle {cycle} ===")
            # Re-discover papers each cycle (picks up new P0 entries)
            paper_dirs = discover_papers(respect_assignment=not args.no_assign)
            if not paper_dirs:
                logger.info("No papers to process, sleeping 300s...")
                time.sleep(300)
                continue
            s, f = run_rolling(paper_dirs, parallel=args.parallel, **kwargs)
            logger.info(f"Cycle {cycle} done: {s} succeeded, {f} failed")
            logger.info("Sleeping 300s before next cycle...")
            time.sleep(300)
    else:
        s, f = run_rolling(paper_dirs, parallel=args.parallel, **kwargs)
        logger.info(f"Done: {s} succeeded, {f} failed")
        return 0 if s > 0 or args.dry_run else 1


if __name__ == "__main__":
    raise SystemExit(main())
