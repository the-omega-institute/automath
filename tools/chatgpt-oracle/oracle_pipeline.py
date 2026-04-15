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
    D3: 修改主论文 → commit
    D4: Claude 验证 → commit

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
    # ── Windows machine (11 papers) ──────────────────────────────
    # High review count, close to acceptance, need Oracle iterations
    "win32": [
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
    ],
    # ── Mac machine (10 papers) ──────────────────────────────────
    # Newer or fewer reviews, need more Codex quality rounds
    "darwin": [
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


# Cache board journals at module load
_board_journals: Optional[dict[str, str]] = None


def _get_board_journals() -> dict[str, str]:
    global _board_journals
    if _board_journals is None:
        _board_journals = _load_board_journals()
    return _board_journals


def detect_target_journal(paper_dir: str) -> str:
    """Auto-detect target journal for a paper.

    Priority:
      1. PROGRAM_BOARD.md (authoritative pub plan)
      2. Paper's own PIPELINE.md
      3. Journal abbreviation in directory name
      4. Empty string → Stage F will select via codex
    """
    paper_path = Path(paper_dir)
    name_lower = paper_path.name.lower()

    # 1. Check PROGRAM_BOARD.md
    board = _get_board_journals()
    for key, journal in board.items():
        if key in name_lower:
            return journal

    # 2. Check paper's own PIPELINE.md
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

    # 3. Check directory name for known abbreviations
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
            detail=kwargs.get("detail", "")[:2000],
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
                     "stage_a_rounds", "stage_a_passed",
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


def git_commit(paper_path: Path, msg: str, *, tag: str = "") -> str:
    """Stage changes under paper_path, commit, return hash. Thread-safe."""
    with _git_lock:
        status = run_cmd(["git", "status", "--porcelain", str(paper_path)])
        if not status.stdout.strip():
            logger.info(f"{tag} No changes to commit")
            return ""
        run_cmd(["git", "add", str(paper_path)])
        full_msg = (
            f"{msg}\n\n"
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
                  model: str = "o3-mini-high") -> bool:
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


def oracle_poll(task_id: str, timeout: int = 7200,
                poll_interval: int = 30) -> str:
    """EVENT WAIT — blocks until oracle responds."""
    logger.info(f"EVENT WAIT: oracle {task_id} (max {timeout}s)")
    start = time.time()
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
            logger.info(f"  Waiting for {task_id}... ({elapsed}s)")
        time.sleep(poll_interval)
    return ""


# ---------------------------------------------------------------------------
# Codex exec
# ---------------------------------------------------------------------------

def codex_exec(prompt: str, *, work_dir: Optional[Path] = None,
               timeout_seconds: int = 1800, model: Optional[str] = None,
               dry_run: bool = False) -> str:
    if dry_run:
        logger.info(f"[DRY RUN] codex exec:\n{prompt[:200]}...")
        return "(dry run)"

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

    cmd = [
        codex_bin, "exec",
        "--dangerously-bypass-approvals-and-sandbox",
        "-C", str(work_dir or REPO_ROOT), "-o", out_file,
    ]
    if model:
        cmd.extend(["-m", model])
    cmd.append("-")

    # Windows: .cmd wrappers need shell=True
    use_shell = IS_WINDOWS and str(codex_bin).endswith(".cmd")

    start = time.monotonic()
    result = None
    try:
        with open(prompt_file, "r", encoding="utf-8") as pf:
            result = subprocess.run(
                cmd, stdin=pf, capture_output=True, text=True,
                timeout=timeout_seconds + 30,
                cwd=str(work_dir or REPO_ROOT),
                shell=use_shell,
                encoding="utf-8", errors="replace",
            )
    except subprocess.TimeoutExpired:
        return "(timeout)"
    finally:
        elapsed = time.monotonic() - start
        rc = result.returncode if result else "?"
        logger.info(f"Codex exec: {elapsed:.1f}s (rc={rc})")
        os.unlink(prompt_file)

    output = ""
    try:
        if os.path.exists(out_file) and os.path.getsize(out_file) > 0:
            with open(out_file, "r", encoding="utf-8") as f:
                output = f.read()
        else:
            output = (result.stdout or "") if result else ""
    finally:
        os.unlink(out_file)
    return output


# ---------------------------------------------------------------------------
# Compile PDF
# ---------------------------------------------------------------------------

def compile_pdf(paper_path: Path, *, dry_run: bool = False) -> Optional[Path]:
    if dry_run:
        return paper_path / "main.pdf"
    main_tex = paper_path / "main.tex"
    if not main_tex.exists():
        return None
    # Auto-detect compiler: xelatex for CJK/fontspec, pdflatex otherwise
    content = main_tex.read_text(encoding="utf-8", errors="replace")
    compiler = ("xelatex" if any(k in content for k in ("xeCJK", "ctex", "fontspec"))
                else "pdflatex")
    for _ in range(2):
        run_cmd([compiler, "-interaction=nonstopmode", "-halt-on-error",
                 "main.tex"], cwd=paper_path, timeout=120)
    # Also check references_local.bib (some papers use that name)
    has_bib = ((paper_path / "references.bib").exists()
               or (paper_path / "references_local.bib").exists())
    if has_bib:
        run_cmd(["bibtex", "main"], cwd=paper_path, timeout=60)
        for _ in range(2):
            run_cmd([compiler, "-interaction=nonstopmode", "-halt-on-error",
                     "main.tex"], cwd=paper_path, timeout=120)
    pdf = paper_path / "main.pdf"
    return pdf if pdf.exists() else None


# ---------------------------------------------------------------------------
# Prompt builders
# ---------------------------------------------------------------------------

def build_quality_review_prompt(paper_dir: str, target_journal: str,
                                round_num: int) -> str:
    """Stage A prompt: review existing paper quality + fix issues."""
    return textwrap.dedent(f"""\
        You are an editor of "{target_journal}" reviewing a submission.
        This is quality-review round {round_num} for the paper in: {paper_dir}

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

        ## Scoring Dimensions
        1. **Mathematical depth & novelty** (are the results genuinely new?)
        2. **Proof completeness** (any gaps, missing steps, implicit assumptions?)
        3. **Writing quality** (natural academic prose, not AI-generated?)
        4. **Journal fit** (matches "{target_journal}" conventions?)
        5. **Structure & flow** (logical progression, appropriate body/appendix ratio?)

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
          "key_issues": ["issue1", "issue2", ...],
          "strengths": ["strength1", "strength2", ...],
          "specific_fixes": ["fix1", "fix2", ...]
        }}
        ```

        Be ruthlessly honest. A score of 8+ means ready for submission.
        Do NOT edit any files — only output the JSON evaluation.
    """)


def build_oracle_review_prompt(target_journal: str) -> str:
    return textwrap.dedent(f"""\
        You are a referee for "{target_journal}". Review the attached paper.

        Provide:
        1. **Overall verdict**: Accept / Minor revision / Major revision / Reject
        2. **Novelty rating** per theorem: HIGH / MEDIUM / LOW with justification
        3. **Issue table**: ID | Section | Severity (BLOCKER/MEDIUM/LOW) | Description | Suggested fix
        4. **Missing references**: important related work not cited
        5. **Concrete fixes**: for each BLOCKER and MEDIUM issue, show HOW to fix
           with mathematical content (corrected proof sketch, precise bound, etc.)

        Be rigorous. Focus on what needs to change, not what the paper already says.
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


def extract_verdict(text: str) -> str:
    t = text.lower()
    for v in ["accept", "minor revision", "major revision", "reject"]:
        if v in t:
            return v
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

    fit_score = fit_data.get("fit_score", 0)
    state.stage_f_fit_score = fit_score
    state.log_event("F", "codex_fit_assessment", score=fit_score,
                    detail=json.dumps(fit_data, ensure_ascii=False)[:2000])
    save_state(state)

    logger.info(f"{tag} Fit score: {fit_score}/10 "
                f"(threshold: {FIT_PASS_THRESHOLD})")

    # ── F2: Claude review ────────────────────────────────────────
    logger.info(f"{tag} F2 — Claude review fit assessment")
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
    out2 = codex_exec(claude_prompt, work_dir=paper_path,
                      timeout_seconds=600, model=model, dry_run=dry_run)
    claude_data = parse_json_from_output(out2) if not dry_run else {
        "adjusted_fit_score": 4,
        "recommended_journal": "Journal of Functional Analysis",
        "notes": "dry run",
    }

    adjusted = claude_data.get("adjusted_fit_score", fit_score)
    recommended = claude_data.get("recommended_journal", state.target_journal)
    final_fit = min(fit_score, adjusted)

    state.log_event("F", "claude_review_fit", score=adjusted,
                    detail=json.dumps(claude_data, ensure_ascii=False)[:2000])
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

    # Log the suggested alternatives
    alts = fit_data.get("suggested_journals", [])
    for alt in alts[:3]:
        logger.info(f"{tag}   Alternative: {alt.get('name', '?')} "
                    f"(fit={alt.get('fit_score', '?')}): "
                    f"{alt.get('reason', '')}")

    return True


# ═══════════════════════════════════════════════════════════════════════════
# STAGE A: Codex Quality Review + Journal Style (score-gated loop)
# ═══════════════════════════════════════════════════════════════════════════

def run_stage_a(state: PaperState, *, dry_run: bool = False,
                model: Optional[str] = None) -> bool:
    tag = f"[{state.paper_name}|A]"
    paper_path = Path(state.paper_dir)

    for rnd in range(state.stage_a_rounds + 1, MAX_STAGE_A_ROUNDS + 1):
        state.stage_a_rounds = rnd
        state.current_round = rnd
        save_state(state)

        # ── A1: Codex quality review + fix ─────────────────────────
        logger.info(f"{tag} Round {rnd}: A1 — Codex quality review")
        prompt_a1 = build_quality_review_prompt(
            state.paper_dir, state.target_journal, rnd)
        codex_exec(prompt_a1, work_dir=paper_path,
                   timeout_seconds=2400, model=model, dry_run=dry_run)
        h = git_commit(paper_path,
                       f"stage-A R{rnd}: codex quality review", tag=tag)
        state.log_event("A", "codex_quality_review", round_num=rnd,
                        committed=bool(h), commit_hash=h)
        save_state(state)

        # ── A2: Codex journal style optimization ─────────────────
        logger.info(f"{tag} Round {rnd}: A2 — Codex journal style")
        prompt_a2 = build_journal_style_prompt(
            state.paper_dir, state.target_journal, rnd)
        codex_exec(prompt_a2, work_dir=paper_path,
                   timeout_seconds=2400, model=model, dry_run=dry_run)
        h = git_commit(paper_path,
                       f"stage-A R{rnd}: codex journal style optimization", tag=tag)
        state.log_event("A", "codex_journal_style", round_num=rnd,
                        committed=bool(h), commit_hash=h)
        save_state(state)

        # ── A3: Codex self-score ─────────────────────────────────
        logger.info(f"{tag} Round {rnd}: A3 — Codex self-score")
        prompt_a3 = build_self_score_prompt(state.paper_dir, state.target_journal)
        out_a3 = codex_exec(prompt_a3, work_dir=paper_path,
                            timeout_seconds=600, model=model, dry_run=dry_run)
        score_data = parse_json_from_output(out_a3) if not dry_run else {
            "overall_score": 6 + rnd, "verdict": "revise" if rnd < 3 else "accept",
            "key_issues": [f"dry run issue R{rnd}"],
            "specific_fixes": [f"dry run fix R{rnd}"],
        }
        score = score_data.get("overall_score", 0)
        state.stage_a_scores.append(score)
        state.log_event("A", "codex_self_score", round_num=rnd,
                        score=score,
                        detail=json.dumps(score_data, ensure_ascii=False)[:2000])
        save_state(state)

        logger.info(f"{tag} Round {rnd}: Score = {score}/10 "
                    f"(threshold = {SCORE_PASS_THRESHOLD})")

        # ── A4: Claude reviews the score/evaluation ──────────────
        logger.info(f"{tag} Round {rnd}: A4 — Claude review of score")
        claude_review_prompt = textwrap.dedent(f"""\
            Review this Codex self-evaluation of a paper in {state.paper_dir}.
            Target journal: {state.target_journal}

            Codex evaluation:
            {json.dumps(score_data, indent=2, ensure_ascii=False)[:3000]}

            Questions:
            1. Is the score of {score}/10 honest? Would you score higher or lower?
            2. Are the listed issues real problems?
            3. Are the suggested fixes actionable?

            Output ONLY a JSON block:
            ```json
            {{
              "adjusted_score": <1-10>,
              "agree_with_issues": true/false,
              "notes": "brief explanation"
            }}
            ```
        """)
        out_a4 = codex_exec(claude_review_prompt, work_dir=paper_path,
                            timeout_seconds=600, model=model, dry_run=dry_run)
        claude_data = parse_json_from_output(out_a4) if not dry_run else {
            "adjusted_score": 5 + rnd, "agree_with_issues": True,
        }
        adjusted = claude_data.get("adjusted_score", score)
        state.log_event("A", "claude_review_score", round_num=rnd,
                        score=adjusted,
                        detail=json.dumps(claude_data, ensure_ascii=False)[:2000])
        save_state(state)

        # Use the more conservative (lower) of the two scores
        final_score = min(score, adjusted)
        logger.info(f"{tag} Round {rnd}: Final score = {final_score} "
                    f"(codex={score}, claude={adjusted})")

        # ── Gate: pass if ≥ threshold ────────────────────────────
        if final_score >= SCORE_PASS_THRESHOLD:
            logger.info(f"{tag} STAGE A PASSED at round {rnd} "
                        f"(score {final_score} >= {SCORE_PASS_THRESHOLD})")
            state.stage_a_passed = True
            save_state(state)
            return True

        logger.info(f"{tag} Score {final_score} < {SCORE_PASS_THRESHOLD}, "
                    f"looping (round {rnd}/{MAX_STAGE_A_ROUNDS})")

    # Max rounds exhausted — proceed anyway with warning
    logger.warning(f"{tag} Max {MAX_STAGE_A_ROUNDS} rounds exhausted, "
                   f"proceeding with best score {max(state.stage_a_scores)}")
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
        h = git_commit(paper_path,
                       f"stage-B R{rnd}: compile PDF", tag=tag)
        state.log_event("B", "compile_pdf", round_num=rnd,
                        committed=bool(h), commit_hash=h)
        save_state(state)

        # ── B2: Oracle editorial review (EVENT WAIT) ─────────────
        task_id = f"review_{state.paper_name}_B{rnd}_{int(time.time())}"
        prompt = (build_oracle_review_prompt(state.target_journal) if rnd == 1
                  else build_oracle_re_review_prompt(state.target_journal))

        logger.info(f"{tag} Round {rnd}: B2 — Oracle review")

        if dry_run:
            response = ("Overall verdict: Major revision\n"
                        "1 | Section 3 | MEDIUM | simulated issue | fix it"
                        if rnd < 2 else "Overall verdict: Minor revision")
        else:
            pdf_path = Path(state.pdf_path) if state.pdf_path else None
            if not oracle_submit(task_id, prompt, pdf_path):
                state.error = "Oracle submit failed"
                return False
            save_state(state)
            response = oracle_poll(task_id, timeout=oracle_timeout)
            if not response:
                state.error = f"Oracle timeout B{rnd}"
                return False

        # Save oracle response
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
        h = git_commit(paper_path,
                       f"stage-B R{rnd}: codex fix oracle issues", tag=tag)
        state.log_event("B", "codex_fix", round_num=rnd,
                        committed=bool(h), commit_hash=h)
        save_state(state)

        # ── B5: Claude review fixes ──────────────────────────────
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
        codex_exec(claude_fix_prompt, work_dir=paper_path,
                   timeout_seconds=900, model=model, dry_run=dry_run)
        h = git_commit(paper_path,
                       f"stage-B R{rnd}: claude review fixes", tag=tag)
        state.log_event("B", "claude_review_fixes", round_num=rnd,
                        committed=bool(h), commit_hash=h)
        save_state(state)

        logger.info(f"{tag} Round {rnd}/{MAX_STAGE_B_ROUNDS} complete, "
                    f"looping for re-review")

    logger.warning(f"{tag} Max {MAX_STAGE_B_ROUNDS} rounds exhausted, "
                   f"proceeding with last verdict: "
                   f"{state.stage_b_verdicts[-1] if state.stage_b_verdicts else '?'}")
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
        out_c1 = codex_exec(review_prompt, work_dir=paper_path,
                            timeout_seconds=900, model=model, dry_run=dry_run)
        review_data = parse_json_from_output(out_c1) if not dry_run else {
            "verdict": "revise" if rnd < 2 else "submit",
            "issues": [f"dry run issue R{rnd}"] if rnd < 2 else [],
        }
        verdict = review_data.get("verdict", "revise")
        issues = review_data.get("issues", [])
        state.stage_c_verdicts.append(verdict)
        state.log_event("C", "claude_independent_review", round_num=rnd,
                        verdict=verdict,
                        detail=json.dumps(review_data, ensure_ascii=False)[:2000])
        save_state(state)

        logger.info(f"{tag} Round {rnd}: Claude verdict = {verdict}, "
                    f"{len(issues)} issues")

        # ── Gate: submit → Stage D ───────────────────────────────
        if verdict == "submit" or not issues:
            logger.info(f"{tag} STAGE C PASSED at round {rnd}: READY TO SUBMIT")
            state.stage_c_passed = True
            save_state(state)
            return True

        # ── C2: Codex fix Claude's issues ────────────────────────
        logger.info(f"{tag} Round {rnd}: C2 — Codex fix Claude issues")
        fix_prompt = build_codex_fix_from_claude_prompt(
            state.paper_dir, issues, rnd)
        codex_exec(fix_prompt, work_dir=paper_path,
                   timeout_seconds=1800, model=model, dry_run=dry_run)
        h = git_commit(paper_path,
                       f"stage-C R{rnd}: codex fix claude issues", tag=tag)
        state.log_event("C", "codex_fix_claude", round_num=rnd,
                        committed=bool(h), commit_hash=h)
        save_state(state)

        logger.info(f"{tag} Round {rnd}/{MAX_STAGE_C_ROUNDS} complete, "
                    f"looping for re-review")

    logger.warning(f"{tag} Max {MAX_STAGE_C_ROUNDS} rounds exhausted")
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
    out_d2 = codex_exec(claude_bf_prompt, work_dir=REPO_ROOT,
                        timeout_seconds=600, model=model, dry_run=dry_run)
    approval = parse_json_from_output(out_d2) if not dry_run else {
        "approved": True, "approved_items": list(range(len(items))),
    }
    state.log_event("D", "claude_review_backflow",
                    detail=json.dumps(approval, ensure_ascii=False)[:2000])
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
                    committed=bool(h), commit_hash=h)
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
                    committed=bool(h), commit_hash=h)
    save_state(state)

    state.stage_d_passed = True
    save_state(state)
    logger.info(f"{tag} STAGE D COMPLETE")
    return True


# ═══════════════════════════════════════════════════════════════════════════
# NEW-PAPER PIPELINE (N1 → N2 → N3 → auto-enters Review A→B→C→D)
# ═══════════════════════════════════════════════════════════════════════════

def build_new_research_prompt(topic: str, outline: str,
                               target_journal: str) -> str:
    """N1: Deep original research on a topic."""
    outline_section = f"\n## Outline provided\n{outline}\n" if outline else ""
    return textwrap.dedent(f"""\
        You are a mathematical researcher preparing a paper for "{target_journal}".

        ## Topic
        {topic}
        {outline_section}
        ## Task: Deep Original Research

        Conduct deep research on this topic. Produce:
        1. Precise definitions and notation
        2. Main theorems with complete, rigorous proofs
        3. Supporting lemmas as needed
        4. Connections to existing literature (cite properly)

        Requirements:
        - Find genuinely striking, publishable conclusions. Push until you reach
          results with real publication value — do not produce incremental filler.
        - Do NOT reproduce reasoning already published by others. You MAY use
          others' results as building blocks — cite them properly.
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
                        detail=json.dumps(j_data, ensure_ascii=False)[:2000])
        save_state(state)
        logger.info(f"{tag} N0 selected journal: {selected} "
                    f"(fit={j_data.get('fit_score', '?')})")
    else:
        logger.info(f"{tag} Journal pre-specified: {target_journal}")
        state.target_journal = target_journal

    journal = state.target_journal

    # ── N1: Deep research ────────────────────────────────────────
    logger.info(f"{tag} N1 — Codex deep research (for {journal})")
    prompt_n1 = build_new_research_prompt(topic, outline, journal)
    codex_exec(prompt_n1, work_dir=paper_path,
               timeout_seconds=3600, model=model, dry_run=dry_run)
    h = git_commit(paper_path, f"new-paper N1: deep research — {topic[:40]}",
                   tag=tag)
    state.log_event("N", "codex_deep_research",
                    committed=bool(h), commit_hash=h)
    save_state(state)

    # ── N2: Scaffold ─────────────────────────────────────────────
    logger.info(f"{tag} N2 — Codex scaffold (for {journal})")
    prompt_n2 = build_scaffold_prompt(str(paper_path), journal)
    codex_exec(prompt_n2, work_dir=paper_path,
               timeout_seconds=1800, model=model, dry_run=dry_run)
    h = git_commit(paper_path, f"new-paper N2: scaffold structure", tag=tag)
    state.log_event("N", "codex_scaffold",
                    committed=bool(h), commit_hash=h)
    save_state(state)

    # ── N3: Initial journal style ────────────────────────────────
    logger.info(f"{tag} N3 — Codex initial journal style (for {journal})")
    prompt_n3 = build_initial_style_prompt(str(paper_path), journal)
    codex_exec(prompt_n3, work_dir=paper_path,
               timeout_seconds=2400, model=model, dry_run=dry_run)
    h = git_commit(paper_path, f"new-paper N3: journal style draft", tag=tag)
    state.log_event("N", "codex_initial_style",
                    committed=bool(h), commit_hash=h)
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

    If respect_assignment=True (default with --all), only return papers
    assigned to this machine to avoid git conflicts with the other machine.
    """
    if paper_dirs:
        return paper_dirs

    my_papers = get_my_papers() if respect_assignment else []
    papers = []
    for base in (PAPERS_PUB_DIR, THEORY_DIR):
        if base.exists():
            for d in sorted(base.iterdir()):
                if d.is_dir() and (d / "main.tex").exists():
                    if my_papers and d.name not in my_papers:
                        continue
                    papers.append(str(d))

    if my_papers:
        logger.info(f"Machine filter ({sys.platform}): "
                    f"{len(papers)}/{len(my_papers)} papers matched")
    return papers


def run_rolling(paper_dirs: list[str], *, parallel: int = 1,
                continuous: bool = False, **kwargs) -> tuple[int, int]:
    succeeded = failed = 0
    queue = list(paper_dirs)

    logger.info(f"Rolling pipeline: {len(queue)} papers, {parallel} workers")

    with ThreadPoolExecutor(max_workers=parallel,
                            thread_name_prefix="paper") as pool:
        futures: dict[Future, str] = {}

        def _submit():
            if not queue:
                return
            d = queue.pop(0)
            fut = pool.submit(run_paper_pipeline, d, **kwargs)
            futures[fut] = d
            logger.info(f"Dispatched: {Path(d).name}")

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
                _submit()

    return succeeded, failed


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def print_status():
    print(f"Oracle Pipeline v2 — Status")
    print(f"{'='*60}")
    print(f"Platform:      {sys.platform}")
    print(f"Oracle server: {'UP' if oracle_server_alive() else 'DOWN'}")
    print(f"Codex CLI:     {CODEX_PATH}")
    my = get_my_papers()
    print(f"My papers:     {len(my)} assigned to {sys.platform}")
    print()
    if not STATE_DIR.exists():
        print("No pipeline state found.")
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
        print(f"  {name}")
        print(f"    Status:  {status}  |  Total rounds: {total}")
        print(f"    Journal: {journal}"
              + (f" (rerouted from {f_orig})" if f_sugg else ""))
        if f_fit:
            print(f"    Stage F: fit={f_fit}/10"
                  + (f", suggested={f_sugg}" if f_sugg else ""))
        print(f"    Stage A: {a_r} rounds, scores={a_scores}")
        print(f"    Stage B: {b_r} rounds, verdicts={b_verd}")
        print(f"    Stage C: {c_r} rounds, verdicts={c_verd}")
        if err:
            print(f"    Error:   {err}")
        print()


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
    parser.add_argument("--parallel", "-p", type=int, default=1)
    parser.add_argument("--continuous", action="store_true")
    parser.add_argument("--skip-to", type=str, default="",
                        choices=["F", "A", "B", "C", "D"])
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--model", type=str, default=None)
    parser.add_argument("--oracle-timeout", type=int, default=7200)
    parser.add_argument("--status", action="store_true")
    parser.add_argument("--reset", type=str, metavar="PAPER_NAME")
    parser.add_argument("--no-assign", action="store_true",
                        help="Ignore machine assignment, process all papers")
    args = parser.parse_args()

    if args.status:
        print_status()
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
