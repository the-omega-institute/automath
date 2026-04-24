#!/usr/bin/env python3
"""Community outreach pipeline for GitHub mathematical contributions.

Workflow:
  Stage A  discovery via gh search repos + Codex/Claude candidate review
  Stage B  deep mathematical research, score-gated (>= 8), max 5 rounds
  Stage C  issue/reply/proposal drafting in Tolmeton style + review gate
  Stage D  interactive approval gate + gh issue create

The script reuses subprocess/state patterns from tools/chatgpt-oracle/oracle_pipeline.py,
but this pipeline has no oracle dependency:
  - structured logging to stdout + file
  - dataclass-backed JSON state persistence
  - subprocess wrappers for codex / claude / gh / git
  - dry-run support for end-to-end verification
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
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

try:
    import fcntl
except ImportError:  # pragma: no cover - Windows fallback
    fcntl = None


# ---------------------------------------------------------------------------
# Paths & constants
# ---------------------------------------------------------------------------

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
LOG_DIR = SCRIPT_DIR / "logs"
STATE_DIR = SCRIPT_DIR / "outreach_state"
CANDIDATES_FILE = STATE_DIR / "candidates.json"
PROCESSED_FILE = STATE_DIR / "processed.json"
GIT_OPS_LOCK = STATE_DIR / ".git_ops.lock"
FUTURE_QUEUE_FILE = STATE_DIR / "future_queue.jsonl"

OUTREACH_STATE_SCHEMA_VERSION = "community-outreach-state-v2"
OUTREACH_CONTRACT_SCHEMA_VERSION = "community-outreach-contract-v1"
FUTURE_QUEUE_SCHEMA_VERSION = "community-outreach-future-v1"
INTERMEDIATE_PATH_PREFIXES = (
    "tools/community-outreach/outreach_state/",
    "tools/community-outreach/logs/",
    "tools/community-outreach/targets/",
    "tools/community-outreach/drafts/",
)

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

BAD_EXAMPLE_DEEP_RESEARCH_STANDARD_ZH = """深度研究升级规则: 研究范式切换为“坏例子结构定理驱动”。
先锁定主命题可能失败的最坏反例；再证明坏例子必然落入少数可分类骨架；再对这些骨架分别建立结构定理、分解定理、预算下界、粘接障碍或归纳矛盾；最后只输出能够闭合的定理—推论—命题—猜想链条。
优先使用 fold-aware restriction 与稳定逆系统、伪不变量剔除、近最大纤维族 sticky 骨架、高阶矩冻结与 escort 集中、Čech 粘接障碍、离散 holonomy 与曲率证书、boundary/Walsh-Stokes/Euler 型证书、prime-register/外置账本与无限预算下界、局部可解而全局不可粘接的对象分类。
禁止同义改写、旧结果换壳、只换符号/常数/指标的弱变体、仅计算例子、仅启发式论证。凡涉及跨分辨率对象，必须在 fold-aware gauge、稳定逆系统或合法等价表述下工作，显式避免朴素截断幻觉。
本管线需要 JSON 输出；上述规则作为内部研究约束执行，不要破坏要求的 JSON schema。"""

NO_LEAN_EXECUTION_POLICY = """NO-LEAN-EXECUTION POLICY:
- This outreach pipeline must not assume a local Lean environment.
- Do not run `lake`, `lean`, `elan`, `#eval`, `#check`, or any Lean compiler/checker command.
- Do not create, edit, or patch files under lean4/ or in the target repository.
- Lean files may be read only as static text evidence with cat/rg/sed.
- Existing committed Lean theorem refs may be cited as prior evidence, but new claims must be justified by mathematical proof text or Python/combinatorial certificates.
- If a result needs Lean formalization, mark it as a future external verification prerequisite, not as completed by this pipeline."""

AGENT_CONTEXT_POLICY = """AGENT CONTEXT POLICY:
- context_aware: use for planning, continued research, scope judgment, and target-facing draft review. Load the scope ledger, prior contribution record, deferred future items, and current issue boundary.
- zero_init_review: use for independent correctness/tone review after a candidate artifact exists. Do not rely on local outreach memory; judge only the public draft plus committed evidence supplied in the prompt.
- Every agent call must say which mode it is using. Do not mix scope-memory work with zero-initialized review in one prompt."""

RESEARCH_ROUTE_POLICY = """RESEARCH ROUTE POLICY:
- Every future-scope research task must declare exactly one route before doing substantive work: computation, proof, or hybrid.
- computation: use when the scope is a finite certificate, matrix/table audit, bounded search, or counterexample enumeration. Output scripts/certificates, input data, reproducibility instructions, and failure conditions.
- proof: use when the scope asks for an all-q theorem, classification, rigidity/obstruction result, or formal mathematical chain. Output theorem statements with complete proof text; computation may only be auxiliary evidence.
- hybrid: use when finite computation is needed to find, certify, or exclude structures before proving the resulting obstruction/theorem. Output both the certificate artifacts and the proof that interprets them.
- If the scope ledger supplies a recommended route, follow it unless you explicitly justify a route override. Never replace proof obligations with numerical evidence."""

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
    outreach_kind: str = ""
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
            "schema_version": OUTREACH_STATE_SCHEMA_VERSION,
            "repo": self.repo,
            "stage": self.stage,
            "round": self.round,
            "scores": self.scores,
            "findings": self.findings,
            "draft_title": self.draft_title,
            "draft_body": self.draft_body,
            "outreach_kind": self.outreach_kind,
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
        state.outreach_kind = data.get("outreach_kind", "")
        state.action_history = data.get("action_history", data.get("events", []))
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
    """Convert 'owner/name' or 'owner/name#123' to a filesystem-safe slug.
    Issue number creates isolated context: owner_name_123."""
    return repo.replace("/", "_").replace("#", "_")


def repo_base(repo: str) -> str:
    """Extract the base repo 'owner/name' from 'owner/name#123'."""
    return repo.split("#")[0]


def repo_issue(repo: str) -> Optional[int]:
    """Extract issue number from 'owner/name#123', or None."""
    if "#" in repo:
        try:
            return int(repo.split("#")[1])
        except (ValueError, IndexError):
            pass
    return None


def state_file(repo: str) -> Path:
    return STATE_DIR / f"{repo_slug(repo)}.json"


def target_dir_for_repo(repo: str) -> Path:
    return SCRIPT_DIR / "targets" / repo_slug(repo)


def _repo_relative(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REPO_ROOT.resolve()))
    except Exception:
        return str(path)


def _rel_from_any(path: str | Path) -> str:
    raw = Path(path)
    if raw.is_absolute():
        return _repo_relative(raw)
    return str(raw).replace("\\", "/").lstrip("./")


def is_intermediate_path(path: str | Path) -> bool:
    rel = _rel_from_any(path)
    return any(rel == prefix.rstrip("/") or rel.startswith(prefix) for prefix in INTERMEDIATE_PATH_PREFIXES)


@contextlib.contextmanager
def git_ops_lock() -> Any:
    """Serialize state/backflow commits across parallel workers."""
    if IS_WINDOWS or fcntl is None:
        yield
        return

    GIT_OPS_LOCK.parent.mkdir(parents=True, exist_ok=True)
    with open(GIT_OPS_LOCK, "w", encoding="utf-8") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def git_status_porcelain(paths: list[Path]) -> list[str]:
    if not paths:
        return []
    args = [_repo_relative(path) for path in paths]
    try:
        result = subprocess.run(
            ["git", "status", "--porcelain", "--", *args],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=30,
            encoding="utf-8",
            errors="replace",
        )
    except Exception:
        return []
    if result.returncode != 0:
        return []
    return [line for line in result.stdout.splitlines() if line.strip()]


def backflow_placement_from_history(state: RepoState) -> Optional[dict[str, Any]]:
    for evt in reversed(state.action_history):
        if evt.get("action") != "backflow completed":
            continue
        try:
            payload = json.loads(evt.get("detail", "{}"))
        except (json.JSONDecodeError, TypeError):
            continue
        if isinstance(payload, dict) and payload.get("placement") and payload.get("section_dir"):
            return payload
    return None


def infer_outreach_kind(repo: str, backflow_placement: Optional[dict[str, Any]]) -> str:
    """Classify the public outreach surface for a draft.

    issue_reply: state is tied to a known upstream issue.
    proposal: discovery produced a paper-side artifact that should be opened as
      a scoped question/proposal, not as a claimed finished PR.
    issue: default standalone issue for a target repo.
    """
    if repo_issue(repo) is not None:
        return "issue_reply"
    section_dir = str((backflow_placement or {}).get("section_dir", "") or "")
    if section_dir == "finite_conditional_expectation":
        return "proposal"
    if backflow_placement:
        return "issue"
    return "unspecified"


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


def _json_sha(payload: Any, length: int = 16) -> str:
    raw = json.dumps(payload, sort_keys=True, ensure_ascii=False, default=str)
    return hashlib.sha1(raw.encode("utf-8")).hexdigest()[:length]


def future_queue_events() -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    if not FUTURE_QUEUE_FILE.exists():
        return events
    for line in FUTURE_QUEUE_FILE.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            item = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(item, dict):
            events.append(item)
    return events


def _future_item_id(item: dict[str, Any]) -> str:
    payload = {
        "source_repo": item.get("source_repo") or item.get("target_repo", ""),
        "title": item.get("title", ""),
        "task": item.get("task", ""),
    }
    return _json_sha(payload, length=18)


def _future_source_fingerprint(item: dict[str, Any], source: dict[str, Any]) -> str:
    payload = {
        "id": item.get("id") or _future_item_id(item),
        "source_repo": source.get("repo", item.get("source_repo", "")),
        "source_stage": source.get("stage", ""),
        "source_title": source.get("draft_title", source.get("title", "")),
        "scope_boundary": item.get("scope_boundary", ""),
        "task": item.get("task", ""),
    }
    return _json_sha(payload, length=18)


def infer_research_route(item: dict[str, Any]) -> tuple[str, str, str]:
    """Infer a conservative route from a future item when the scope did not store one."""
    text = " ".join(
        str(item.get(key, ""))
        for key in ("title", "task", "scope_boundary", "evidence")
    ).lower()
    has_lift_terms = any(term in text for term in ("nonnegative", "flow-equivalence", "bowen-franks", "sft"))
    has_all_q_terms = any(term in text for term in ("all-q", "all q", "all-`q`", "classification", "structure theorem", "obstruction theorem"))
    if has_all_q_terms and not has_lift_terms:
        return (
            "proof",
            "The scope asks for an unbounded theorem/classification rather than only a finite audit.",
            "Produce formal theorem/proposition statements with complete proof text; use computation only as auxiliary exploration.",
        )
    if has_lift_terms or "certificate" in text:
        return (
            "hybrid",
            "The scope asks for concrete certificate data but also requires a mathematical obstruction or interpretation.",
            "Produce reproducible Python/certificate artifacts and a proof explaining why the artifact gives a lift or obstruction.",
        )
    if has_all_q_terms:
        return (
            "proof",
            "The scope asks for an unbounded theorem/classification rather than only a finite audit.",
            "Produce formal theorem/proposition statements with complete proof text; use computation only as auxiliary exploration.",
        )
    if any(term in text for term in ("bounded", "q=2..", "table", "finite", "enumeration", "counterexample")):
        return (
            "computation",
            "The scope is a finite bounded audit or enumeration certificate.",
            "Produce scripts, input data, JSON/certificate output, and reproducibility/failure checks.",
        )
    return (
        "hybrid",
        "The scope does not determine a pure proof or pure computation route, so use a conservative hybrid contract.",
        "Declare which parts are certificate-backed and which parts are theorem/proof obligations.",
    )


def normalize_future_item_route(item: dict[str, Any]) -> dict[str, Any]:
    route, reason, contract = infer_research_route(item)
    item.setdefault("research_route", route)
    item.setdefault("route_reason", reason)
    item.setdefault("route_contract", contract)
    return item


def load_future_queue() -> list[dict[str, Any]]:
    """Compact the append-only local future queue into current items."""
    items: dict[str, dict[str, Any]] = {}
    for event in future_queue_events():
        item_id = str(event.get("id", "")).strip()
        if not item_id:
            continue
        event_type = str(event.get("event_type", "queued"))
        if event_type == "queued":
            base = dict(event)
            base.setdefault("source_records", [])
            if base.get("source") and not base["source_records"]:
                base["source_records"].append(base["source"])
            base.setdefault("updates", [])
            normalize_future_item_route(base)
            items[item_id] = base
            continue

        base = items.setdefault(
            item_id,
            {
                "id": item_id,
                "schema_version": FUTURE_QUEUE_SCHEMA_VERSION,
                "event_type": "queued",
                "status": event.get("status", "queued"),
                "source_repo": event.get("source_repo", ""),
                "title": event.get("title", ""),
                "task": event.get("task", ""),
                "source_records": [],
                "updates": [],
            },
        )
        if event.get("status"):
            base["status"] = event["status"]
        if event.get("updated_at"):
            base["updated_at"] = event["updated_at"]
        for key in ("research_route", "route_reason", "route_contract", "recommended_agent_context", "priority"):
            if event.get(key):
                base[key] = event[key]
        for source in event.get("source_records", []):
            if source not in base["source_records"]:
                base["source_records"].append(source)
        base["updates"].append(event)
        normalize_future_item_route(base)
    return sorted(items.values(), key=lambda item: (item.get("source_repo", ""), item.get("title", "")))


def future_items_for_repo(repo: str, *, include_done: bool = False) -> list[dict[str, Any]]:
    keys = {repo, repo_base(repo)}
    issue = repo_issue(repo)
    matches: list[dict[str, Any]] = []
    for item in load_future_queue():
        status = str(item.get("status", "queued"))
        if status in {"done", "closed", "dropped"} and not include_done:
            continue
        source_repo = str(item.get("source_repo", ""))
        target_repo = str(item.get("target_repo", ""))
        source_issue = item.get("source_issue")
        item_keys = {source_repo, target_repo, repo_base(source_repo) if source_repo else ""}
        if keys.isdisjoint(item_keys):
            continue
        if issue is not None and source_issue not in {None, "", issue}:
            continue
        if issue is not None and source_issue in {None, ""} and repo not in item_keys:
            continue
        matches.append(item)
    return matches


def append_future_queue_item(item: dict[str, Any], *, dry_run: bool = False) -> bool:
    source = dict(item.pop("source", {}) or {})
    entry = dict(item)
    entry.setdefault("schema_version", FUTURE_QUEUE_SCHEMA_VERSION)
    entry.setdefault("event_type", "queued")
    entry.setdefault("status", "queued")
    entry.setdefault("created_at", iso_now())
    entry["updated_at"] = iso_now()
    entry.setdefault("source_repo", source.get("repo", ""))
    entry.setdefault("target_repo", repo_base(str(entry.get("source_repo", ""))))
    entry.setdefault("source_issue", source.get("issue"))
    normalize_future_item_route(entry)
    entry["id"] = str(entry.get("id") or _future_item_id(entry))
    source_fingerprint = _future_source_fingerprint(entry, source)
    entry["source_records"] = [source] if source else []
    entry["source_fingerprint"] = source_fingerprint

    existing_events = future_queue_events()
    if any(
        event.get("id") == entry["id"] and event.get("source_fingerprint") == source_fingerprint
        for event in existing_events
    ):
        return False

    if any(event.get("id") == entry["id"] for event in existing_events):
        event = {
            "schema_version": FUTURE_QUEUE_SCHEMA_VERSION,
            "event_type": "append",
            "id": entry["id"],
            "updated_at": iso_now(),
            "source_repo": entry.get("source_repo", ""),
            "target_repo": entry.get("target_repo", ""),
            "source_issue": entry.get("source_issue"),
            "title": entry.get("title", ""),
            "task": entry.get("task", ""),
            "status": entry.get("status", "queued"),
            "research_route": entry.get("research_route"),
            "route_reason": entry.get("route_reason"),
            "route_contract": entry.get("route_contract"),
            "recommended_agent_context": entry.get("recommended_agent_context"),
            "priority": entry.get("priority"),
            "source_records": entry["source_records"],
            "source_fingerprint": source_fingerprint,
        }
    else:
        event = entry

    logger.info("Future queue %s: %s", "would append" if dry_run else "append", entry["title"])
    if dry_run:
        return True
    with _state_lock:
        FUTURE_QUEUE_FILE.parent.mkdir(parents=True, exist_ok=True)
        with open(FUTURE_QUEUE_FILE, "a", encoding="utf-8") as handle:
            handle.write(json.dumps(event, ensure_ascii=False, sort_keys=True) + "\n")
    return True


def append_future_queue_note(
    item_id: str,
    note: str,
    *,
    source_repo: str = "",
    status: Optional[str] = None,
    dry_run: bool = False,
) -> bool:
    existing = {item["id"]: item for item in load_future_queue()}
    if item_id not in existing:
        raise RuntimeError(f"Unknown future queue id: {item_id}")
    event = {
        "schema_version": FUTURE_QUEUE_SCHEMA_VERSION,
        "event_type": "append_note",
        "id": item_id,
        "updated_at": iso_now(),
        "source_repo": source_repo or existing[item_id].get("source_repo", ""),
        "target_repo": repo_base(source_repo or existing[item_id].get("source_repo", "")),
        "status": status or existing[item_id].get("status", "queued"),
        "note": note,
        "source_records": [
            {
                "repo": source_repo,
                "stage": "manual",
                "note": note,
                "recorded_at": iso_now(),
            }
        ],
        "source_fingerprint": _json_sha({"id": item_id, "note": note, "source_repo": source_repo}, length=18),
    }
    if any(
        old.get("id") == item_id and old.get("source_fingerprint") == event["source_fingerprint"]
        for old in future_queue_events()
    ):
        return False
    logger.info("Future queue note %s: %s", "would append" if dry_run else "append", item_id)
    if dry_run:
        return True
    with _state_lock:
        FUTURE_QUEUE_FILE.parent.mkdir(parents=True, exist_ok=True)
        with open(FUTURE_QUEUE_FILE, "a", encoding="utf-8") as handle:
            handle.write(json.dumps(event, ensure_ascii=False, sort_keys=True) + "\n")
    return True


def _scope_excerpt(text: str, pattern: str, *, radius: int = 260) -> str:
    match = re.search(pattern, text, flags=re.IGNORECASE | re.DOTALL)
    if not match:
        return text[: min(len(text), radius)]
    start = max(0, match.start() - radius)
    end = min(len(text), match.end() + radius)
    return " ".join(text[start:end].split())


def future_scope_items_from_state(
    state: RepoState,
    *,
    contract: Optional[dict[str, Any]] = None,
) -> list[dict[str, Any]]:
    """Extract deferred-but-valuable research tasks from a scoped public draft."""
    body = state.draft_body or ""
    if not body.strip():
        return []
    lower = body.lower()
    source = {
        "repo": state.repo,
        "base_repo": repo_base(state.repo),
        "issue": repo_issue(state.repo),
        "stage": state.stage,
        "draft_title": state.draft_title,
        "state_file": _repo_relative(state_file(state.repo)),
        "backflow": backflow_placement_from_history(state) or {},
        "contract_approved": bool((contract or {}).get("approved")),
        "recorded_at": iso_now(),
    }
    current_scope = (
        "The public reply should close only the confirmed, paper-side scope of the current issue. "
        "Deferred items remain research tasks until separately proved, backflowed, and reviewed."
    )
    items: list[dict[str, Any]] = []

    signed_companion_scope = "signed companion" in lower and ("q=2" in lower or "q=6" in lower or "q=7" in lower)
    if signed_companion_scope and any(term in lower for term in ["nonnegative", "bowen-franks", "flow-equivalence", "sft"]):
        items.append(
            {
                "title": "Nonnegative lift and flow-equivalence certificate for q=6,7 signed companions",
                "task": (
                    "Determine whether the q=6,7 signed-companion proxies admit nonnegative presentations "
                    "preserving the audited determinant/exterior-square data. If yes, construct the presentation "
                    "and a Bowen-Franks/SFT flow-equivalence certificate; if no, prove the obstruction in the "
                    "paper's fold-aware/stable inverse-system language."
                ),
                "current_scope": current_scope,
                "scope_boundary": (
                    "Issue #38 reply closes the bounded signed-companion coefficient audit and q=2..23 "
                    "exterior-Lucas certificate. It does not claim a nonnegative collision-kernel presentation, "
                    "Bowen-Franks invariant, or SFT flow-equivalence result."
                ),
                "evidence": _scope_excerpt(body, r"not claimed|nonnegative|Bowen-Franks|flow-equivalence|SFT"),
                "priority": "high",
                "recommended_agent_context": "context_aware_research",
                "research_route": "hybrid",
                "route_reason": (
                    "A finite q=6,7 lift/obstruction needs computation or explicit certificate data, "
                    "but BF/SFT promotion also requires a proof interpreting the certificate."
                ),
                "route_contract": (
                    "Produce reproducible scripts/certificates for candidate nonnegative presentations or "
                    "failed searches, plus a proof that the resulting certificate gives a valid lift or obstruction."
                ),
                "review_policy": (
                    "Use context-aware agents for the proof search because the scope boundary and paper-side "
                    "artifacts matter; use zero_init_review only after a standalone certificate is drafted."
                ),
                "source": source,
            }
        )

    if signed_companion_scope and any(term in lower for term in ["q=2,...,23", "q=2..23", "q=2, ..., 23", "q=23"]):
        items.append(
            {
                "title": "All-q obstruction to exterior-Lucas continuation beyond q=5",
                "task": (
                    "Upgrade the bounded q=2..23 exterior-Lucas certificate into either an all-q obstruction "
                    "theorem or a classified bad-example mechanism. The preferred route is a bad-example "
                    "structure theorem: locate the worst possible continuation failure, force it into a "
                    "small skeleton, then close the obstruction with a fold-aware or stable inverse-system "
                    "argument."
                ),
                "current_scope": current_scope,
                "scope_boundary": (
                    "The current outreach reply only reports the finite q=2..23 certificate and the isolated "
                    "q=5 triple coincidence in that audited range. It does not assert an all-q classification."
                ),
                "evidence": _scope_excerpt(body, r"q=2.*23|q=23|exterior-Lucas|triple coincidence"),
                "priority": "high",
                "recommended_agent_context": "context_aware_research",
                "research_route": "proof",
                "route_reason": (
                    "The task asks to upgrade a bounded q=2..23 certificate into an all-q obstruction "
                    "or classified bad-example theorem."
                ),
                "route_contract": (
                    "Produce theorem/proposition statements with complete proof text. Computation may be used "
                    "to identify candidate skeletons but cannot replace the all-q argument."
                ),
                "review_policy": (
                    "Start with context-aware research using the paper artifacts and prior scope ledger. "
                    "A later zero_init_review should check any final theorem statement independently."
                ),
                "source": source,
            }
        )

    if items:
        return items

    deferred_lines = [
        line.strip(" -")
        for line in body.splitlines()
        if re.search(r"\b(not claimed|future|separate|out[- ]of[- ]scope|requires separate)\b", line, flags=re.IGNORECASE)
    ]
    if deferred_lines:
        items.append(
            {
                "title": f"Deferred scope from {state.draft_title or state.repo}",
                "task": "Resolve the explicitly deferred claims from the scoped outreach draft.",
                "current_scope": current_scope,
                "scope_boundary": "The draft explicitly separates current claims from deferred work.",
                "evidence": " ".join(deferred_lines[:4])[:1200],
                "priority": "medium",
                "recommended_agent_context": "context_aware_research",
                "research_route": "hybrid",
                "route_reason": "Deferred scope did not specify whether the remaining work is purely finite or theorem-level.",
                "route_contract": "Declare the route at task start and separate certificate claims from proof obligations.",
                "review_policy": "Use context-aware agents for continuation; use zero_init_review for final public text.",
                "source": source,
            }
        )
    return items


def record_future_scope_items(
    state: RepoState,
    *,
    contract: Optional[dict[str, Any]] = None,
    dry_run: bool = False,
) -> int:
    items = future_scope_items_from_state(state, contract=contract)
    added = 0
    for item in items:
        if append_future_queue_item(item, dry_run=dry_run):
            added += 1
    return added


def agent_context_header(mode: str, scope_context: str = "") -> str:
    normalized = mode.strip().lower()
    if normalized not in {"context_aware", "zero_init_review"}:
        normalized = "context_aware"
    header = f"{AGENT_CONTEXT_POLICY}\n\n{RESEARCH_ROUTE_POLICY}\n\nAGENT_CONTEXT_MODE: {normalized}\n"
    if normalized == "context_aware":
        header += (
            "Use the scope ledger below to distinguish already-closed contribution scope "
            "from deferred future research. Do not turn deferred tasks into current claims.\n"
        )
        if scope_context:
            header += "\n" + scope_context + "\n"
    else:
        header += (
            "Ignore local outreach memory unless it appears as committed/public evidence in this prompt. "
            "This is a cold independent review.\n"
        )
    return header


def build_scope_context(repo: str, state: Optional[RepoState] = None, *, max_chars: int = 4500) -> str:
    state = state or load_state(repo)
    queue = future_items_for_repo(repo)
    if not state and not queue:
        return ""

    lines = [
        "SCOPE LEDGER (local ignored outreach memory; not public evidence by itself):",
        f"- Target: {repo}",
    ]
    if state:
        lines.append(f"- Current state: stage={state.stage}, round={state.round}")
        if state.draft_title:
            lines.append(f"- Current/last draft title: {state.draft_title}")
        backflow = backflow_placement_from_history(state)
        if backflow:
            lines.append(
                "- Paper-side contribution already backflowed: "
                f"{backflow.get('placement')}/{backflow.get('section_dir')}"
            )
        if state.submission_url:
            lines.append(f"- Submitted issue/reply: {state.submission_url}")
        if state.error:
            lines.append(f"- Current blocker: {state.error[:300]}")

    if queue:
        lines.append("- Deferred future research items:")
        for item in queue[:6]:
            lines.append(
                f"  * [{item.get('id')}] {item.get('title')} "
                f"(priority={item.get('priority', 'medium')}, route={item.get('research_route', 'hybrid')}, "
                f"agent={item.get('recommended_agent_context', 'context_aware_research')})"
            )
            if item.get("scope_boundary"):
                lines.append(f"    scope_boundary: {str(item.get('scope_boundary'))[:500]}")
            if item.get("route_contract"):
                lines.append(f"    route_contract: {str(item.get('route_contract'))[:500]}")
            if item.get("task"):
                lines.append(f"    task: {str(item.get('task'))[:500]}")
    lines.append(
        "- Interaction rule: close only the current verified scope in public replies; "
        "queue ambitious or unproved extensions for later runs."
    )
    return "\n".join(lines)[:max_chars]


def print_future_queue(filter_repos: Optional[list[str]] = None) -> None:
    items = load_future_queue()
    if filter_repos:
        keys = set(filter_repos) | {repo_base(repo) for repo in filter_repos}
        items = [
            item for item in items
            if item.get("source_repo") in keys or item.get("target_repo") in keys
        ]
    print(f"Future queue items: {len(items)}")
    for item in items:
        print(f"{item.get('id')}  {item.get('source_repo')}  {item.get('title')}")
        print(f"  Status:   {item.get('status', 'queued')}")
        print(f"  Priority: {item.get('priority', 'medium')}")
        print(f"  Route:    {item.get('research_route', 'hybrid')}")
        print(f"  Contract: {str(item.get('route_contract', ''))[:300]}")
        print(f"  Agent:    {item.get('recommended_agent_context', 'context_aware_research')}")
        if item.get("scope_boundary"):
            print(f"  Scope:    {str(item.get('scope_boundary'))[:240]}")
        print(f"  Task:     {str(item.get('task', ''))[:360]}")
        print("")


def mark_repo_replied(repo: str, url: str, *, dry_run: bool = False) -> RepoState:
    state = load_state(repo) or RepoState(repo=repo)
    state.stage = "DONE"
    state.round = 0
    state.error = ""
    state.submission_url = url
    state.timestamps["completed_at"] = iso_now()
    state.log_event("D", "issue reply submitted", verdict="approve", detail=url)
    if not dry_run:
        save_state(state)
        mark_processed(repo, dry_run=dry_run)
    logger.info("[%s] Marked replied: %s", repo, url)
    return state


def find_future_item(item_id: str) -> dict[str, Any]:
    matches = [item for item in load_future_queue() if str(item.get("id", "")).startswith(item_id)]
    if not matches:
        raise RuntimeError(f"Unknown future queue item: {item_id}")
    if len(matches) > 1:
        raise RuntimeError(f"Ambiguous future queue item prefix {item_id}: {[item.get('id') for item in matches]}")
    return normalize_future_item_route(matches[0])


def future_research_dir(item: dict[str, Any]) -> Path:
    repo = str(item.get("source_repo") or item.get("target_repo") or "future")
    return target_dir_for_repo(repo) / "future" / str(item.get("id", "unknown"))


def prior_future_research_context(research_dir: Path, *, max_chars: int = 9000) -> str:
    if not research_dir.exists():
        return ""
    parts: list[str] = []
    for pattern in ("summary_*.md", "result_*.json", "proof.md"):
        for path in sorted(research_dir.glob(pattern), key=lambda item: item.stat().st_mtime, reverse=True)[:2]:
            try:
                text = path.read_text(encoding="utf-8")
            except Exception:
                continue
            parts.append(f"\n--- PRIOR {path.name} ---\n{text[:3500]}")
    if not parts:
        return ""
    return "\n".join(parts)[:max_chars]


def build_future_research_prompt(item: dict[str, Any], research_dir: Path) -> str:
    source_repo = str(item.get("source_repo") or item.get("target_repo") or "")
    route = str(item.get("research_route", "hybrid"))
    scope_context = build_scope_context(source_repo)
    prior_context = prior_future_research_context(research_dir)
    related_future_context = latest_repo_future_context(source_repo)
    backflow = {}
    state = load_state(source_repo)
    if state:
        backflow = backflow_placement_from_history(state) or {}

    return textwrap.dedent(
        f"""\
        You are running a context-aware Codex future-research task from the
        community outreach queue. This is not a public reply. Produce research
        artifacts under the ignored runtime directory shown below. Do not edit
        Lean files, do not run Lean, and do not write public outreach text.

        {NO_LEAN_EXECUTION_POLICY}
        {agent_context_header("context_aware", scope_context)}

        FUTURE ITEM:
        {json.dumps(item, indent=2, ensure_ascii=False)}

        PAPER BACKFLOW CONTEXT:
        {json.dumps(backflow, indent=2, ensure_ascii=False)}

        WORK DIRECTORY FOR ANY NEW RUNTIME ARTIFACTS:
        {_repo_relative(research_dir)}

        PRIOR RUN CONTEXT FOR THIS FUTURE ITEM:
        {prior_context or "(none)"}

        RECENT RELATED FUTURE CONTEXT FOR THIS REPO:
        {related_future_context or "(none)"}

        REQUIRED ROUTE:
        - research_route: {route}
        - route_reason: {item.get("route_reason", "")}
        - route_contract: {item.get("route_contract", "")}

        EXECUTION RULES:
        - Begin by declaring whether you accept the required route or are
          overriding it. Route override is allowed only with a concrete reason.
        - If route is computation, produce reproducible Python/certificate
          artifacts and do not claim theorem-level closure without proof.
        - If route is proof, produce theorem/proposition statements with complete
          proof text. Computation may guide but cannot replace the proof.
        - If route is hybrid, produce both reproducible artifacts and the proof
          explaining why the artifact gives a lift, obstruction, or certificate.
        - Save reusable scripts/data into `{_repo_relative(research_dir)}`.
        - If the task is not resolved, state the precise mathematical blocker.
        - Do not mention local hidden state as public evidence. Paper paths and
          committed scripts may be cited as evidence.

        Return JSON only:
        {{
          "future_item_id": "{item.get('id')}",
          "research_route": "computation|proof|hybrid",
          "route_override": false,
          "route_reason": "why this route is correct",
          "route_contract_satisfied": true,
          "status": "resolved|partial|blocked",
          "title": "short result title",
          "summary": "technical summary",
          "results": [
            {{
              "type": "theorem|proposition|certificate|obstruction|counterexample|computation",
              "statement": "precise statement",
              "proof_or_verification": "complete proof or reproducibility explanation",
              "artifact": "path to script/json/tex if any, else null"
            }}
          ],
          "artifacts": ["relative paths created or used"],
          "backflow_candidate": true,
          "next_review": "claude_context_aware|zero_init_review|not_ready",
          "notes": "risks, blockers, or required review"
        }}
        """
    )


def write_future_research_summary(research_dir: Path, result: dict[str, Any], raw_output: str, prompt: str) -> tuple[Path, Path]:
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    research_dir.mkdir(parents=True, exist_ok=True)
    prompt_path = research_dir / f"prompt_{stamp}.txt"
    raw_path = research_dir / f"raw_{stamp}.txt"
    json_path = research_dir / f"result_{stamp}.json"
    md_path = research_dir / f"summary_{stamp}.md"
    prompt_path.write_text(prompt, encoding="utf-8")
    raw_path.write_text(raw_output, encoding="utf-8")
    json_path.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")

    lines = [
        f"# {result.get('title', 'Future research result')}",
        "",
        f"- status: {result.get('status', 'unknown')}",
        f"- route: {result.get('research_route', 'unknown')}",
        f"- route_contract_satisfied: {result.get('route_contract_satisfied', False)}",
        f"- next_review: {result.get('next_review', 'not_ready')}",
        "",
        "## Summary",
        str(result.get("summary", "")),
        "",
        "## Results",
    ]
    for entry in result.get("results", []) if isinstance(result.get("results"), list) else []:
        lines.extend(
            [
                "",
                f"### {entry.get('type', 'result')}",
                str(entry.get("statement", "")),
                "",
                str(entry.get("proof_or_verification", "")),
                "",
                f"Artifact: {entry.get('artifact')}",
            ]
        )
    if result.get("notes"):
        lines.extend(["", "## Notes", str(result.get("notes", ""))])
    md_path.write_text("\n".join(lines).strip() + "\n", encoding="utf-8")
    return json_path, md_path


def latest_file(research_dir: Path, pattern: str) -> Optional[Path]:
    matches = sorted(research_dir.glob(pattern), key=lambda item: item.stat().st_mtime, reverse=True)
    return matches[0] if matches else None


def prepare_future_review_packet(item_id: str, *, dry_run: bool = False) -> Path:
    item = find_future_item(item_id)
    research_dir = future_research_dir(item)
    latest_summary = latest_file(research_dir, "summary_*.md")
    latest_result = latest_file(research_dir, "result_*.json")
    if not latest_summary or not latest_result:
        raise RuntimeError(f"Future item {item_id} has no result/summary to review")

    try:
        result_data = json.loads(latest_result.read_text(encoding="utf-8"))
    except Exception:
        result_data = {}

    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    packet_path = research_dir / f"claude_review_packet_{stamp}.md"
    proof_files = sorted(path for path in research_dir.glob("proof*.md"))
    script_files = sorted(path for path in research_dir.glob("*.py"))
    json_files = sorted(path for path in research_dir.glob("*.json"))

    body = "\n".join(
        [
            f"# Claude Review Packet: {item.get('title')}",
            "",
            "## Queue Metadata",
            f"- future_item_id: {item.get('id')}",
            f"- source_repo: {item.get('source_repo')}",
            f"- queue_status_before_review: {item.get('status', 'queued')}",
            f"- research_route: {result_data.get('research_route', item.get('research_route'))}",
            f"- route_contract_satisfied: {result_data.get('route_contract_satisfied')}",
            f"- result_status: {result_data.get('status')}",
            f"- backflow_candidate: {result_data.get('backflow_candidate')}",
            f"- next_review: {result_data.get('next_review')}",
            "",
            "## Scope Boundary",
            str(item.get("scope_boundary", "")),
            "",
            "## Review Questions",
            "- Is the stated result mathematically correct under the recorded scope boundary?",
            "- Is the route contract actually satisfied?",
            "- Should this be backflowed into the main paper now, held as a partial reduction, or sent back for more Codex work?",
            "- Are there any claims that overstate the relation to the original signed companions, Lean formalization, or SFT/Bowen-Franks classification?",
            "",
            "## Latest Summary",
            latest_summary.read_text(encoding="utf-8")[:8000],
            "",
            "## Artifacts",
            *[f"- `{_repo_relative(path)}`" for path in [latest_result, latest_summary, *proof_files, *script_files, *json_files]],
            "",
        ]
    )
    if dry_run:
        print(body)
        return packet_path
    packet_path.write_text(body, encoding="utf-8")
    append_future_queue_note(
        str(item.get("id")),
        f"Prepared Claude review packet: {_repo_relative(packet_path)}",
        source_repo=str(item.get("source_repo", "")),
        status="awaiting_claude_review",
        dry_run=False,
    )
    return packet_path


def build_future_claude_review_prompt(item: dict[str, Any], packet_path: Path) -> str:
    packet = packet_path.read_text(encoding="utf-8")
    return textwrap.dedent(
        f"""\
        You are the final Claude review gate for a community-outreach future
        research artifact. This is a review task, not a generation task.

        {NO_LEAN_EXECUTION_POLICY}
        {AGENT_CONTEXT_POLICY}
        {RESEARCH_ROUTE_POLICY}

        Review the packet below. Be strict about scope:
        - Do not approve an all-q theorem if the packet only proves a reduction.
        - Do not reject a useful partial reduction merely because it is not a full theorem;
          instead use verdict "approve_partial" when it is correct and worth preserving.
        - Do not approve any claim that says local Lean was run or that a signed
          proxy is a canonical nonnegative collision kernel unless the packet proves it.
        - For SFT/Bowen-Franks claims, check whether the stated invariant is scoped
          as a nonnegative lift/class representative rather than equality with the
          original signed companion.

        FUTURE ITEM:
        {json.dumps(item, indent=2, ensure_ascii=False)}

        REVIEW PACKET:
        {packet[:18000]}

        Return JSON only:
        {{
          "approved": true,
          "overall_score": 1,
          "verdict": "approve_backflow|approve_partial|needs_revision|reject",
          "status": "claude_approved_backflow|claude_approved_partial|needs_codex_revision|rejected",
          "summary": "technical review summary",
          "findings": [
            {{"severity": "blocker|major|minor|note", "issue": "specific issue", "recommendation": "specific fix"}}
          ],
          "required_fixes": ["..."],
          "backflow_recommendation": "backflow_now|hold_partial|continue_codex|do_not_use",
          "scope_assessment": "whether the result stays inside the recorded scope boundary",
          "route_contract_assessment": "whether computation/proof/hybrid contract is actually satisfied"
        }}
        """
    )


def write_future_claude_review(
    research_dir: Path,
    item: dict[str, Any],
    review: dict[str, Any],
    raw_output: str,
    prompt: str,
) -> tuple[Path, Path]:
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    review_path = research_dir / f"claude_review_{stamp}.json"
    raw_path = research_dir / f"claude_review_raw_{stamp}.txt"
    prompt_path = research_dir / f"claude_review_prompt_{stamp}.txt"
    md_path = research_dir / f"claude_review_{stamp}.md"
    review_path.write_text(json.dumps(review, indent=2, ensure_ascii=False), encoding="utf-8")
    raw_path.write_text(raw_output, encoding="utf-8")
    prompt_path.write_text(prompt, encoding="utf-8")

    lines = [
        f"# Claude Review: {item.get('title')}",
        "",
        f"- future_item_id: {item.get('id')}",
        f"- approved: {review.get('approved')}",
        f"- score: {review.get('overall_score')}",
        f"- verdict: {review.get('verdict')}",
        f"- status: {review.get('status')}",
        f"- backflow_recommendation: {review.get('backflow_recommendation')}",
        "",
        "## Summary",
        str(review.get("summary", "")),
        "",
        "## Scope",
        str(review.get("scope_assessment", "")),
        "",
        "## Route Contract",
        str(review.get("route_contract_assessment", "")),
        "",
        "## Findings",
    ]
    for finding in review.get("findings", []) if isinstance(review.get("findings"), list) else []:
        lines.append(
            f"- {finding.get('severity', 'note')}: {finding.get('issue', '')} "
            f"Recommendation: {finding.get('recommendation', '')}"
        )
    if review.get("required_fixes"):
        lines.extend(["", "## Required Fixes"])
        for fix in review.get("required_fixes", []):
            lines.append(f"- {fix}")
    md_path.write_text("\n".join(lines).strip() + "\n", encoding="utf-8")
    return review_path, md_path


def review_future_item(item_id: str, *, dry_run: bool = False) -> dict[str, Any]:
    item = find_future_item(item_id)
    research_dir = future_research_dir(item)
    packet = latest_file(research_dir, "claude_review_packet_*.md")
    if not packet:
        packet = prepare_future_review_packet(item_id, dry_run=dry_run)
    prompt = build_future_claude_review_prompt(item, packet)
    if dry_run:
        print(prompt)
        return {
            "approved": False,
            "overall_score": 0,
            "verdict": "dry_run",
            "status": "dry_run",
        }

    raw_output = claude_exec(prompt, work_dir=REPO_ROOT, timeout=1200, dry_run=False)
    parsed = parse_json_from_output(raw_output)
    raw_lower = raw_output.lower()
    if "hit your limit" in raw_lower or "usage limit" in raw_lower or "rate limit" in raw_lower:
        parsed = {
            "approved": False,
            "overall_score": 0,
            "verdict": "claude_quota_blocked",
            "status": "awaiting_claude_review",
            "summary": "Claude review could not run because the Claude CLI reported a usage/quota limit.",
            "findings": [
                {
                    "severity": "note",
                    "issue": "Claude quota/usage limit blocked final review.",
                    "recommendation": "Retry --review-future after the Claude quota resets.",
                }
            ],
            "required_fixes": [],
            "backflow_recommendation": "pending_claude",
            "scope_assessment": "Not reviewed; pending Claude.",
            "route_contract_assessment": "Not reviewed; pending Claude.",
            "raw_excerpt": raw_output[:2000],
        }
    if not isinstance(parsed, dict) or not parsed:
        parsed = {
            "approved": False,
            "overall_score": 0,
            "verdict": "needs_revision",
            "status": "needs_codex_revision",
            "summary": "Claude returned no parseable JSON.",
            "findings": [
                {
                    "severity": "blocker",
                    "issue": "No parseable JSON review was returned.",
                    "recommendation": "Rerun review with a stricter prompt or inspect raw output.",
                }
            ],
            "required_fixes": ["Obtain parseable Claude review JSON."],
            "backflow_recommendation": "continue_codex",
            "scope_assessment": "",
            "route_contract_assessment": "",
            "raw_excerpt": raw_output[:2000],
        }

    review_path, md_path = write_future_claude_review(research_dir, item, parsed, raw_output, prompt)
    status = str(parsed.get("status") or "needs_codex_revision")
    allowed_statuses = {
        "awaiting_claude_review",
        "claude_approved_backflow",
        "claude_approved_partial",
        "needs_codex_revision",
        "rejected",
    }
    if status not in allowed_statuses:
        verdict = str(parsed.get("verdict", ""))
        approved = parsed.get("approved") is True
        if approved and verdict == "approve_backflow":
            status = "claude_approved_backflow"
        elif approved and verdict == "approve_partial":
            status = "claude_approved_partial"
        elif verdict == "reject":
            status = "rejected"
        else:
            status = "needs_codex_revision"
    append_future_queue_note(
        str(item.get("id")),
        (
            f"Claude review status={status} score={parsed.get('overall_score')} "
            f"verdict={parsed.get('verdict')} review={_repo_relative(md_path)} json={_repo_relative(review_path)}"
        ),
        source_repo=str(item.get("source_repo", "")),
        status=status,
        dry_run=False,
    )
    return parsed


def find_state_record(repo: str, *, include_archive: bool = True) -> tuple[RepoState, Path, bool]:
    """Load an active state, or the latest archived state for a repo."""
    active = state_file(repo)
    if active.exists():
        state = load_state(repo)
        if state:
            return state, active, False

    if not include_archive:
        raise RuntimeError(f"No state found for {repo}")

    candidates: list[tuple[str, Path, dict[str, Any]]] = []
    for path in sorted((STATE_DIR / "archive").glob("*/*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        if data.get("repo") != repo:
            continue
        candidates.append((_state_updated_at(path, data), path, data))

    if not candidates:
        raise RuntimeError(f"No active or archived state found for {repo}")

    _, path, data = max(candidates, key=lambda item: item[0])
    return RepoState.from_dict(data), path, True


def state_review_dir(state: RepoState) -> Path:
    return target_dir_for_repo(state.repo) / "review"


def _artifact_listing(root: Path, *, max_items: int = 80) -> list[str]:
    if not root.exists():
        return []
    rows: list[str] = []
    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        rel = _repo_relative(path)
        try:
            size = path.stat().st_size
        except OSError:
            size = 0
        rows.append(f"- `{rel}` ({size} bytes)")
        if len(rows) >= max_items:
            rows.append("- ...")
            break
    return rows


def prepare_state_review_packet(repo: str, *, dry_run: bool = False) -> Path:
    """Prepare a final Claude review packet for ordinary repo states.

    This covers Stage D drafts and lower-level discovery/backflow artifacts that
    are not future-queue items. Runtime packets stay under ignored targets/.
    """
    state, source_path, was_archived = find_state_record(repo, include_archive=True)
    review_dir = state_review_dir(state)
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    packet_path = review_dir / f"claude_state_review_packet_{stamp}.md"

    backflow = backflow_placement_from_history(state) or {}
    tex_text = ""
    tex_path_raw = str(backflow.get("tex_path", "") or "")
    if tex_path_raw:
        tex_path = Path(tex_path_raw)
        if not tex_path.is_absolute():
            tex_path = REPO_ROOT / tex_path_raw
        if tex_path.exists():
            tex_text = tex_path.read_text(encoding="utf-8", errors="replace")[:12000]

    research_doc = ""
    research_path = target_dir_for_repo(state.repo) / "research.md"
    if research_path.exists():
        research_doc = research_path.read_text(encoding="utf-8", errors="replace")[:12000]

    body = "\n".join(
        [
            f"# Claude State Review Packet: {state.repo}",
            "",
            "## State Metadata",
            f"- state_source: `{_repo_relative(source_path)}`",
            f"- restored_from_archive: {was_archived}",
            f"- stage_before_review: {state.stage}",
            f"- round: {state.round}",
            f"- scores: `{json.dumps(state.scores, ensure_ascii=False)}`",
            f"- outreach_kind: {state.outreach_kind or '(unspecified)'}",
            f"- draft_title: {state.draft_title or '(none)'}",
            f"- submission_url: {state.submission_url or '(none)'}",
            f"- backflow: `{json.dumps(backflow, ensure_ascii=False)}`",
            "",
            "## Review Mode",
            "This is a final gate packet for an ordinary outreach state, not a future-queue continuation.",
            "If a public draft is present, review it as the public reply/issue candidate.",
            "If no public draft is present, review whether the backflow/research artifact is correct enough to preserve, draft later, or mark reference-only.",
            "",
            "## Review Questions",
            "- Are the mathematical claims correct and scoped honestly?",
            "- Are the committed paper-side artifacts sufficient evidence for the stated claims?",
            "- Should the item be posted/drafted, held for more Codex work, or kept only as a reference/negative audit?",
            "- Does the packet avoid local Lean execution claims and scratch-path public citations?",
            "",
            "## Draft",
            state.draft_body[:12000] if state.draft_body else "(no public draft in state)",
            "",
            "## Findings",
            json.dumps(state.findings[:8], indent=2, ensure_ascii=False)[:12000],
            "",
            "## Latest Events",
            json.dumps(state.action_history[-10:], indent=2, ensure_ascii=False)[:12000],
            "",
            "## Research Document Excerpt",
            research_doc or "(none)",
            "",
            "## Paper Backflow Excerpt",
            tex_text or "(none)",
            "",
            "## Target Artifacts",
            *(_artifact_listing(target_dir_for_repo(state.repo)) or ["(none)"]),
            "",
        ]
    )

    if dry_run:
        print(body)
        return packet_path

    review_dir.mkdir(parents=True, exist_ok=True)
    packet_path.write_text(body, encoding="utf-8")
    state.stage = "AWAITING_CLAUDE_REVIEW"
    state.error = ""
    state.log_event(
        "R",
        "prepared Claude final state review packet",
        verdict="awaiting_claude_review",
        detail=_repo_relative(packet_path),
    )
    save_state(state)
    logger.info("[%s] State review packet: %s", state.repo, _repo_relative(packet_path))
    return packet_path


def build_state_claude_review_prompt(state: RepoState, packet_path: Path) -> str:
    packet = packet_path.read_text(encoding="utf-8")
    return textwrap.dedent(
        f"""\
        You are the final Claude review gate for an ordinary community-outreach
        state. This is a review task, not a generation task.

        {NO_LEAN_EXECUTION_POLICY}
        {AGENT_CONTEXT_POLICY}
        {RESEARCH_ROUTE_POLICY}

        Review the packet below. Be strict about scope, public tone, and
        evidence boundaries. Do not approve claims that require local Lean
        execution unless the packet cites pre-existing committed Lean evidence.

        TARGET STATE:
        - repo: {state.repo}
        - stage: {state.stage}
        - has_public_draft: {bool(state.draft_title and state.draft_body)}

        REVIEW PACKET:
        {packet[:22000]}

        Return JSON only:
        {{
          "approved": true,
          "overall_score": 1,
          "verdict": "approve_public_draft|approve_artifact|approve_partial|needs_revision|reference_only|reject",
          "status": "claude_approved_public_draft|claude_approved_artifact|claude_approved_partial|needs_codex_revision|reference_only|rejected",
          "summary": "technical review summary",
          "findings": [
            {{"severity": "blocker|major|minor|note", "issue": "specific issue", "recommendation": "specific fix"}}
          ],
          "required_fixes": ["..."],
          "posting_recommendation": "post_now|draft_after_review|hold_partial|reference_only|do_not_use",
          "scope_assessment": "whether the item stays inside its verified scope",
          "evidence_assessment": "whether committed paper-side evidence supports the claims"
        }}
        """
    )


def write_state_claude_review(
    state: RepoState,
    review: dict[str, Any],
    raw_output: str,
    prompt: str,
) -> tuple[Path, Path]:
    review_dir = state_review_dir(state)
    review_dir.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    json_path = review_dir / f"claude_state_review_{stamp}.json"
    md_path = review_dir / f"claude_state_review_{stamp}.md"
    raw_path = review_dir / f"claude_state_review_raw_{stamp}.txt"
    prompt_path = review_dir / f"claude_state_review_prompt_{stamp}.txt"
    json_path.write_text(json.dumps(review, indent=2, ensure_ascii=False), encoding="utf-8")
    raw_path.write_text(raw_output, encoding="utf-8")
    prompt_path.write_text(prompt, encoding="utf-8")

    lines = [
        f"# Claude State Review: {state.repo}",
        "",
        f"- approved: {review.get('approved')}",
        f"- score: {review.get('overall_score')}",
        f"- verdict: {review.get('verdict')}",
        f"- status: {review.get('status')}",
        f"- posting_recommendation: {review.get('posting_recommendation')}",
        "",
        "## Summary",
        str(review.get("summary", "")),
        "",
        "## Scope",
        str(review.get("scope_assessment", "")),
        "",
        "## Evidence",
        str(review.get("evidence_assessment", "")),
        "",
        "## Findings",
    ]
    for finding in review.get("findings", []) if isinstance(review.get("findings"), list) else []:
        lines.append(
            f"- {finding.get('severity', 'note')}: {finding.get('issue', '')} "
            f"Recommendation: {finding.get('recommendation', '')}"
        )
    if review.get("required_fixes"):
        lines.extend(["", "## Required Fixes"])
        for fix in review.get("required_fixes", []):
            lines.append(f"- {fix}")
    md_path.write_text("\n".join(lines).strip() + "\n", encoding="utf-8")
    return json_path, md_path


def review_state_item(repo: str, *, dry_run: bool = False) -> dict[str, Any]:
    state, _, _ = find_state_record(repo, include_archive=True)
    review_dir = state_review_dir(state)
    packet = latest_file(review_dir, "claude_state_review_packet_*.md")
    if not packet:
        packet = prepare_state_review_packet(repo, dry_run=dry_run)
    prompt = build_state_claude_review_prompt(state, packet)
    if dry_run:
        print(prompt)
        return {
            "approved": False,
            "overall_score": 0,
            "verdict": "dry_run",
            "status": "dry_run",
        }

    raw_output = claude_exec(prompt, work_dir=REPO_ROOT, timeout=1200, dry_run=False)
    parsed = parse_json_from_output(raw_output)
    raw_lower = raw_output.lower()
    if "hit your limit" in raw_lower or "usage limit" in raw_lower or "rate limit" in raw_lower:
        parsed = {
            "approved": False,
            "overall_score": 0,
            "verdict": "claude_quota_blocked",
            "status": "awaiting_claude_review",
            "summary": "Claude review could not run because the Claude CLI reported a usage/quota limit.",
            "findings": [
                {
                    "severity": "note",
                    "issue": "Claude quota/usage limit blocked final state review.",
                    "recommendation": "Retry --review-state after the Claude quota resets.",
                }
            ],
            "required_fixes": [],
            "posting_recommendation": "pending_claude",
            "scope_assessment": "Not reviewed; pending Claude.",
            "evidence_assessment": "Not reviewed; pending Claude.",
            "raw_excerpt": raw_output[:2000],
        }
    if not isinstance(parsed, dict) or not parsed:
        parsed = {
            "approved": False,
            "overall_score": 0,
            "verdict": "needs_revision",
            "status": "needs_codex_revision",
            "summary": "Claude returned no parseable JSON.",
            "findings": [
                {
                    "severity": "blocker",
                    "issue": "No parseable JSON review was returned.",
                    "recommendation": "Rerun review with a stricter prompt or inspect raw output.",
                }
            ],
            "required_fixes": ["Obtain parseable Claude review JSON."],
            "posting_recommendation": "hold_partial",
            "scope_assessment": "",
            "evidence_assessment": "",
            "raw_excerpt": raw_output[:2000],
        }

    review_path, md_path = write_state_claude_review(state, parsed, raw_output, prompt)
    status = str(parsed.get("status") or "needs_codex_revision")
    allowed_statuses = {
        "awaiting_claude_review",
        "claude_approved_public_draft",
        "claude_approved_artifact",
        "claude_approved_partial",
        "needs_codex_revision",
        "reference_only",
        "rejected",
    }
    if status not in allowed_statuses:
        verdict = str(parsed.get("verdict", ""))
        approved = parsed.get("approved") is True
        if approved and verdict == "approve_public_draft":
            status = "claude_approved_public_draft"
        elif approved and verdict == "approve_artifact":
            status = "claude_approved_artifact"
        elif approved and verdict == "approve_partial":
            status = "claude_approved_partial"
        elif verdict == "reference_only":
            status = "reference_only"
        elif verdict == "reject":
            status = "rejected"
        else:
            status = "needs_codex_revision"

    if status == "claude_approved_public_draft" and state.draft_title and state.draft_body:
        state.stage = "D"
    elif status == "reference_only":
        state.stage = "SKIPPED"
    elif status == "rejected":
        state.stage = "SKIPPED"
    elif status == "needs_codex_revision":
        state.stage = "C" if state.draft_title and state.draft_body else "B"
    else:
        state.stage = "AWAITING_CLAUDE_REVIEW"
    state.error = "" if status != "needs_codex_revision" else str(parsed.get("summary", ""))[:1000]
    state.log_event(
        "R",
        "Claude final state review",
        score=coerce_score(parsed.get("overall_score"), 0),
        verdict=status,
        detail=(
            f"verdict={parsed.get('verdict')} review={_repo_relative(md_path)} "
            f"json={_repo_relative(review_path)}"
        ),
    )
    save_state(state)
    return parsed


def set_state_status(repo: str, status: str, note: str, *, dry_run: bool = False) -> RepoState:
    state, _, _ = find_state_record(repo, include_archive=True)
    state.stage = status
    state.error = "" if status not in {"ERROR", "needs_codex_revision"} else note[:1000]
    if status in {"DONE", "SKIPPED", "REFERENCE_ONLY"}:
        state.timestamps.setdefault("completed_at", iso_now())
    state.log_event("R", "manual state status update", verdict=status, detail=note)
    if not dry_run:
        save_state(state)
    logger.info("[%s] State status set to %s", repo, status)
    return state


def latest_repo_future_context(repo: str, *, max_chars: int = 3500) -> str:
    future_root = target_dir_for_repo(repo) / "future"
    if not future_root.exists():
        return ""
    parts: list[str] = []
    patterns = (
        "summary_*.md",
        "proof_closure_packet_*.md",
        "theorem_packet.md",
        "*certificate*.json",
    )
    for pattern in patterns:
        matches = sorted(
            future_root.glob(f"*/{pattern}"),
            key=lambda path: path.stat().st_mtime,
            reverse=True,
        )
        for path in matches[:2]:
            try:
                text = path.read_text(encoding="utf-8")
            except Exception:
                continue
            parts.append(f"\n--- {_repo_relative(path)} ---\n{text[:1200]}")
    return "\n".join(parts)[:max_chars]


def queue_state_deepening(repo: str, *, kind: str = "default", dry_run: bool = False) -> dict[str, Any]:
    """Convert a reference-only state into a future deep-research task."""
    state, _, _ = find_state_record(repo, include_archive=True)
    backflow = backflow_placement_from_history(state) or {}
    section_dir = str(backflow.get("section_dir", ""))
    kind = (kind or "default").strip().lower()

    if state.repo == "teorth/equational_theories" and section_dir == "stable_arithmetic_equational_audit":
        if kind == "integral-primary":
            title = "Integral and 2/3-primary closure of the affine dashboard obstruction"
            task = (
                "Continue from the exact stable-affine dashboard obstruction boundary. "
                "Attack the remaining all-affine gap: decide whether the coefficient-ideal "
                "containment I(F) subset I(E) can be strengthened from Z[1/6][a,b] to "
                "Z[a,b] for the current 498 dashboard pairs. If integral containment fails, "
                "classify the obstruction over the 2-primary and 3-primary fibers and state "
                "the sharp replacement theorem. The output must be a theorem packet with "
                "complete proof or a precise blocker certificate; do not claim a universal "
                "small-characteristic affine obstruction unless proved."
            )
            scope_boundary = (
                "Previous work proved affine-linear obstruction only over rings where 6 is "
                "invertible and by finite certificate for the audited Fibonacci residues. "
                "This task may strengthen that boundary, or prove why the integral/primary "
                "closure is blocked. It must not treat the Z[1/6] theorem as an integral theorem."
            )
            route = "proof"
            route_reason = (
                "The remaining gap is an ideal-containment/primary-decomposition theorem, "
                "not a broad enumeration."
            )
            route_contract = (
                "Produce one of: (1) an integral containment theorem over Z[a,b] with proof; "
                "(2) a 2/3-primary decomposition theorem with proof; or (3) a minimal "
                "counterexample/blocker certificate explaining exactly where integral "
                "containment fails."
            )
            priority = "high"
        elif kind == "non-affine":
            title = "First non-affine mechanism beyond the stable-affine obstruction"
            task = (
                "Use the stable-affine obstruction as a boundary theorem and search for the "
                "first genuinely non-affine/path-order/nonlinear mechanism that could separate "
                "a current ETP dashboard pair. The goal is not a broad scan; follow the "
                "bad-example route: identify the smallest dashboard pair not explainable by "
                "the affine shadows, propose a non-affine skeleton, and either construct a "
                "certificate or prove a sharper obstruction for that skeleton."
            )
            scope_boundary = (
                "StableAdd, stableMul, affine-linear rings with 6 invertible, and audited "
                "Fibonacci affine residues are already excluded. This task must leave those "
                "shadows and must not repackage affine-linear data as a new mechanism."
            )
            route = "hybrid"
            route_reason = (
                "A first non-affine mechanism likely needs finite certificate search plus "
                "a proof interpreting the found skeleton or obstruction."
            )
            route_contract = (
                "Produce a concrete non-affine candidate certificate with proof of what it "
                "separates, or a precise theorem excluding the attempted skeleton. Include "
                "reproducible scripts/certificates if a finite search is used."
            )
            priority = "high"
        else:
            title = "Deep structural theorem from stable arithmetic dashboard-disjointness"
            task = (
                "Continue from the stable_arithmetic_equational_audit negative result. "
                "Do not stop at '0 dashboard unknowns'. Use the bad-example-structure route: "
                "explain structurally why stableAdd/stableMul and the Fibonacci affine-linear "
                "family are dashboard-disjoint, classify the obstruction if possible, and "
                "look for a genuinely new theorem chain that either proves an impossibility "
                "for the affine-linear/stable-arithmetic mechanism or identifies the next "
                "non-affine mechanism needed to hit current ETP unknowns. The output must be "
                "publishable mathematical text or a precise blocker theorem, not another "
                "value-summary."
            )
            scope_boundary = (
                "The existing public-outreach value is insufficient because the computed "
                "stable arithmetic and Fibonacci affine-linear spectra resolve 0 of 498 "
                "current ETP dashboard unknowns. This future task should deepen the negative "
                "audit into structural theory; it must not claim a dashboard resolution unless "
                "a new verified mechanism is found."
            )
            route = "proof"
            route_reason = (
                "The finite computations are already available; the missing value is a "
                "structural theorem/classification or obstruction explaining the negative audit."
            )
            route_contract = (
                "Produce theorem/proposition statements with complete proof text. Existing "
                "Python certificates may be cited as finite evidence, but a new outreach-worthy "
                "result must be a structural proof, classification, or impossibility theorem."
            )
            priority = "high"
    else:
        title = f"Deepen reference-only outreach result for {state.repo}"
        task = (
            "Continue from the reference-only or skipped outreach result and attempt to "
            "turn it into a structural theorem, classification, obstruction, or precise "
            "negative result. Do not merely restate why the previous public-outreach value "
            "was low."
        )
        scope_boundary = (
            "The current state is not ready for public outreach. Deepening may produce "
            "a future contribution, but existing low-value claims must remain scoped as "
            "reference-only until a stronger result is proved."
        )
        route = "proof"
        route_reason = "The next step is theorem-level strengthening, not another draft."
        route_contract = "Produce complete proof text or a precise mathematical blocker."
        priority = "medium"

    source = {
        "repo": state.repo,
        "base_repo": repo_base(state.repo),
        "issue": repo_issue(state.repo),
        "stage": state.stage,
        "draft_title": state.draft_title,
        "state_file": _repo_relative(state_file(state.repo)),
        "backflow": backflow,
        "recorded_at": iso_now(),
    }
    evidence = {
        "scores": state.scores,
        "backflow": backflow,
        "latest_events": state.action_history[-5:],
        "findings": state.findings[:4],
        "prior_future_context": latest_repo_future_context(state.repo),
    }
    item = {
        "title": title,
        "task": task,
        "current_scope": (
            "This is a continuation of an internal reference-only result. It is not a "
            "public reply and should not create target-facing text before review."
        ),
        "scope_boundary": scope_boundary,
        "evidence": json.dumps(evidence, ensure_ascii=False)[:2500],
        "priority": priority,
        "recommended_agent_context": "context_aware_research",
        "research_route": route,
        "route_reason": route_reason,
        "route_contract": route_contract,
        "review_policy": (
            "Use context-aware Codex for deepening because the negative audit, paper "
            "backflow, and ETP dashboard scope matter. Use zero_init_review only after "
            "a standalone theorem packet exists."
        ),
        "source": source,
    }
    item_id = str(
        item.get("id")
        or _future_item_id(
            {
                **item,
                "source_repo": source.get("repo", ""),
                "target_repo": repo_base(source.get("repo", "")),
            }
        )
    )
    added = append_future_queue_item(item, dry_run=dry_run)
    if not dry_run:
        state.stage = "DEEPENING_QUEUED"
        state.error = ""
        state.log_event(
            "R",
            "queued deepening future task",
            verdict="deepening_queued",
            detail=f"{item_id}: {title}",
        )
        save_state(state)
    logger.info("[%s] Deepening future task %s: %s", state.repo, "queued" if added else "already exists", title)
    return {"queued": added, "id": item_id, "title": title}


def refresh_state_draft(repo: str, *, dry_run: bool = False) -> RepoState:
    """Refresh a public draft from deterministic backflow-aware templates."""
    state, _, _ = find_state_record(repo, include_archive=True)
    backflow = backflow_placement_from_history(state) or {}
    title, body = fallback_draft(
        state.repo,
        normalize_findings(state.findings),
        [],
        backflow_placement=backflow,
    )
    state.draft_title = title
    state.draft_body = body
    state.outreach_kind = infer_outreach_kind(state.repo, backflow)
    contract = validate_draft_contract(
        state,
        backflow_placement=backflow,
        dry_run=dry_run,
        fallback_used=False,
    )
    state.stage = "D" if contract["approved"] else "C"
    state.round = 0
    state.error = "" if contract["approved"] else "; ".join(contract["errors"])[:1000]
    state.log_event(
        "C",
        "draft refreshed from deterministic backflow template",
        score=max(state.scores.get("final", []) or [0]),
        verdict=f"{state.outreach_kind}_ready" if contract["approved"] else "draft_contract_failed",
        detail=json.dumps(
            {
                "title": title,
                "body_len": len(body),
                "backflow": backflow,
                "outreach_kind": state.outreach_kind,
                "contract": contract,
            },
            ensure_ascii=False,
        ),
    )
    if dry_run:
        print(stage_d_prompt(state))
        return state
    save_state(state)
    logger.info("[%s] Draft refreshed from deterministic template", repo)
    return state


def process_future_item(item_id: str, *, model: Optional[str], dry_run: bool) -> dict[str, Any]:
    item = find_future_item(item_id)
    research_dir = future_research_dir(item)
    prompt = build_future_research_prompt(item, research_dir)
    if dry_run:
        print(prompt)
        return {
            "future_item_id": item.get("id"),
            "research_route": item.get("research_route", "hybrid"),
            "status": "dry-run",
            "route_contract_satisfied": False,
        }

    raw_output = codex_exec(prompt, work_dir=REPO_ROOT, timeout=2400, model=model, dry_run=dry_run)
    parsed = parse_json_from_output(raw_output)
    if not isinstance(parsed, dict):
        parsed = {
            "future_item_id": item.get("id"),
            "research_route": item.get("research_route", "hybrid"),
            "route_override": False,
            "route_reason": item.get("route_reason", ""),
            "route_contract_satisfied": False,
            "status": "blocked",
            "title": item.get("title", "Future research task"),
            "summary": "Codex returned no parseable JSON.",
            "results": [],
            "artifacts": [],
            "backflow_candidate": False,
            "next_review": "not_ready",
            "notes": raw_output[:4000],
        }

    parsed.setdefault("future_item_id", item.get("id"))
    parsed.setdefault("research_route", item.get("research_route", "hybrid"))
    parsed.setdefault("status", "partial")
    json_path, md_path = write_future_research_summary(research_dir, parsed, raw_output, prompt)
    note = (
        f"Codex future research run status={parsed.get('status')} "
        f"route={parsed.get('research_route')} "
        f"contract={parsed.get('route_contract_satisfied')} "
        f"summary={_repo_relative(md_path)} result={_repo_relative(json_path)}"
    )
    queue_status = str(parsed.get("status", "queued"))
    if (
        queue_status == "resolved"
        and bool(parsed.get("route_contract_satisfied", False))
        and str(parsed.get("next_review", "")).startswith("claude")
    ):
        queue_status = "awaiting_claude_review"
    append_future_queue_note(
        str(item.get("id")),
        note,
        source_repo=str(item.get("source_repo", "")),
        status=queue_status,
        dry_run=False,
    )
    logger.info("Future research result: %s", _repo_relative(md_path))
    return parsed


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
        if rc != 0:
            if stderr:
                logger.warning("Codex stderr: %s", stderr[:400])
            return ""
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

# ---------------------------------------------------------------------------
# Backflow language & terminology policy
# ---------------------------------------------------------------------------
PAPER_LANGUAGE = "zh-CN"
PAPER_LANGUAGE_LABEL = "中文"

BACKFLOW_TERMINOLOGY_FIXES: dict[str, str] = {
    "稳定纤维": "稳定类型",
}

BACKFLOW_LANGUAGE_POLICY = """BACKFLOW LANGUAGE POLICY:
- The main paper is written entirely in Chinese (中文学术散文).
  All backflow .tex content MUST be in Chinese, matching the style of
  existing sections (see sync_kernel, unit_circle_phase_arithmetic,
  normalization appendices for reference).
- Use \\text{且} (NOT \\text{and}) for connectives in display math.
- Use established paper terminology:
    稳定类型集合 (for X_m the set), 稳定类型 (for x ∈ X_m an element),
    稳定值环同构 (for stableValueRingEquiv), 折叠 (for Fold).
  Do NOT use 稳定纤维 — the paper uses 稳定类型.
- Keep technical English terms that have no standard Chinese equivalent:
  magma, Lean, ETP, CRT, Fibonacci, Bowen-Franks, SFT.
- Table headers, captions, and all non-formula prose must be in Chinese.
- No revision notes, no timestamps, no 'new X' or 'updated Y' markers."""


def verify_backflow_language(tex_path: "Path") -> dict[str, Any]:
    """Verify backflow .tex matches paper language and terminology.

    Returns {"passed": bool, "errors": [...], "warnings": [...], "fixes_applied": int}.
    """
    errors: list[str] = []
    warnings: list[str] = []
    fixes_applied = 0

    if not tex_path.exists():
        return {"passed": False, "errors": ["tex file does not exist"], "warnings": [], "fixes_applied": 0}

    content = tex_path.read_text(encoding="utf-8")

    # --- Check 1: Language detection (heuristic) ---
    # Count Chinese chars vs English prose words outside of LaTeX commands
    import re as _re
    stripped = _re.sub(r"\\[a-zA-Z]+(\[[^\]]*\])?(\{[^}]*\})*", "", content)
    stripped = _re.sub(r"\$[^$]*\$", "", stripped)
    stripped = _re.sub(r"\\\[[^\]]*\\\]", "", stripped)
    chinese_chars = len(_re.findall(r"[\u4e00-\u9fff]", stripped))
    english_words = len(_re.findall(r"\b[a-zA-Z]{4,}\b", stripped))
    # If English words dominate, flag as wrong language
    if english_words > 0 and chinese_chars < english_words * 2:
        errors.append(
            f"backflow content appears to be in English ({english_words} English words vs "
            f"{chinese_chars} Chinese chars). Paper requires Chinese (中文)."
        )

    # --- Check 2: Terminology fixes ---
    original = content
    for wrong, correct in BACKFLOW_TERMINOLOGY_FIXES.items():
        if wrong in content:
            count = content.count(wrong)
            content = content.replace(wrong, correct)
            fixes_applied += count
            warnings.append(f"replaced {count}x '{wrong}' → '{correct}'")

    # --- Check 3: \\text{{and}} in math → \\text{{且}} ---
    and_pattern = r"\\text\{and\}"
    and_matches = _re.findall(and_pattern, content)
    if and_matches:
        content = _re.sub(and_pattern, r"\\text{且}", content)
        fixes_applied += len(and_matches)
        warnings.append(f"replaced {len(and_matches)}x \\text{{and}} → \\text{{且}}")

    # --- Check 4: English table headers ---
    eng_header_patterns = [
        (r"\\text\{exact entries\}", r"\\text{精确条目}"),
        (r"\\text\{superset entries\}", r"\\text{超集条目}"),
        (r"\\text\{pair\}", r"\\text{对}"),
        (r"\\text\{satisfied\}", r"\\text{满足}"),
        (r"\\text\{refuted\}", r"\\text{反驳}"),
    ]
    for pat, repl in eng_header_patterns:
        matches = _re.findall(pat, content)
        if matches:
            content = _re.sub(pat, repl, content)
            fixes_applied += len(matches)
            warnings.append(f"replaced {len(matches)}x {pat} → {repl}")

    # Write back if fixes were applied
    if content != original:
        tex_path.write_text(content, encoding="utf-8")
        logger.info("backflow language check: applied %d fixes to %s", fixes_applied, tex_path)

    return {
        "passed": len(errors) == 0,
        "errors": errors,
        "warnings": warnings,
        "fixes_applied": fixes_applied,
    }


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
          "section_title_short": "short title for commit messages"
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

        {BACKFLOW_LANGUAGE_POLICY}

        Write the COMPLETE .tex file to: {tex_dir}/main.tex
        Create the directory first: `mkdir -p {tex_dir}`

        ═══════════════════════════════════════════════════════════════
        ALSO: Decide whether to copy verification scripts into the paper
        ═══════════════════════════════════════════════════════════════

        Check: `ls {MAIN_PAPER_DIR}/scripts/`
        Check: `ls {target_dir}/*.py`

        If the research produced Python scripts that are part of the proof
        (verification, certificate computation, enumeration), they belong
        in the paper's scripts/ directory for reproducibility.

        If they are just exploratory/search scripts, leave them in outreach.

        For each script you decide to include:
        - Copy to: {MAIN_PAPER_DIR}/scripts/<topic_subdir>/<script>.py
        - Update the .tex to reference the paper path

        ═══════════════════════════════════════════════════════════════

        Return JSON:
        {{
          "tex_path": "path to the .tex file written",
          "sections_written": ["list of theorem/lemma names included"],
          "scripts_copied_to_paper": ["list of scripts copied, or empty if none"]
        }}
        """
    )


def backflow_to_main_paper(
    state: "RepoState",
    *,
    model: Optional[str] = None,
    dry_run: bool = False,
    push_final_artifacts: bool = True,
    skip_mid_claude: bool = False,
) -> dict[str, Any]:
    """Two-step backflow: Codex proposes paper placement, Claude reviews, then
    Codex generates paper-quality .tex inside the main paper tree.

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

    # Step 2: optional mid-pipeline placement review.
    if skip_mid_claude:
        logger.info("[%s] Backflow: skipping mid-pipeline Claude placement review", state.repo)
    else:
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

    # Step 3: Codex generates the .tex section inside the main paper tree.
    logger.info("[%s] Backflow: generating main-paper .tex section", state.repo)
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

    # Step 3.5: Verify backflow language & terminology
    section_type = placement.get("placement", "appendix")
    section_dir = placement.get("section_dir", slug)
    tex_dir = MAIN_PAPER_DIR / "sections" / section_type / section_dir
    tex_file = tex_dir / "main.tex"
    if tex_file.exists() and not dry_run:
        lang_check = verify_backflow_language(tex_file)
        if not lang_check["passed"]:
            logger.warning(
                "[%s] Backflow language check FAILED: %s. "
                "Generated content is not in Chinese — requires manual rewrite or re-generation.",
                state.repo, "; ".join(lang_check["errors"]),
            )
            state.log_event("B", "backflow language check failed", detail=json.dumps({
                "errors": lang_check["errors"],
                "warnings": lang_check["warnings"],
            }, ensure_ascii=False))
            save_state(state)
        else:
            if lang_check["fixes_applied"] > 0:
                logger.info(
                    "[%s] Backflow language check: auto-fixed %d terminology issues (%s)",
                    state.repo, lang_check["fixes_applied"],
                    "; ".join(lang_check["warnings"]),
                )
            else:
                logger.info("[%s] Backflow language check passed", state.repo)

    # Step 4: Wire the new section into the paper's main.tex
    insert_after = placement.get("insert_after", "")
    main_tex_path = MAIN_PAPER_DIR / "sections" / section_type / "main.tex"
    subfile_line = f"\\subfile{{{section_dir}/main}}"

    if main_tex_path.exists():
        main_tex = main_tex_path.read_text(encoding="utf-8")
        if subfile_line not in main_tex:
            # Insert after the specified section, or before \end{document}
            if insert_after:
                anchor = f"\\subfile{{{insert_after}/main}}"
                if anchor in main_tex:
                    main_tex = main_tex.replace(
                        anchor,
                        f"{anchor}\n{subfile_line}",
                    )
                    main_tex_path.write_text(main_tex, encoding="utf-8")
                    logger.info("[%s] Backflow: inserted %s after %s in %s/main.tex",
                                state.repo, section_dir, insert_after, section_type)
                else:
                    # Anchor not found, insert before \end{document}
                    main_tex = main_tex.replace(
                        "\\end{document}",
                        f"{subfile_line}\n\\end{{document}}",
                    )
                    main_tex_path.write_text(main_tex, encoding="utf-8")
                    logger.info("[%s] Backflow: appended %s before \\end{document} in %s/main.tex",
                                state.repo, section_dir, section_type)
            else:
                main_tex = main_tex.replace(
                    "\\end{document}",
                    f"{subfile_line}\n\\end{{document}}",
                )
                main_tex_path.write_text(main_tex, encoding="utf-8")
                logger.info("[%s] Backflow: appended %s to %s/main.tex",
                            state.repo, section_dir, section_type)
        else:
            logger.info("[%s] Backflow: %s already in %s/main.tex, skipping",
                        state.repo, section_dir, section_type)

    # Record backflow
    placement["gen_result"] = gen_result
    state.log_event("B", "backflow completed", detail=json.dumps({
        "placement": placement.get("placement"),
        "section_dir": placement.get("section_dir"),
        "tex_path": gen_result.get("tex_path", ""),
        "wired_into_main_tex": str(main_tex_path),
    }, ensure_ascii=False))
    save_state(state)

    logger.info("[%s] Backflow done: %s/%s → tex=%s wired=%s",
                state.repo,
                placement.get("placement"), placement.get("section_dir"),
                gen_result.get("tex_path", "N/A"),
                str(main_tex_path))

    if not dry_run:
        paths_to_add: list[str | Path] = [
            MAIN_PAPER_DIR / "sections" / section_type / section_dir,
            main_tex_path,
        ]
        scripts_copied = gen_result.get("scripts_copied_to_paper", [])
        for raw_script in scripts_copied if isinstance(scripts_copied, list) else []:
            script_path = _paper_script_path(str(raw_script))
            if script_path and is_final_artifact_path(script_path):
                paths_to_add.append(script_path)
            else:
                logger.warning("[%s] Ignoring non-paper script path from backflow: %s", state.repo, raw_script)
        msg = f"backflow: {state.repo} → {section_type}/{section_dir}"
        auto_commit_final_artifacts(
            paths_to_add,
            msg,
            dry_run=dry_run,
            push=push_final_artifacts,
        )

    return placement


def fan_out_discovery(
    state: "RepoState",
    findings: list[dict[str, Any]],
) -> list[str]:
    """After discovery R1, split contribution_opportunities into independent targets.

    Each opportunity gets its own target dir, state, and issue brief.
    Returns a list of new repo identifiers (e.g. "teorth/analysis#opp_1")
    that can be processed in parallel by the pipeline.
    """
    base = repo_base(state.repo)
    slug = repo_slug(state.repo)

    # Extract contribution_opportunities from findings
    opportunities = []
    for f in findings:
        if isinstance(f, dict):
            # Discovery mode returns opportunities in the findings list
            if f.get("type") in ("data_pr", "script_pr", "computation",
                                  "mathematical_result", "tooling"):
                opportunities.append(f)
            # Also check for nested contribution_opportunities
            for opp in f.get("contribution_opportunities", []):
                if isinstance(opp, dict):
                    opportunities.append(opp)

    if not opportunities:
        logger.info("[%s] Fan-out: no contribution_opportunities found in R1", state.repo)
        return []

    new_targets: list[str] = []
    for idx, opp in enumerate(opportunities, 1):
        title = opp.get("title", f"opportunity_{idx}")
        # Create a slug-safe identifier
        opp_slug = re.sub(r"[^a-zA-Z0-9_]", "_", title.lower())[:40].rstrip("_")
        opp_id = f"{base}#opp_{idx}_{opp_slug}"
        opp_dir_slug = repo_slug(opp_id)

        # Create target directory with the opportunity as an issue brief
        target_dir = SCRIPT_DIR / "targets" / opp_dir_slug
        target_dir.mkdir(parents=True, exist_ok=True)

        brief = (
            f"# {base} — Opportunity {idx}: {title}\n\n"
            f"**Type:** {opp.get('type', 'unknown')}\n"
            f"**Effort:** {opp.get('effort', 'unknown')}\n\n"
            f"## Their Gap\n{opp.get('their_gap', opp.get('target_need', 'N/A'))}\n\n"
            f"## Our Asset\n{opp.get('our_asset', opp.get('our_side', 'N/A'))}\n\n"
            f"## Deliverable\n{opp.get('deliverable', opp.get('bridge', 'N/A'))}\n\n"
            f"## Impact\n{opp.get('impact', 'N/A')}\n\n"
            f"## Context from Discovery\n"
            f"Parent discovery: {state.repo}\n"
            f"Automath refs: {opp.get('automath_refs', [])}\n"
        )
        brief_path = target_dir / "opportunity_brief.md"
        brief_path.write_text(brief, encoding="utf-8")

        # Create fresh state
        opp_state = {
            "schema_version": OUTREACH_STATE_SCHEMA_VERSION,
            "repo": opp_id,
            "stage": "B",
            "round": 0,
            "scores": {"codex": [], "claude": [], "final": []},
            "findings": [],
            "action_history": [],
            "timestamps": {"created_at": iso_now()},
            "error": "",
            "draft_title": "",
            "draft_body": "",
            "submission_url": "",
        }
        state_path = STATE_DIR / f"{opp_dir_slug}.json"
        state_path.write_text(json.dumps(opp_state, indent=2), encoding="utf-8")

        new_targets.append(opp_id)
        logger.info("[%s] Fan-out: created opportunity %d/%d → %s (%s)",
                    state.repo, idx, len(opportunities), opp_id, title)

    logger.info("[%s] Fan-out complete: %d opportunities → %d targets",
                state.repo, len(opportunities), len(new_targets))
    return new_targets


def _tex_escape(text: str) -> str:
    """Minimal LaTeX escaping for generated content."""
    if not isinstance(text, str):
        text = str(text)
    for char, repl in [("&", "\\&"), ("%", "\\%"), ("#", "\\#"), ("_", "\\_"), ("{", "\\{"), ("}", "\\}")]:
        text = text.replace(char, repl)
    return text


def is_final_artifact_path(path: str | Path) -> bool:
    rel = _rel_from_any(path)
    allowed_prefixes = (
        _repo_relative(MAIN_PAPER_DIR / "sections") + "/",
        _repo_relative(MAIN_PAPER_DIR / "scripts") + "/",
    )
    return any(rel.startswith(prefix) for prefix in allowed_prefixes)


def _paper_script_path(raw: str) -> Optional[Path]:
    if not raw:
        return None
    path = Path(raw)
    if path.is_absolute():
        return path
    rel = str(path).replace("\\", "/").lstrip("./")
    if rel.startswith(_repo_relative(MAIN_PAPER_DIR / "scripts") + "/"):
        return REPO_ROOT / rel
    if rel.startswith("scripts/"):
        return MAIN_PAPER_DIR / rel
    if rel.startswith("theory/"):
        return REPO_ROOT / rel
    return MAIN_PAPER_DIR / "scripts" / rel


def auto_commit_final_artifacts(
    paths: list[str | Path],
    msg: str,
    *,
    dry_run: bool = False,
    push: bool = True,
) -> None:
    """Commit only reviewed final artifacts; never commit runtime intermediates."""
    if dry_run:
        return

    rel_paths: list[str] = []
    rejected: list[str] = []
    for path in paths:
        rel = _rel_from_any(path)
        if is_intermediate_path(rel) or not is_final_artifact_path(rel):
            rejected.append(rel)
        else:
            rel_paths.append(rel)

    if rejected:
        raise RuntimeError(
            "Refusing to commit non-final/intermediate outreach paths: "
            + ", ".join(rejected[:8])
        )
    if not rel_paths:
        logger.info("No final artifacts to commit for: %s", msg)
        return

    with git_ops_lock():
        subprocess.run(
            ["git", "add", *rel_paths],
            cwd=str(REPO_ROOT),
            capture_output=True,
            timeout=30,
        )
        result = subprocess.run(
            ["git", "commit", "-m", msg, "--", *rel_paths],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode != 0:
            logger.debug("Final artifact commit skipped: %s", (result.stderr or result.stdout)[:300])
            return
        logger.info("Committed final artifacts: %s", msg)

        if push:
            pushed = subprocess.run(
                ["git", "push", "origin", "HEAD"],
                cwd=str(REPO_ROOT),
                capture_output=True,
                text=True,
                timeout=60,
            )
            if pushed.returncode == 0:
                logger.info("Pushed final artifact commit")
            else:
                logger.warning("Push failed: %s", pushed.stderr[:200])


def auto_commit_push(repo: str, stage: str, round_num: int, score: int, *, dry_run: bool = False) -> None:
    """Record a local checkpoint without committing runtime intermediates.

    Outreach state, target research docs, logs, and drafts are runtime
    intermediates. Final artifacts are committed only through
    auto_commit_final_artifacts().
    """
    if dry_run:
        return
    logger.info(
        "Local checkpoint only: %s Stage %s R%d (score=%d); no git commit/push",
        repo,
        stage,
        round_num,
        score,
    )


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
    # Accept "owner/name" or "owner/name#123"
    return bool(re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(#\d+)?", repo.strip()))


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

    base = repo_base(repo)
    if base == "the-omega-institute/automath":
        yield REPO_ROOT
        return

    temp_dir = Path(tempfile.mkdtemp(prefix=f"outreach_{repo_slug(repo)}_"))
    clone_dir = temp_dir / base.split("/", 1)[1]
    try:
        result = run_cmd(
            ["git", "clone", "--depth", "1", f"https://github.com/{base}.git", str(clone_dir)],
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
    otherwise falls back to static Lean source scanning.

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

    scope_context = build_scope_context(repo)
    context_header = agent_context_header("context_aware", scope_context)

    # If we have target-specific docs (issue briefs, prior research), use them
    if target_context:
        plan = {
            "codex_task": (
                f"{context_header}\n"
                f"Read the research documents below for {repo}. "
                f"They describe specific issues, prior results, and computation data. "
                f"Your job: continue the research described, address open questions, "
                f"and produce findings that are NEW and USEFUL to the target.\n"
                f"{NO_LEAN_EXECUTION_POLICY}\n"
                f"{target_context}"
            ),
            "target_format": "GitHub issue",
            "target_format_example": "README.md",
            "output_type": "findings JSON",
            "output_path": str(target_dir / "research.md"),
            "content_list": [],
            "what_target_gains": "answers to their specific open questions",
            "backflow": {"enabled": True, "description": "new computation results"},
            "mode": "directed",
        }
        logger.info("[%s] B0 plan from target docs (%d chars context)", repo, len(target_context))
        return plan

    # DISCOVERY MODE: no target docs → scan the repo for contribution opportunities.
    # Read their README, CONTRIBUTING, recent PRs, code structure.
    # Find where OUR results add value, not where THEIR gaps are.
    base = repo_base(repo)
    plan = {
        "codex_task": (
            f"{context_header}\n"
            f"DISCOVERY MODE for {base}.\n\n"
            f"You are looking for ways the Omega project (https://github.com/the-omega-institute/automath) "
            f"can make SUBSTANTIVE contributions to {base}. Not bug fixes, not doc edits, not filling "
            f"their known gaps. We want to ADD something they don't have — computed results, mathematical "
            f"connections, data, proofs, or tools that come from our x²=x+1 framework.\n\n"
            f"STEP 1: Understand their project deeply.\n"
            f"- `gh api repos/{base}/contents/README.md --jq '.content' | base64 -d`\n"
            f"- `gh api repos/{base}/contents/CONTRIBUTING.md --jq '.content' | base64 -d` (if exists)\n"
            f"- `gh pr list --repo {base} --state merged --limit 10 --json number,title,author`\n"
            f"- `gh issue list --repo {base} --state open --limit 20 --json number,title,labels`\n"
            f"- Browse their code structure and Lean modules as static text only\n\n"
            f"STEP 2: Understand OUR project.\n"
            f"- Read our paper: `head -100 theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/main.tex`\n"
            f"- Our Lean modules may be inspected with cat/rg only; do not run Lean tooling\n"
            f"- Our scripts: `ls theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/scripts/equational_theory/`\n"
            f"- Existing committed Lean theorem refs are prior evidence, not something this pipeline recompiles\n\n"
            f"{NO_LEAN_EXECUTION_POLICY}\n\n"
            f"STEP 3: Find where our work adds value to theirs.\n"
            f"- What mathematical structures do we both care about?\n"
            f"- Where do our computed results answer their open questions?\n"
            f"- What can we PR that showcases Omega while being genuinely useful?\n"
            f"- Think: data contributions, new computational results, mathematical bridges\n"
            f"- NOT: fixing their typos, filling their sorries, reviewing their PRs\n\n"
            f"Be specific. Name files, functions, theorem names, issue numbers."
        ),
        "target_format": "GitHub PR or issue",
        "target_format_example": "README.md CONTRIBUTING.md",
        "output_type": "findings JSON",
        "output_path": str(target_dir / "research.md"),
        "content_list": [],
        "what_target_gains": "new mathematical results from the Omega framework",
        "backflow": {"enabled": True, "description": "discoveries from target scanning"},
        "mode": "discovery",
    }
    logger.info("[%s] B0 plan: DISCOVERY MODE (no target docs)", repo)
    return plan

    # FALLBACK: generic plan from static Lean source scanning (only if discovery mode is disabled)
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
                "category": "open_reference",
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
                    "category": "proved_reference",
                    "ams": "37",
                    "source_file": "lean4/Omega/Folding/MomentSum.lean",
                    "doc_comment": f"Proved: {name}",
                    "proved": True,
                })

    # FiberRing.lean — proved ring isomorphism
    formalized_results: list[dict[str, Any]] = [{
        "name": "stableValueRingEquiv",
        "category": "proved_reference",
        "ams": "11",
        "source_file": "lean4/Omega/Folding/FiberRing.lean:157",
        "doc_comment": "X_m is ring-isomorphic to ZMod(Nat.fib(m+2))",
        "proved": True,
    }]

    # S₃ recurrence IS PROVED (S3Recurrence.lean + CCSPrime8Split.lean, no sorry).
    # Mark as an existing proved reference, not open.
    key_results: list[dict[str, Any]] = [{
        "name": "S₃_recurrence",
        "category": "proved_reference",
        "ams": "37",
        "source_file": "lean4/Omega/Folding/S3Recurrence.lean",
        "doc_comment": "S₃ linear recurrence: proved unconditionally in Automath",
        "proved": True,
    }, {
        "name": "S₂_exponential_growth",
        "category": "open_reference",
        "ams": "37",
        "source_file": "lean4/Omega/Folding/MomentRecurrence.lean",
        "doc_comment": "S₂(m) = Theta(lambda_+^m) where lambda_+ is Perron root of t³-2t²-2t+2",
        "proved": False,
    }]

    all_content = test_cases[:5] + formalized_results + key_results + open_conjectures[:4]

    # Determine target format from repo
    if "formal-conjectures" in repo:
        task = (
            "Draft a GitHub issue or data-contribution proposal for formal-conjectures. "
            "Do not write Lean files or proofs. If a future Lean PR is appropriate, "
            "describe it as a separate manual follow-up with exact source references."
        )
        fmt = "GitHub issue"
        example = "FormalConjectures/Wikipedia/ABC.lean"
        output = "tools/community-outreach/drafts/OmegaGoldenMeanShift_issue.md"
    elif "equational_theories" in repo:
        task = (
            "Construct Fibonacci ring-operation magmas as separating countermodels. "
            "Use Python/combinatorial certificates and paper references only. "
            "Do not define Lean magmas, run Lean, or edit Lean files."
        )
        fmt = "GitHub issue + data"
        example = "README.md CONTRIBUTING.md"
        output = "tools/community-outreach/drafts/FibonacciMagmas_issue.md"
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

        {NO_LEAN_EXECUTION_POLICY}

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
           PROVED = already present in committed Automath text/Lean/paper sources
           OPEN = explicitly not proved by the current Automath sources

        3. Write a COMPLETE content list for Codex. Codex should NOT search or decide
           what to include — it should only draft target-facing text/artifact plans.

        4. If deep research produces NEW results, flag for backflow to main paper.

        Return JSON only:
        {{
          "codex_task": "Draft a target-facing issue/reply/artifact plan containing exactly the items listed below.
                        Do NOT add, remove, or modify items. Do not write or run Lean.",
          "target_format": "GitHub issue|PR plan|zulip post|email|data artifact",
          "target_format_example": "URL to example file in target repo to copy format from",
          "output_type": "issue body|post text|data artifact plan",
          "output_path": "where to write the output",
          "content_list": [
            {{
              "name": "theorem/conjecture name",
              "category": "proved_reference|open_reference|new_result|computation",
              "ams": "11|37|40|47",
              "source_file": "lean4/Omega/path/File.lean:line",
              "statement": "mathematical statement in prose/LaTeX, not Lean code",
              "doc_comment": "one-line description",
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
    scope_context = build_scope_context(repo)
    return textwrap.dedent(
        f"""\
        You are Stage B1 of a community outreach pipeline.

        Repository target: {repo}
        Automath repo root: {REPO_ROOT}
        Forbidden paths: {", ".join(FORBIDDEN_PATH_PATTERNS)}
        {NO_LEAN_EXECUTION_POLICY}
        {agent_context_header("context_aware", scope_context)}

        Read the target repository and the Automath repository. Identify the
        mathematically substantive parts of the target repo, especially static
        Lean 4 source text, README claims, and any PDF papers. Do not compile
        or edit Lean.

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

    scope_context = build_scope_context(repo)
    context_header = agent_context_header("context_aware", scope_context)

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

        target_dir = target_dir_for_repo(repo)
        scripts_available = ""
        if target_dir.exists():
            scripts = [f.name for f in target_dir.iterdir() if f.suffix == ".py"]
            if scripts:
                scripts_available = f"\n\nAvailable scripts in {target_dir}:\n" + "\n".join(f"  - {s}" for s in scripts)

        return textwrap.dedent(
            f"""\
            You are a research mathematician continuing deep work on {repo}.
            Your goal: RESOLVE the open questions below. Use whatever tools you need.
            {NO_LEAN_EXECUTION_POLICY}
            {context_header}

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
            - Needs literature/code reading → read the relevant files as text
            - Needs Lean formalization → mark as blocked/future external verification
            First declare `research_route` as exactly one of computation, proof,
            or hybrid. If the scope ledger supplied a recommended route, follow
            it unless you explicitly justify an override.

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
              "research_route": "computation|proof|hybrid",
              "route_reason": "why this route fits the scope",
              "route_contract_satisfied": true,
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

    # R1 PATH: discovery or directed bridge-finding
    if claude_plan and claude_plan.get("codex_task"):
        base = repo_base(repo)
        mode = claude_plan.get("mode", "directed")

        # DISCOVERY MODE: scan repo for contribution opportunities
        if mode == "discovery":
            existing_block = ""
            if existing_research:
                existing_block = f"\nEXISTING RESEARCH (BUILD ON THIS):\n{existing_research[:4000]}\n"
            return textwrap.dedent(
                f"""\
                {claude_plan.get('codex_task', '')}
                {NO_LEAN_EXECUTION_POLICY}
                {context_header}
                {existing_block}
                Return JSON:
                {{
                  "research_route": "computation|proof|hybrid",
                  "route_reason": "why this route fits the scope",
                  "route_contract_satisfied": true,
                  "target_summary": "what {base} does and what they need",
                  "contribution_opportunities": [
                    {{
                      "title": "what we can contribute",
                      "type": "data_pr|script_pr|computation|mathematical_result|tooling",
                      "their_gap": "what they're missing or what would help them",
                      "our_asset": "what Omega result or tool fills this gap",
                      "deliverable": "concrete: file path, PR description, data format",
                      "effort": "low|medium|high",
                      "impact": "how this makes Omega visible while helping them"
                    }}
                  ],
                  "findings": [
                    {{
                      "title": "mathematical connection found",
                      "type": "theorem|computation|data|conjecture",
                      "status": "proved|computed|proposed",
                      "their_side": "what they have",
                      "our_side": "what we have",
                      "bridge": "the connection",
                      "target_need": "how this helps THEM",
                      "automath_refs": ["lean4/Omega/path:line"]
                    }}
                  ],
                  "recommended_first_action": "what to do first (be specific)"
                }}
                """
            )

        # DIRECTED MODE: bridge-finding for a specific issue/task
        return textwrap.dedent(
            f"""\
            You are a mathematical research analyst. Your job is to find deep
            connections between two projects, like a researcher writing a bridge paper.

            TARGET: {base}
            TASK: {claude_plan.get('codex_task', '')}
            {NO_LEAN_EXECUTION_POLICY}
            {context_header}
            {"" if not existing_research else chr(10) + "═══════════════════════════════════════════════════════════════" + chr(10) + "EXISTING RESEARCH (from previous runs — BUILD ON THIS, don't discard):" + chr(10) + "═══════════════════════════════════════════════════════════════" + chr(10) + existing_research[:4000] + chr(10) + chr(10) + "Keep the findings above. You may ADD new ones but do NOT remove existing." + chr(10)}
            ═══════════════════════════════════════════════════════════════
            STEP 1: DEEP-READ THE TARGET
            ═══════════════════════════════════════════════════════════════
            Read the target project thoroughly:
            - `gh api repos/{base}/contents/README.md --jq '.content' | base64 -d`
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
            These are text-inspection commands only; do not run Lean tooling.

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
              "research_route": "computation|proof|hybrid",
              "route_reason": "why this route fits the scope",
              "route_contract_satisfied": true,
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
        deep_section = textwrap.dedent(f"""

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

        6. 坏例子结构定理驱动约束:
        {BAD_EXAMPLE_DEEP_RESEARCH_STANDARD_ZH}
        """)

    return textwrap.dedent(
        f"""\
        You are Stage B2 of a community outreach pipeline.

        Repository target: {repo}
        Automath repo root: {REPO_ROOT}
        Forbidden paths: {", ".join(FORBIDDEN_PATH_PATTERNS)}
        {NO_LEAN_EXECUTION_POLICY}
        {context_header}

        Stage B1 output:
        {json.dumps(b1_data, indent=2, ensure_ascii=False)}{feedback_section}{whitelist_section}{deep_section}

        ═══════════════════════════════════════════════════════════════
        CLAUDE'S PLAN (B0) — FOLLOW THIS EXACTLY
        ═══════════════════════════════════════════════════════════════
        {json.dumps(claude_plan or {}, indent=2, ensure_ascii=False)}

        YOUR JOB: Take the "content_list" above and draft target-facing
        prose/artifact plans in the target repo's structure. Do NOT add items.
        Do NOT remove items. Do NOT change mathematical statements. ONLY format.
        Do not generate Lean files.

        Before doing substantive work, declare `research_route` as exactly
        "computation", "proof", or "hybrid". Use the scope ledger route when
        supplied. The final findings must satisfy the corresponding route
        contract from the research-route policy.

        If "content_list" is provided:
          - Read the "target_format_example" to learn the exact file format
          - Write each item from content_list into target-facing prose
          - Use the category, AMS tag, statement, and source_file exactly as given
          - Do not add imports, proof terms, `sorry`, or Lean syntax

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

        Automath is a large project. USE YOUR TOOLS to search static text.
        Search the ENTIRE project, not just lean4/:

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
              for the special case Z, with an existing committed Lean 4 reference
              or paper proof at file:line."
        Bad:  "Automath's theorem Y is related to your theorem X."

        Research standard (must follow verbatim):
        {RESEARCH_STANDARD_ZH}

        HARD CONSTRAINTS:
        1. Every `automath_refs` entry MUST point to a real file:line in the Automath repo.
           Do NOT invent paths. Verify the file exists before citing it.
        2. Theorem names MUST match actual committed Lean 4 theorem names from the whitelist,
           but do not run Lean to check them.
        3. Do NOT invent fictional mathematical objects.
        4. If the target repo has no needs Automath can help with, return
           `"findings": []` with `"stop_reason"` explaining why.
        5. Every finding MUST include `"target_need"` — what specific need
           of the target repo this finding addresses.

        Return JSON only:
        {{
          "research_route": "computation|proof|hybrid",
          "route_reason": "why this route fits the scope",
          "route_contract_satisfied": true,
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
    No Lean execution is allowed; if a claim is wrong, fix it."""
    return textwrap.dedent(
        f"""\
        You made these mathematical claims about {repo}. Some may have concrete
        algebra errors. Your job: VERIFY each concrete claim with Python, then
        fix or remove any that fail.
        {NO_LEAN_EXECUTION_POLICY}

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
        {NO_LEAN_EXECUTION_POLICY}

        Penalize any finding that claims this pipeline ran Lean, added Lean
        proofs, or completed local formalization.
        Penalize missing or incoherent research_route declarations. A computation
        route must include reproducible scripts/certificates; a proof route must
        include real proof text; a hybrid route must include both.

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
    scope_context = build_scope_context(repo)
    return textwrap.dedent(
        f"""\
        You are Stage B4 (Claude final review) of a community outreach pipeline.

        Review the findings below for repository {repo}.
        Score on THREE dimensions equally weighted:
        {NO_LEAN_EXECUTION_POLICY}
        {agent_context_header("context_aware", scope_context)}

        1. CORRECTNESS: Is the math right? Are PROVED items actually proved in
           Automath? Are OPEN items actually open (not proved elsewhere)?
           CRITICAL: use committed Automath text/Lean refs and paper sections as
           static evidence only; do not request or assume a local Lean build.
        2. PLAN COMPLIANCE: Did Codex follow the B0 content_list exactly?
           Every item from the list should be present. No invented items.
           Correct category tags (proved_reference, open_reference, new_result, computation).
        3. FORMAT QUALITY: Does the output match the target-facing artifact?
           Reject generated Lean code, imports, proof terms, or `sorry` blocks.
        4. ROUTE CONTRACT: Did Codex declare computation/proof/hybrid and satisfy
           that contract? Computation needs reproducible artifacts; proof needs
           theorem/proof text; hybrid needs both certificate and interpretation.

        Score 8+ if: all content_list items present, math correct, no Lean execution
        is claimed, and the artifact is useful to the target.
        Score <5 if: Codex added items not in the plan, got proved/open wrong, or
        claims local Lean compilation/formalization.

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
    allow_low_score_backflow: bool = False,
    push_final_artifacts: bool = True,
    skip_mid_claude: bool = False,
) -> RepoState:
    if state.stage not in {"B", "NEW"}:
        return state

    # Bug 4 fix: build real Automath theorem whitelist for grounding
    automath_theorem_whitelist = load_automath_theorem_whitelist()

    # Bug 1 fix: accumulate previous rounds' feedback to pass to next round
    previous_rounds_feedback: list[dict[str, Any]] = []
    b0_plan: dict[str, Any] = {}

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
                existing_doc = target_dir_for_repo(state.repo) / "research.md"
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
            if isinstance(parsed_b2, dict) and findings:
                route = str(parsed_b2.get("research_route", "")).strip().lower()
                if route in {"computation", "proof", "hybrid"}:
                    for finding in findings:
                        finding.setdefault("research_route", route)
                        finding.setdefault("route_reason", str(parsed_b2.get("route_reason", "")))
                        finding.setdefault(
                            "route_contract_satisfied",
                            bool(parsed_b2.get("route_contract_satisfied", False)),
                        )

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
            if is_first_round and findings and not skip_mid_claude:
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

            if skip_mid_claude:
                b4_data = {
                    "overall_score": coerce_score(b3_data.get("overall_score"), 0),
                    "verdict": "pass" if coerce_score(b3_data.get("overall_score"), 0) >= PASS_SCORE else "retry",
                    "notes": "Mid-pipeline Claude research review skipped by --skip-mid-claude",
                    "action_items": [],
                }
            else:
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

        # AUTO-SKIP: if Claude says "skip this target entirely" or verdict=skip,
        # don't waste R2-R5 on a dead target
        claude_verdict = str(b4_data.get("verdict", "")).lower()
        claude_notes = str(b4_data.get("notes", "")).lower()
        if claude_verdict == "skip" or "skip entirely" in claude_notes or "no viable contribution" in claude_notes:
            logger.info("[%s] Claude recommends skip — terminating early", state.repo)
            state.stage = "SKIPPED"
            state.error = ""
            state.timestamps["completed_at"] = iso_now()
            state.log_event("B", "auto-skipped (Claude recommendation)",
                            score=final_score, verdict="skip",
                            detail=str(b4_data.get("notes", ""))[:300])
            save_state(state)
            auto_commit_push(state.repo, "B-skip", round_num, final_score, dry_run=dry_run)
            return state

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

        # Document-driven local memory: write full findings + review to a file
        # so next round's Codex can READ the complete document, not just a summary.
        # targets/{repo}/ is ignored runtime scratch, not a branch artifact.
        target_dir = target_dir_for_repo(state.repo)
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
                    "research_route": f.get("research_route", ""),
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

        # DISCOVERY FAN-OUT: after R1 in discovery mode, split opportunities
        # into independent targets that can be processed in parallel.
        is_discovery = isinstance(b0_plan, dict) and b0_plan.get("mode") == "discovery"
        if is_first_round and is_discovery and findings:
            fan_out_targets = fan_out_discovery(state, findings)
            if fan_out_targets:
                state.stage = "FAN_OUT"
                state.timestamps["fan_out_at"] = iso_now()
                state.log_event("B", "discovery fan-out",
                                detail=json.dumps(fan_out_targets, ensure_ascii=False))
                save_state(state)
                logger.info("[%s] Discovery R1 complete → fan-out to %d targets. "
                            "Re-run pipeline with these targets for parallel execution.",
                            state.repo, len(fan_out_targets))
                return state

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
            backflow_placement = backflow_to_main_paper(
                state,
                model=model,
                dry_run=dry_run,
                push_final_artifacts=push_final_artifacts,
                skip_mid_claude=skip_mid_claude,
            )

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

    if allow_low_score_backflow:
        logger.warning("[%s] Backflow override enabled below pass gate (score=%d)",
                       state.repo, last_score)
        backflow_to_main_paper(
            state,
            model=model,
            dry_run=dry_run,
            push_final_artifacts=push_final_artifacts,
            skip_mid_claude=skip_mid_claude,
        )
    else:
        state.log_event(
            "B",
            "backflow skipped (below pass gate)",
            score=last_score,
            verdict="skip",
            detail=f"requires score >= {PASS_SCORE}; use --allow-low-score-backflow to override",
        )
        save_state(state)

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
    scope_context = build_scope_context(repo)

    # If backflow was done, include reference to the paper section
    backflow_context = ""
    if backflow_placement:
        section_type = backflow_placement.get("placement", "appendix")
        section_dir = backflow_placement.get("section_dir", "")
        backflow_context = (
            f"\n\nBACKFLOW COMPLETED: The research has been written into the Omega paper.\n"
            f"- Paper section: {section_type}/{section_dir}\n"
            f"- Verification scripts: in the paper's scripts/ directory\n"
            f"- Repo: {AUTOMATH_REPO_URL}\n\n"
            f"Your reply should mention the repo naturally. Lead with the math.\n"
        )

    return textwrap.dedent(
        f"""\
        You are Stage C1 of a community outreach pipeline.

        Draft a GitHub issue, issue reply, or scoped proposal for repository {repo}.
        This must read like a serious technical contribution, not a pitch.
        {NO_LEAN_EXECUTION_POLICY}
        {agent_context_header("context_aware", scope_context)}
        {backflow_context}
        Requirements:
        - Include the main theorem statement(s) and proof sketch
        - Reference committed verification scripts and computational certificates.
          Prefer paper-side paths under theory/.../scripts/ when backflow copied them.
          Do not cite tools/community-outreach/targets/...; that directory is local scratch.
        - Prefer paper-side .tex/scripts over lean4/ refs. If paper-side artifacts
          exist, do not list lean4/ paths in the public draft; keep Lean refs as
          internal audit anchors only.
        - Cite existing committed Automath Lean 4 theorem references using exact file:line form
          only when they are already present; do not claim new local Lean verification
        - Honest proved/conjectured/untested labeling
        - Explicitly keep the public reply within the verified current scope.
          If a stronger direction is interesting but unproved, label it as out-of-scope
          or omit it; it will be recorded in the local future queue.
        - Avoid self-promotion. Lead with the math, mention the repo naturally.
        - Do not introduce unrelated target-repo theorem anchors. The refs below
          are target repository refs, not Automath proof refs; cite them only if
          the finding directly depends on them.
        - The body must end with exactly:
          {AUTOMATH_TRAILER}
        - Return JSON only.

        {note_block}Findings:
        {json.dumps(findings, indent=2, ensure_ascii=False)}

        Target repository Lean theorem refs (not Automath refs):
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


def build_stage_c2_prompt(
    repo: str,
    title: str,
    body: str,
    findings: list[Any],
    backflow_placement: Optional[dict[str, Any]] = None,
    agent_context_mode: str = "context_aware",
) -> str:
    scope_context = build_scope_context(repo)
    backflow_block = "No backflow placement was supplied."
    if backflow_placement:
        backflow_block = json.dumps(backflow_placement, indent=2, ensure_ascii=False)
    return textwrap.dedent(
        f"""\
        You are Stage C2 of a community outreach pipeline.

        Review the GitHub issue draft below for repository {repo}.
        {NO_LEAN_EXECUTION_POLICY}
        {agent_context_header(agent_context_mode, scope_context)}
        Check:
        - technical accuracy
        - tone (no self-promotion)
        - honest proved/conjectured/untested labeling
        - Automath Lean 4 theorem references are real-looking, specific file:line refs
        - target-repo theorem refs are used only when directly relevant
        - no unrelated theorem anchors are introduced from the target repository
        - paper backflow context is reflected when backflow exists
        - verification artifacts are committed/public paths, not private scratch paths
        - the draft closes only the verified current scope and does not sell deferred
          future-queue items as completed results
        - body ends with {AUTOMATH_TRAILER}

        Reject the draft if it cites a theorem/object not present in the findings,
        if it turns a conjecture into a proved theorem, or if it reads like an
        Automath advertisement rather than a target-facing technical contribution.
        Also reject it if it claims that this outreach run compiled Lean, added a
        Lean proof, ran `lake build`, or otherwise completed local formalization.

        Return JSON only:
        {{
          "approved": true,
          "overall_score": 1,
          "title": "possibly revised title",
          "body": "possibly revised body",
          "notes": "short review note"
        }}

        Findings:
        {json.dumps(findings[:8], indent=2, ensure_ascii=False)}

        Backflow placement:
        {backflow_block}

        Draft title:
        {title}

        Draft body:
        {body}
        """
    )


def fallback_draft(
    repo: str,
    findings: list[dict[str, Any]],
    theorem_refs: list[str],
    backflow_placement: Optional[dict[str, Any]] = None,
) -> tuple[str, str]:
    section_dir = (backflow_placement or {}).get("section_dir", "")
    tex_path = str((backflow_placement or {}).get("tex_path", ""))
    if section_dir == "signed_companion_collision_audit":
        title = "Signed companion determinant audit and exterior-Lucas certificate"
        body = "\n".join(
            [
                "I prepared a compact audit note for the signed companion convention used in the collision-kernel calculations.",
                "",
                "### Main statement",
                "",
                "For the signed Frobenius recurrence companion `A(c)` attached to the monic polynomial",
                "",
                "`x^d + c_1 x^{d-1} + ... + c_d`,",
                "",
                "the determinant identity is",
                "",
                "`det(I - A(c)) = 1 + sum_i c_i`.",
                "",
                "For the ordinary recurrence companion with the opposite sign convention, the corresponding determinant is `1 - sum_i c_i`; the two conventions therefore differ by a sign conversion rather than by a new invariant.",
                "",
                "For the audited q=6 and q=7 recurrence vectors, the signed proxy determinants are `110` and `422`.",
                "",
                "### Finite certificate",
                "",
                "The paper-side certificate checks the exterior-Lucas comparison for q=2,...,23. In that range, `c_{q,2} = Lucas(q)` holds exactly for q=3,4,5 and fails for q=2 and every q=6,...,23. The simultaneous triple coincidence with the signed determinant excess occurs exactly at q=5 in the audited range.",
                "",
                "### Paper-side artifacts",
                "",
                f"- `{_repo_relative(Path(tex_path)) if tex_path else 'the main-paper appendix section signed_companion_collision_audit'}`",
                "- `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/scripts/equational_theory/signed_companion_collision_audit.py`",
                "- `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/scripts/equational_theory/exterior_lucas_certificate_q2_23.json`",
                "",
                "### Status",
                "",
                "- Proved in the paper note: the signed determinant convention and the q=6,7 signed proxy determinant values.",
                "- Computationally certified: the q=2,...,23 exterior-Lucas table.",
                "- Not claimed here: a nonnegative collision-kernel presentation, a Bowen-Franks invariant statement, or an SFT flow-equivalence certificate for q=6 or q=7. Those require separate nonnegative-presentation or flow-equivalence data.",
                "",
                AUTOMATH_TRAILER,
            ]
        )
        return title, sanitize_issue_text(body)

    if section_dir == "window6_countermodel_certificate":
        title = "Window-6 CRT countermodel certificate for #364"
        body = "\n".join(
            [
                "I have a compact finite countermodel certificate that looks relevant to #364.",
                "",
                "### Claim",
                "",
                "Let `G` be the magma on `Fin 21` defined by",
                "",
                "```text",
                "x ◇ y = 7x + 15y mod 21.",
                "```",
                "",
                "Using `21 = 3 * 7`, the CRT presentation identifies this operation with",
                "",
                "```text",
                "(a3,a7) ◇ (b3,b7) = (a3,b7)",
                "```",
                "",
                "on `ZMod 3 × ZMod 7`. Therefore every binary term evaluates by keeping the first variable in the `ZMod 3` coordinate and the last variable in the `ZMod 7` coordinate. A law holds in this magma exactly when the two sides have the same first and last variables.",
                "",
                "Direct enumeration against the current order-four ETP equation list gives:",
                "",
                "```lean",
                "Facts G [10, 52, 55] [43, 46]",
                "```",
                "",
                "That is, `G` satisfies `E10`, `E52`, and `E55`, and refutes `E43` and `E46`.",
                "",
                "### Current-head freshness",
                "",
                "The audit was run against ETP commit `b99c0e486501e5b0690ef3fe5250d3aa57e63478`. The combined `[10,52,55] / [43,46]` certificate has no exact `Facts` entry and no satisfied/refuted superset entry in `full_entries.json` at that commit.",
                "",
                "Five of the six pairwise consequences are also absent as exact entries and as superset entries:",
                "",
                "- `E10` does not imply `E46`",
                "- `E52` does not imply `E43`",
                "- `E52` does not imply `E46`",
                "- `E55` does not imply `E43`",
                "- `E55` does not imply `E46`",
                "",
                "The remaining pair, `E10` does not imply `E43`, is already covered upstream by two `Fin 2` `SmallMagmas.lean` facts, so I would not claim novelty for that pair.",
                "",
                "### Paper-side artifacts",
                "",
                f"- `{_repo_relative(Path(tex_path)) if tex_path else 'theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/appendix/window6_countermodel_certificate/main.tex'}`",
                "- `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/scripts/equational_theory/audit_window6_current.py`",
                "",
                "### Scope",
                "",
                "The CRT/rectangular-band argument is a mathematical proof of the structure of this `Fin 21` magma. The indexed ETP law satisfaction and current-head freshness checks are Python-verified finite data, not claimed here as new Lean theorems in ETP. I am also not claiming a broad graph-edge theorem, an all-prime-field result, or a general Fibonacci-linear framework contribution for #364.",
                "",
                AUTOMATH_TRAILER,
            ]
        )
        return title, sanitize_issue_text(body)

    if section_dir == "finite_conditional_expectation":
        title = "Finite fiber-average conditional expectation proposal"
        body = "\n".join(
            [
                "I extracted a small finite conditional-expectation lemma from the Automath fold audit that may be useful as a proposal for the analysis/probability side of this repository.",
                "",
                "### Main statement",
                "",
                "For a finite probability space `Ω`, a finite factor map `π : Ω → X`, and a real-valued function `f`, define `E_{π,μ} f` by averaging `f` on each positive-mass fiber of `π`. Then `E_{π,μ}` is the orthogonal projection in `L^2(Ω,μ)` onto the fiber-constant functions.",
                "",
                "Consequently, for every `f`,",
                "",
                "```text",
                "||f||_2^2 = ||E_{π,μ} f||_2^2 + ||f - E_{π,μ} f||_2^2,",
                "```",
                "",
                "and the finite variance decomposes as",
                "",
                "```text",
                "Var_μ(f) = Var_μ(E_{π,μ} f) + within_fiber_variance_{π,μ}(f).",
                "```",
                "",
                "The one-fiber uniform case gives the layer-average `L^2` contraction and zero-variance statement used in the Automath fold audits.",
                "",
                "### Possible target-side API",
                "",
                "If this is a useful direction for `teorth/analysis`, the contribution could be packaged as an explicit finite combinatorial counterpart to the usual conditional-expectation viewpoint:",
                "",
                "- a finite `fiberAverage` operator for a factor map",
                "- the `L^2` contraction/Pythagoras identity",
                "- finite mean and variance helpers",
                "- the corrected zero-variance statement for the one-atom quotient case",
                "",
                "### Paper-side artifact",
                "",
                f"- `{_repo_relative(Path(tex_path)) if tex_path else 'theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/appendix/finite_conditional_expectation/main.tex'}`",
                "",
                "### Scope",
                "",
                "This is a proposal/question rather than a finished PR. The theorem is elementary, and the point is to expose a clean finite fiber-average API that bridges explicit finite sums with the standard conditional-expectation viewpoint. I am not claiming that this outreach pipeline has added or checked a Lean file in the target repository. If the maintainers think the lemma belongs here, the next step would be a separate target-side Lean contribution reviewed against the repository's current probability API.",
                "",
                AUTOMATH_TRAILER,
            ]
        )
        return title, sanitize_issue_text(body)

    title = f"Potential paper-side bridge for {repo.split('/')[-1]}"
    rows = []
    for item in findings[:5]:
        status = item.get("status", "untested")
        rows.append(
            f"| {item.get('title', 'Unnamed connection')} | {status} | "
            f"{item.get('bridge') or item.get('connection', '')} |"
        )
    if not rows:
        rows.append("| Candidate connection | untested | Requires fresh validation |")

    body = "\n".join(
        [
            "I found a few paper-side bridges that look worth checking against this target.",
            "",
            "| Correspondence | Status | Evidence |",
            "| --- | --- | --- |",
            *rows,
            "",
            "### Paper-side context",
            f"- Section: `{section_dir or 'not recorded'}`",
            f"- TeX path: `{_repo_relative(Path(tex_path)) if tex_path else 'not recorded'}`",
            "",
            "This draft intentionally cites paper-side artifacts rather than local outreach scratch files or new local Lean work.",
            "",
            AUTOMATH_TRAILER,
        ]
    )
    return title, sanitize_issue_text(body)


def _referenced_local_paths(text: str) -> list[Path]:
    patterns = (
        r"(lean4/[A-Za-z0-9_./-]+\.lean)",
        r"(theory/[A-Za-z0-9_./-]+\.(?:tex|py|lean|json))",
        r"(papers/[A-Za-z0-9_./-]+\.(?:tex|py|lean|json))",
        r"(tools/community-outreach/targets/[A-Za-z0-9_./-]+\.(?:py|json|md|lean))",
    )
    paths: dict[str, Path] = {}
    for pattern in patterns:
        for raw in re.findall(pattern, text):
            cleaned = raw.rstrip(".,);:`")
            paths[cleaned] = REPO_ROOT / cleaned
    return list(paths.values())


def validate_draft_contract(
    state: RepoState,
    *,
    backflow_placement: Optional[dict[str, Any]],
    dry_run: bool,
    fallback_used: bool = False,
) -> dict[str, Any]:
    """Deterministic Stage C gate before a draft can enter Stage D."""
    errors: list[str] = []
    warnings: list[str] = []
    best_score = max(state.scores.get("final", []) or [0])

    if not state.draft_title.strip():
        errors.append("empty draft title")
    if not state.draft_body.strip():
        errors.append("empty draft body")
    if state.draft_body and not state.draft_body.rstrip().endswith(AUTOMATH_TRAILER):
        errors.append("draft body does not end with Automath trailer")
    safe_deterministic_fallback = (
        fallback_used
        and "Paper-side artifacts" in state.draft_body
        and "lean4/" not in state.draft_body
        and "tools/community-outreach/targets/" not in state.draft_body
    )
    if fallback_used and not dry_run and not safe_deterministic_fallback:
        errors.append("C1 draft generation failed and fallback draft was used")
    body_without_trailer = state.draft_body.replace(AUTOMATH_TRAILER, "").strip()
    if len(body_without_trailer) < 500:
        errors.append("draft body is too short to be a substantive outreach reply")

    if not dry_run and best_score >= PASS_SCORE and not backflow_placement:
        errors.append("passed research gate but no persisted backflow placement was found")

    if backflow_placement:
        section_dir = str(backflow_placement.get("section_dir", "")).strip()
        tex_path = str(backflow_placement.get("tex_path", "")).strip()
        if section_dir and section_dir not in state.draft_body and tex_path and tex_path not in state.draft_body:
            warnings.append(f"draft does not mention backflow section/script context: {section_dir}")

    referenced_paths = _referenced_local_paths(state.draft_body)
    dirty = [] if dry_run else git_status_porcelain(referenced_paths)
    if dirty:
        errors.append("draft references uncommitted local artifacts: " + "; ".join(dirty[:8]))

    lean_execution_claims = (
        r"\blake build\b",
        r"\bran lake\b",
        r"\bcompiled (?:the )?Lean\b",
        r"\bverified with lake\b",
        r"\bLean proof (?:was )?added\b",
        r"\badded .*Lean proof\b",
        r"\bformalized in Lean\b",
    )
    if any(re.search(pattern, state.draft_body, flags=re.IGNORECASE) for pattern in lean_execution_claims):
        errors.append("draft claims local Lean execution/formalization, but this pipeline is no-Lean-execution")

    scratch_refs = [
        _repo_relative(path)
        for path in referenced_paths
        if "tools/community-outreach/targets/" in _repo_relative(path)
    ]
    if scratch_refs:
        warnings.append(
            "draft cites outreach scratch artifacts; prefer paper-side theory/.../scripts paths: "
            + ", ".join(scratch_refs[:5])
        )

    return {
        "schema_version": OUTREACH_CONTRACT_SCHEMA_VERSION,
        "approved": not errors,
        "errors": errors,
        "warnings": warnings,
        "referenced_paths": [_repo_relative(path) for path in referenced_paths],
        "backflow": backflow_placement or {},
        "outreach_kind": state.outreach_kind or infer_outreach_kind(state.repo, backflow_placement),
    }


def run_stage_c(
    state: RepoState,
    *,
    inventory: dict[str, Any],
    theorem_refs: list[str],
    revision_note: str,
    model: Optional[str],
    dry_run: bool,
    backflow_placement: Optional[dict[str, Any]] = None,
    no_claude_review: bool = False,
    c2_context_mode: str = "context_aware",
) -> RepoState:
    if state.stage not in {"C", "D"}:
        return state

    # Stage C runs AFTER backflow. The reply/issue draft references the paper
    # section produced inside the main paper tree.
    state.stage = "C"
    state.round = 1
    state.timestamps.setdefault("stage_c_started_at", iso_now())
    save_state(state)
    logger.info("[%s] Stage C (C1 draft + C2 review, backflow=%s)",
                state.repo, "yes" if backflow_placement else "no")

    fallback_used = False
    if dry_run:
        title, body = fallback_draft(
            state.repo,
            normalize_findings(state.findings),
            theorem_refs,
            backflow_placement=backflow_placement,
        )
        c2_data = {
            "approved": True,
            "overall_score": 8,
            "title": title,
            "body": body,
            "notes": "dry-run review",
        }
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
            raw_body = str(parsed_c1.get("body", "")).strip()
            body = sanitize_issue_text(raw_body) if raw_body else ""
        else:
            title, body = "", ""
        if not title or not body:
            fallback_used = True
            title, body = fallback_draft(
                state.repo,
                normalize_findings(state.findings),
                theorem_refs,
                backflow_placement=backflow_placement,
            )

        if no_claude_review:
            c2_data = {
                "approved": True,
                "overall_score": PASS_SCORE,
                "title": title,
                "body": body,
                "notes": "Claude review skipped; deterministic contract gate only",
            }
        else:
            c2_raw = claude_exec(
                build_stage_c2_prompt(
                    state.repo,
                    title,
                    body,
                    normalize_findings(state.findings),
                    backflow_placement=backflow_placement,
                    agent_context_mode=c2_context_mode,
                ),
                work_dir=REPO_ROOT,
                timeout=900,
                dry_run=dry_run,
            )
            parsed_c2 = parse_json_from_output(c2_raw)
            c2_data = parsed_c2 if isinstance(parsed_c2, dict) else {
                "approved": False,
                "overall_score": 0,
                "notes": "C2 returned no parseable JSON",
            }
            if c2_data.get("title"):
                title = str(c2_data.get("title", "")).strip()
            if c2_data.get("body"):
                body = sanitize_issue_text(str(c2_data.get("body", "")).strip())

    state.draft_title = title
    state.draft_body = sanitize_issue_text(body)
    state.outreach_kind = infer_outreach_kind(state.repo, backflow_placement)
    c2_score = coerce_score(c2_data.get("overall_score"), 0)
    approved_raw = c2_data.get("approved")
    c2_approval_flag = approved_raw is True or str(approved_raw).strip().lower() in {"true", "yes", "approved"}
    c2_approved = c2_approval_flag and c2_score >= PASS_SCORE
    contract = validate_draft_contract(
        state,
        backflow_placement=backflow_placement,
        dry_run=dry_run,
        fallback_used=fallback_used,
    )
    future_queue_added = (
        record_future_scope_items(state, contract=contract, dry_run=dry_run)
        if state.draft_body and contract["approved"]
        else 0
    )
    state.log_event(
        "C",
        "draft reviewed by C2",
        round=1,
        score=c2_score,
        verdict="advance" if c2_approved and contract["approved"] else "revise",
        detail=json.dumps(
            {
                "title": title[:120],
                "body_len": len(state.draft_body),
                "outreach_kind": state.outreach_kind,
                "c2_notes": str(c2_data.get("notes", ""))[:800],
                "c2_agent_context_mode": c2_context_mode,
                "contract": contract,
                "future_queue_added": future_queue_added,
            },
            ensure_ascii=False,
        ),
    )
    save_state(state)

    if state.draft_title and state.draft_body and c2_approved and contract["approved"]:
        state.stage = "D"
        state.round = 0
        state.error = ""
        state.timestamps["stage_c_completed_at"] = iso_now()
        save_state(state)
        auto_commit_push(state.repo, "C", 1, c2_score, dry_run=dry_run)
        return state

    state.stage = "C"
    state.round = 1
    reasons = []
    if not c2_approved:
        reasons.append(f"C2 score={c2_score}, approved={c2_approval_flag}")
    reasons.extend(contract["errors"])
    state.error = "; ".join(reasons)[:1000] or "Stage C draft did not pass review"
    save_state(state)
    auto_commit_push(state.repo, "C-review", 1, c2_score, dry_run=dry_run)
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
            f"Outreach kind: {state.outreach_kind or 'unspecified'}",
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
    allow_low_score_backflow: bool = False,
    push_final_artifacts: bool = True,
    no_claude_review: bool = False,
    skip_mid_claude: bool = False,
    c2_context_mode: str = "context_aware",
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
            backflow_placement = backflow_placement_from_history(state)
            if state.stage == "B":
                state = run_stage_b(
                    state,
                    inventory=inventory,
                    theorem_refs=theorem_refs,
                    model=model,
                    dry_run=dry_run,
                    todo_item=todo_item,
                    allow_low_score_backflow=allow_low_score_backflow,
                    push_final_artifacts=push_final_artifacts,
                    skip_mid_claude=skip_mid_claude,
                )
                backflow_placement = backflow_placement_from_history(state)

            # FAN_OUT: discovery R1 produced opportunities → return state
            # so orchestrator can spawn parallel targets
            if state.stage == "FAN_OUT":
                return state

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
                    no_claude_review=no_claude_review,
                    c2_context_mode=c2_context_mode,
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
    no_claude_review: bool = False,
    c2_context_mode: str = "context_aware",
) -> RepoState:
    while state.stage == "D":
        state, revision_note = run_stage_d(state, dry_run=dry_run)
        if state.stage != "C":
            return state
        with repo_checkout(state.repo, dry_run=dry_run) as repo_path:
            inventory = repo_inventory(repo_path, state.repo)
            theorem_refs = extract_lean_theorem_refs(repo_path)
            backflow_placement = backflow_placement_from_history(state)
            state = run_stage_c(
                state,
                inventory=inventory,
                theorem_refs=theorem_refs,
                revision_note=revision_note,
                model=model,
                dry_run=dry_run,
                backflow_placement=backflow_placement,
                no_claude_review=no_claude_review,
                c2_context_mode=c2_context_mode,
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
    allow_low_score_backflow: bool = False,
    push_final_artifacts: bool = True,
    no_claude_review: bool = False,
    skip_mid_claude: bool = False,
    c2_context_mode: str = "context_aware",
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
    worker_count = max(1, parallel)

    def _run_batch(repo_list: list[str]) -> list[RepoState]:
        batch_states: list[RepoState] = []
        if worker_count == 1 or len(repo_list) == 1:
            for repo in repo_list:
                batch_states.append(process_repo_to_stage_d(
                    repo,
                    skip_to=skip_to,
                    model=model,
                    dry_run=dry_run,
                    todo_item=todo_item,
                    allow_low_score_backflow=allow_low_score_backflow,
                    push_final_artifacts=push_final_artifacts,
                    no_claude_review=no_claude_review,
                    skip_mid_claude=skip_mid_claude,
                    c2_context_mode=c2_context_mode,
                ))
        else:
            with ThreadPoolExecutor(max_workers=min(worker_count, len(repo_list))) as executor:
                future_map = {
                    executor.submit(
                        process_repo_to_stage_d, repo,
                        skip_to=skip_to,
                        model=model,
                        dry_run=dry_run,
                        allow_low_score_backflow=allow_low_score_backflow,
                        push_final_artifacts=push_final_artifacts,
                        no_claude_review=no_claude_review,
                        skip_mid_claude=skip_mid_claude,
                        c2_context_mode=c2_context_mode,
                    ): repo
                    for repo in repo_list
                }
                for future in as_completed(future_map):
                    repo = future_map[future]
                    try:
                        batch_states.append(future.result())
                    except Exception as exc:
                        logger.exception("[%s] Worker failed", repo)
                        failed = RepoState(repo=repo, stage="ERROR", error=str(exc))
                        save_state(failed)
                        batch_states.append(failed)
        return batch_states

    # Phase 1: run initial batch (may include discovery targets)
    states = _run_batch(unique_repos)

    # Phase 2: fan-out — collect targets from discovery and process them
    fan_out_repos: list[str] = []
    for st in states:
        if st.stage == "FAN_OUT":
            for evt in reversed(st.action_history):
                if evt.get("action") == "discovery fan-out":
                    try:
                        targets = json.loads(evt.get("detail", "[]"))
                        fan_out_repos.extend(targets)
                    except (json.JSONDecodeError, TypeError):
                        pass
                    break

    if fan_out_repos:
        logger.info("Fan-out: processing %d discovered opportunities (parallel=%d)",
                    len(fan_out_repos), worker_count)
        fan_out_states = _run_batch(fan_out_repos)
        states.extend(fan_out_states)

    return sorted(states, key=lambda state: state.repo)


# ---------------------------------------------------------------------------
# Artifact hygiene / promotion
# ---------------------------------------------------------------------------


def tracked_intermediate_paths() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files"],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=30,
        encoding="utf-8",
        errors="replace",
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or "git ls-files failed")
    return sorted(path for path in result.stdout.splitlines() if is_intermediate_path(path))


def staged_intermediate_additions() -> list[str]:
    result = subprocess.run(
        ["git", "diff", "--cached", "--name-status"],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=30,
        encoding="utf-8",
        errors="replace",
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or "git diff --cached failed")
    bad: list[str] = []
    for line in result.stdout.splitlines():
        if not line.strip():
            continue
        status, _, path = line.partition("\t")
        if status.startswith("D"):
            continue
        if is_intermediate_path(path):
            bad.append(path)
    return sorted(bad)


def check_artifact_hygiene() -> bool:
    tracked = tracked_intermediate_paths()
    staged = staged_intermediate_additions()
    if tracked or staged:
        print("Outreach artifact hygiene: FAIL")
        if tracked:
            print("Tracked intermediate paths:")
            for path in tracked[:80]:
                print(f"  {path}")
            if len(tracked) > 80:
                print(f"  ... {len(tracked) - 80} more")
        if staged:
            print("Staged intermediate additions:")
            for path in staged[:80]:
                print(f"  {path}")
            if len(staged) > 80:
                print(f"  ... {len(staged) - 80} more")
        return False

    print("Outreach artifact hygiene: OK")
    return True


def promote_artifact(src_arg: str, dest_arg: str, *, dry_run: bool, push: bool) -> Path:
    src = Path(src_arg)
    if not src.is_absolute():
        src = REPO_ROOT / src
    dest = Path(dest_arg)
    if not dest.is_absolute():
        dest = REPO_ROOT / dest

    if not src.exists() or not src.is_file():
        raise RuntimeError(f"Promote source must be an existing file: {src_arg}")
    if is_intermediate_path(dest) or not is_final_artifact_path(dest):
        raise RuntimeError(
            "Promote destination must be a final artifact path under the main paper "
            f"sections/scripts tree: {_repo_relative(dest)}"
        )

    if dry_run:
        logger.info("[DRY RUN] promote %s → %s", _repo_relative(src), _repo_relative(dest))
        return dest

    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dest)
    auto_commit_final_artifacts(
        [dest],
        f"promote outreach artifact: {_repo_relative(dest)}",
        dry_run=dry_run,
        push=push,
    )
    return dest


def _state_updated_at(path: Path, data: dict[str, Any]) -> str:
    timestamps = data.get("timestamps", {})
    return str(timestamps.get("updated_at") or timestamps.get("created_at") or path.stat().st_mtime)


def archive_stale_states(*, dry_run: bool) -> list[Path]:
    """Move stale local state files into an ignored archive directory."""
    records: list[tuple[Path, dict[str, Any]]] = []
    for path in sorted(STATE_DIR.glob("*.json")):
        if path.name in {"processed.json", "candidates.json"}:
            continue
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        records.append((path, data))

    by_repo: dict[str, list[tuple[Path, dict[str, Any]]]] = {}
    for path, data in records:
        by_repo.setdefault(str(data.get("repo", "")), []).append((path, data))

    archive: set[Path] = set()
    for repo, items in by_repo.items():
        if len(items) <= 1:
            continue
        keep_path, _ = max(items, key=lambda item: _state_updated_at(item[0], item[1]))
        for path, _ in items:
            if path != keep_path:
                archive.add(path)

    for path, data in records:
        if data.get("stage") == "ERROR" and "object has no attribute 'events'" in str(data.get("error", "")):
            archive.add(path)

    if not archive:
        logger.info("No stale outreach state files to archive")
        return []

    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    archive_dir = STATE_DIR / "archive" / stamp
    moved: list[Path] = []
    for path in sorted(archive):
        dest = archive_dir / path.name
        logger.info("Archive stale state: %s → %s", path.name, dest.relative_to(STATE_DIR))
        if dry_run:
            moved.append(dest)
            continue
        dest.parent.mkdir(parents=True, exist_ok=True)
        path.replace(dest)
        moved.append(dest)
    return moved


# ---------------------------------------------------------------------------
# Status / CLI
# ---------------------------------------------------------------------------


def print_status() -> None:
    states = load_all_states()
    processed = load_processed_repos()
    future_queue = load_future_queue()
    repo_counts: dict[str, int] = {}
    for state in states:
        repo_counts[state.repo] = repo_counts.get(state.repo, 0) + 1
    duplicates = sorted(repo for repo, count in repo_counts.items() if count > 1)

    print(f"Community outreach states: {len(states)}")
    print(f"Processed repos: {len(processed)}")
    print(f"Future queue items: {len(future_queue)}")
    print(f"Contract schema: {OUTREACH_CONTRACT_SCHEMA_VERSION}")
    if duplicates:
        print(f"Duplicate repo states: {', '.join(duplicates)}")
    if CANDIDATES_FILE.exists():
        print(f"Candidates file: {CANDIDATES_FILE}")
    print("")
    for state in sorted(states, key=lambda item: item.repo):
        final_scores = state.scores.get("final", [])
        codex_scores = state.scores.get("codex", [])
        claude_scores = state.scores.get("claude", [])
        print(state.repo)
        print(f"  Stage:    {state.stage}")
        if state.outreach_kind:
            print(f"  Outreach: {state.outreach_kind}")
        print(f"  Round:    {state.round}")
        print(f"  Scores:   codex={codex_scores} claude={claude_scores} final={final_scores}")
        backflow = backflow_placement_from_history(state)
        if backflow:
            print(f"  Backflow: {backflow.get('placement')}/{backflow.get('section_dir')}")
        future_items = future_items_for_repo(state.repo)
        if future_items:
            print(f"  Future:  {len(future_items)} active")
            for item in future_items[:3]:
                print(f"           [{item.get('id')}] {item.get('status', 'queued')} — {item.get('title')}")
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
              python3 tools/community-outreach/outreach_pipeline.py --future-queue
              python3 tools/community-outreach/outreach_pipeline.py --process-future 797e010c2138e6bb9b
              python3 tools/community-outreach/outreach_pipeline.py --prepare-future-review 797e010c2138e6bb9b
              python3 tools/community-outreach/outreach_pipeline.py --review-future 797e010c2138e6bb9b
              python3 tools/community-outreach/outreach_pipeline.py --repo teorth/equational_theories --prepare-state-review
              python3 tools/community-outreach/outreach_pipeline.py --repo teorth/equational_theories --review-state
              python3 tools/community-outreach/outreach_pipeline.py --repo teorth/equational_theories --issue 364 --refresh-state-draft
              python3 tools/community-outreach/outreach_pipeline.py --repo teorth/equational_theories --queue-state-deepening
              python3 tools/community-outreach/outreach_pipeline.py --repo teorth/equational_theories --queue-state-deepening --deepening-kind integral-primary
              python3 tools/community-outreach/outreach_pipeline.py --repo owner/name --issue 38 --register-future-scope
              python3 tools/community-outreach/outreach_pipeline.py --repo owner/name --issue 38 --mark-replied https://github.com/owner/name/issues/38#issuecomment-...
              python3 tools/community-outreach/outreach_pipeline.py --check-artifacts
              python3 tools/community-outreach/outreach_pipeline.py --archive-stale-states
              python3 tools/community-outreach/outreach_pipeline.py --promote tools/community-outreach/targets/x/final.tex theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/appendix/x/main.tex
              python3 tools/community-outreach/outreach_pipeline.py --discover --parallel 2
              python3 tools/community-outreach/outreach_pipeline.py --repo owner/name
              python3 tools/community-outreach/outreach_pipeline.py --repo owner/name --skip-to C
            """
        ),
    )
    parser.add_argument("--discover", action="store_true", help="Run Stage A discovery and process the resulting candidates")
    parser.add_argument("--repo", action="append", default=[], help="Target repository in owner/name form; repeatable")
    parser.add_argument("--issue", action="append", default=[], type=int, help="Issue number per --repo (same order); isolates state/context per issue")
    parser.add_argument("--todo", action="store_true", help="Claim and process next TODO item from TODO.md")
    parser.add_argument("--status", action="store_true", help="Show persisted state")
    parser.add_argument("--future-queue", action="store_true", help="Show deferred scope/deep-research queue")
    parser.add_argument("--process-future", action="append", default=[], metavar="ID", help="Run a queued future-scope Codex research task by id or unique prefix")
    parser.add_argument("--prepare-future-review", action="append", default=[], metavar="ID", help="Prepare a Claude review packet for a future-scope result and mark it awaiting review")
    parser.add_argument("--review-future", action="append", default=[], metavar="ID", help="Run Claude final review for a future-scope result by id or unique prefix")
    parser.add_argument("--prepare-state-review", action="store_true", help="Prepare Claude final review packets for ordinary --repo states")
    parser.add_argument("--review-state", action="store_true", help="Run Claude final review for ordinary --repo states")
    parser.add_argument("--set-state-status", nargs=2, metavar=("STATUS", "NOTE"), help="Set ordinary --repo state status with a note")
    parser.add_argument("--refresh-state-draft", action="store_true", help="Refresh ordinary --repo drafts from deterministic backflow-aware templates")
    parser.add_argument("--queue-state-deepening", action="store_true", help="Queue deep-research continuation tasks for reference-only --repo states")
    parser.add_argument("--deepening-kind", choices=["default", "integral-primary", "non-affine"], default="default", help="Specific deepening task kind for --queue-state-deepening")
    parser.add_argument("--register-future-scope", action="store_true", help="Extract deferred future tasks from the current draft state for --repo targets")
    parser.add_argument("--mark-replied", metavar="URL", help="Mark --repo target state as replied/submitted with an existing GitHub issue comment URL")
    parser.add_argument("--append-future-note", nargs=2, metavar=("ID", "NOTE"), help="Append a note/source update to a future queue item")
    parser.add_argument("--set-future-status", nargs=3, metavar=("ID", "STATUS", "NOTE"), help="Append a future queue note and update item status")
    parser.add_argument("--check-artifacts", action="store_true", help="Fail if outreach runtime artifacts are tracked or staged for addition")
    parser.add_argument("--archive-stale-states", action="store_true", help="Move duplicate/error runtime states into an ignored local archive")
    parser.add_argument("--promote", nargs=2, action="append", metavar=("SRC", "DEST"), help="Copy a reviewed local artifact to an allowed final path and commit it")
    parser.add_argument("--skip-to", choices=["B", "C", "D"], default="", help="Override the starting stage for --repo targets")
    parser.add_argument("--parallel", "-p", type=int, default=1, help="Number of repositories to process in parallel")
    parser.add_argument("--dry-run", action="store_true", help="Do not call external services or submit issues")
    parser.add_argument("--model", default=None, help="Override Codex model")
    parser.add_argument("--no-push", action="store_true", help="Commit final artifacts locally without pushing")
    parser.add_argument("--no-claude-review", action="store_true", help="Skip Claude review stages; use deterministic contract gates only")
    parser.add_argument("--skip-mid-claude", action="store_true", help="Skip mid-pipeline Claude reviews while keeping final Stage C2 review enabled")
    parser.add_argument("--zero-init-final-review", action="store_true", help="Run final Stage C2 as a cold zero-init review instead of context-aware scope review")
    parser.add_argument("--prepare-only", action="store_true", help="Stop after preparing a draft; do not enter interactive Stage D")
    parser.add_argument(
        "--allow-low-score-backflow",
        action="store_true",
        help="Permit paper backflow after max research rounds even when the research score is below the pass gate",
    )
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
    if args.future_queue:
        print_future_queue(args.repo or None)
        return 0
    if args.process_future:
        for future_id in args.process_future:
            result = process_future_item(future_id, model=args.model, dry_run=args.dry_run)
            print(
                "Future research:",
                result.get("future_item_id"),
                result.get("status"),
                result.get("research_route"),
                "contract=" + str(result.get("route_contract_satisfied")),
            )
        return 0
    if args.prepare_future_review:
        for future_id in args.prepare_future_review:
            packet = prepare_future_review_packet(future_id, dry_run=args.dry_run)
            print(f"Future review packet: {_repo_relative(packet)}")
        return 0
    if args.review_future:
        for future_id in args.review_future:
            review = review_future_item(future_id, dry_run=args.dry_run)
            print(
                "Future Claude review:",
                future_id,
                review.get("status"),
                review.get("verdict"),
                "score=" + str(review.get("overall_score")),
            )
        return 0
    if args.append_future_note:
        item_id, note = args.append_future_note
        source_repo = args.repo[0] if args.repo else ""
        added = append_future_queue_note(item_id, note, source_repo=source_repo, dry_run=args.dry_run)
        print(f"Future queue note appended: {1 if added else 0}")
        return 0
    if args.set_future_status:
        item_id, status, note = args.set_future_status
        source_repo = args.repo[0] if args.repo else ""
        added = append_future_queue_note(item_id, note, source_repo=source_repo, status=status, dry_run=args.dry_run)
        print(f"Future queue status updated: {1 if added else 0}")
        return 0
    if args.check_artifacts:
        return 0 if check_artifact_hygiene() else 1
    if args.archive_stale_states:
        moved = archive_stale_states(dry_run=args.dry_run)
        print(f"Archived stale state files: {len(moved)}")
        for path in moved:
            print(f"  {path}")
        return 0
    if args.promote:
        for src, dest in args.promote:
            promoted = promote_artifact(src, dest, dry_run=args.dry_run, push=not args.no_push)
            logger.info("Promoted artifact: %s", _repo_relative(promoted))
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
    # Pair --repo with --issue: if --issue is given, each repo gets an issue number.
    # Issue number is embedded in the repo identifier as "owner/name#123" so that
    # repo_slug() produces "owner_name_123" — isolated state and target dirs per issue.
    issue_map = dict(zip(args.repo, args.issue)) if args.issue else {}
    for repo in args.repo:
        issue_num = issue_map.get(repo)
        if issue_num:
            repos.append(f"{repo}#{issue_num}")
        else:
            repos.append(repo)

    if not repos:
        print("Specify --discover, --repo, or --status.", file=sys.stderr)
        return 1

    for repo in args.repo:
        if not valid_repo_slug(repo):
            print(f"Invalid repo slug: {repo}", file=sys.stderr)
            return 1

    if args.mark_replied:
        if not repos:
            print("--mark-replied requires --repo", file=sys.stderr)
            return 1
        for repo in repos:
            mark_repo_replied(repo, args.mark_replied, dry_run=args.dry_run)
        print(f"Marked replied: {len(repos)}")
        return 0

    if args.prepare_state_review:
        for repo in repos:
            packet = prepare_state_review_packet(repo, dry_run=args.dry_run)
            print(f"State review packet: {_repo_relative(packet)}")
        return 0

    if args.review_state:
        for repo in repos:
            review = review_state_item(repo, dry_run=args.dry_run)
            print(
                "State Claude review:",
                repo,
                review.get("status"),
                review.get("verdict"),
                "score=" + str(review.get("overall_score")),
            )
        return 0

    if args.set_state_status:
        status, note = args.set_state_status
        for repo in repos:
            set_state_status(repo, status, note, dry_run=args.dry_run)
        print(f"State status updated: {len(repos)}")
        return 0

    if args.refresh_state_draft:
        for repo in repos:
            state = refresh_state_draft(repo, dry_run=args.dry_run)
            print(f"Draft refreshed: {state.repo} ({len(state.draft_body)} chars)")
        return 0

    if args.queue_state_deepening:
        for repo in repos:
            item = queue_state_deepening(repo, kind=args.deepening_kind, dry_run=args.dry_run)
            print(f"Deepening queued: {item['id']} {item['title']} queued={item['queued']}")
        return 0

    if args.register_future_scope:
        total = 0
        for repo in repos:
            state = load_state(repo)
            if not state:
                print(f"No state found for {repo}", file=sys.stderr)
                continue
            contract = validate_draft_contract(
                state,
                backflow_placement=backflow_placement_from_history(state),
                dry_run=True,
                fallback_used=False,
            )
            if not contract["approved"]:
                logger.warning("[%s] Future scope not registered; draft contract errors: %s",
                               repo, "; ".join(contract["errors"]))
                continue
            added = record_future_scope_items(state, contract=contract, dry_run=args.dry_run)
            total += added
            logger.info("[%s] Registered future scope items: %d", repo, added)
        print(f"Future scope items registered: {total}")
        return 0

    states = process_repositories(
        repos,
        parallel=args.parallel,
        skip_to=args.skip_to,
        model=args.model,
        dry_run=args.dry_run,
        todo_item=todo_item,
        allow_low_score_backflow=args.allow_low_score_backflow,
        push_final_artifacts=not args.no_push,
        no_claude_review=args.no_claude_review,
        skip_mid_claude=args.skip_mid_claude,
        c2_context_mode="zero_init_review" if args.zero_init_final_review else "context_aware",
    )

    if not args.dry_run and not args.prepare_only:
        for idx, state in enumerate(states):
            if state.stage == "D":
                logger.info("[%d/%d] Entering Stage D for %s", idx + 1, len(states), state.repo)
                states[idx] = complete_repo_interactively(
                    state,
                    model=args.model,
                    dry_run=args.dry_run,
                    no_claude_review=args.no_claude_review,
                    c2_context_mode="zero_init_review" if args.zero_init_final_review else "context_aware",
                )

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
