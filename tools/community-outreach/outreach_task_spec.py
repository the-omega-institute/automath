#!/usr/bin/env python3
"""outreach_task_spec — zero-dependency task record + queue helpers.

A "task" here is a specific operator commitment (e.g. "draft Tolmetes #38 §1
ledger reply", "deliver Israel paper-trade Lean pointers + annotated
questions"), distinct from open-ended T-NN open-problem research that
outreach_research_loop handles.

Each task is one JSON file under outreach_state/task_queue/<task_id>.json.
The task_runner daemon drains the queue, claims via .in_progress markers,
dispatches a typed worker, runs a gate adapter, and on gate-pass writes
deliverables to drafts/ and marks the task `gated_ready` for operator review.

This module is intentionally zero-dep so a bug in higher-level worker /
gate code cannot prevent task_runner from at least listing / loading /
saving tasks.
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

SCRIPT_DIR = Path(__file__).resolve().parent
TASK_QUEUE_DIR = SCRIPT_DIR / "outreach_state" / "task_queue"
TASK_CLAIMS_DIR = SCRIPT_DIR / "outreach_state" / "task_claims"

VALID_TYPES = {
    "issue_reply_draft",
    "email_reply_draft",
    "paper_trade",
    "code_pr_response",
    "experimental",
}

VALID_GATE_KINDS = {
    "claude_review",
    "checklist_files",
    "audit_external",
    "none",
}

VALID_STATUSES = {
    "pending",
    "in_progress",
    "gated_ready",
    "rejected",
    "blocked",  # blocked by external dep (e.g. requires_external_repo) — not workable here
}

DEFAULT_MAX_RETRIES = 3


@dataclass
class GateConfig:
    kind: str = "none"
    # claude_review:
    min_score: int = 8
    rubric_md: str = ""
    rubric_path: str = ""  # alternative to inline
    # checklist_files:
    must_exist: list[str] = field(default_factory=list)
    min_size_bytes: dict[str, int] = field(default_factory=dict)
    must_contain: dict[str, list[str]] = field(default_factory=dict)
    # audit_external:
    gh_repo: str = ""
    gh_pr_or_issue: int = 0
    # generic:
    notes: str = ""

    @classmethod
    def from_dict(cls, d: dict) -> "GateConfig":
        out = cls()
        for k, v in (d or {}).items():
            if hasattr(out, k):
                setattr(out, k, v)
        if out.kind not in VALID_GATE_KINDS:
            out.kind = "none"
        return out


@dataclass
class TaskSpec:
    id: str
    type: str
    title: str
    created_at: str
    deadline_iso: str = ""

    # Free-form context payload the worker can read (varies per task type).
    context: dict = field(default_factory=dict)

    # Where deliverables are expected to land. Worker writes here, gate
    # checklist verifies presence.
    deliverable_paths: list[str] = field(default_factory=list)

    gate: GateConfig = field(default_factory=GateConfig)

    status: str = "pending"
    retries: int = 0
    max_retries: int = DEFAULT_MAX_RETRIES

    # Constraints flagged by the operator for execution gating
    requires_lean: bool = False           # true → skip on Lean-restricted machines
    requires_external_repo: str = ""      # non-empty path/URL → may need worktree elsewhere

    last_run_iso: str = ""
    last_verdict: str = ""
    last_reason: str = ""
    log_paths: list[str] = field(default_factory=list)

    @classmethod
    def from_dict(cls, d: dict) -> "TaskSpec":
        gate_d = d.get("gate") or {}
        spec = cls(
            id=d["id"],
            type=d.get("type", "experimental"),
            title=d.get("title", ""),
            created_at=d.get("created_at", _now_iso()),
            deadline_iso=d.get("deadline_iso", ""),
            context=dict(d.get("context") or {}),
            deliverable_paths=list(d.get("deliverable_paths") or []),
            gate=GateConfig.from_dict(gate_d),
            status=d.get("status", "pending"),
            retries=int(d.get("retries", 0)),
            max_retries=int(d.get("max_retries", DEFAULT_MAX_RETRIES)),
            requires_lean=bool(d.get("requires_lean", False)),
            requires_external_repo=str(d.get("requires_external_repo", "")),
            last_run_iso=str(d.get("last_run_iso", "")),
            last_verdict=str(d.get("last_verdict", "")),
            last_reason=str(d.get("last_reason", "")),
            log_paths=list(d.get("log_paths") or []),
        )
        if spec.type not in VALID_TYPES:
            spec.type = "experimental"
        if spec.status not in VALID_STATUSES:
            spec.status = "pending"
        return spec

    def to_dict(self) -> dict:
        d = asdict(self)
        # asdict serializes nested GateConfig automatically
        return d

    def is_workable_locally(self, *, lean_available: bool, allow_external_repo: bool = False) -> tuple[bool, str]:
        if self.requires_lean and not lean_available:
            return False, "task requires Lean execution; skipping on Lean-restricted machine"
        if self.requires_external_repo and not allow_external_repo:
            return False, f"task requires external repo {self.requires_external_repo!r}; not configured"
        if self.status not in {"pending", "rejected"}:
            return False, f"task status is {self.status!r}, not workable"
        if self.retries >= self.max_retries:
            return False, f"task exhausted retries ({self.retries}/{self.max_retries})"
        return True, ""

    def path(self, queue_dir: Path | None = None) -> Path:
        return (queue_dir or TASK_QUEUE_DIR) / f"{self.id}.json"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def load_task(task_id: str, queue_dir: Path | None = None) -> TaskSpec | None:
    p = (queue_dir or TASK_QUEUE_DIR) / f"{task_id}.json"
    if not p.exists():
        return None
    try:
        return TaskSpec.from_dict(json.loads(p.read_text(encoding="utf-8")))
    except (OSError, json.JSONDecodeError):
        return None


def save_task(task: TaskSpec, queue_dir: Path | None = None) -> Path:
    qd = queue_dir or TASK_QUEUE_DIR
    qd.mkdir(parents=True, exist_ok=True)
    p = qd / f"{task.id}.json"
    tmp = p.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(task.to_dict(), ensure_ascii=False, indent=2), encoding="utf-8")
    tmp.replace(p)
    return p


def list_tasks(queue_dir: Path | None = None) -> list[TaskSpec]:
    qd = queue_dir or TASK_QUEUE_DIR
    if not qd.exists():
        return []
    out: list[TaskSpec] = []
    for p in sorted(qd.glob("*.json")):
        try:
            out.append(TaskSpec.from_dict(json.loads(p.read_text(encoding="utf-8"))))
        except (OSError, json.JSONDecodeError):
            continue
    return out


def select_workable(
    tasks: Iterable[TaskSpec],
    *,
    lean_available: bool = False,
    allow_external_repo: bool = False,
) -> list[TaskSpec]:
    out: list[TaskSpec] = []
    for t in tasks:
        ok, _ = t.is_workable_locally(
            lean_available=lean_available,
            allow_external_repo=allow_external_repo,
        )
        if ok:
            out.append(t)
    # Priority: deadline_iso (earliest first), then created_at (oldest first).
    def _key(t: TaskSpec) -> tuple[str, str]:
        return (t.deadline_iso or "9999-12-31", t.created_at or "9999")
    out.sort(key=_key)
    return out
