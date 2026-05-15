#!/usr/bin/env python3
"""outreach_gates — gate adapters for outreach_task_runner.

A gate is the structured ready-to-deliver criterion attached to a TaskSpec.
The task_runner invokes evaluate(task) AFTER the worker has finished; the
gate decides whether the deliverable can be marked `gated_ready` for
operator review or needs another retry / escalation.

Gate kinds:

  - claude_review     :: legacy alias for `none` in the normal task runner.
                         Claude review is reserved for the explicit writeback
                         stage; normal drafts are gated deterministically and
                         by operator review.
  - checklist_files   :: pure-disk verification (paper_trade / multi_artifact).
                         Each path in `gate.must_exist` (or `deliverable_paths`)
                         must exist + meet `min_size_bytes` + `must_contain`
                         substring tests.
  - audit_external    :: gh PR / issue comment audit (code_pr_response). Pulls
                         comments via `gh api`, checks at least one matches the
                         operator's reply commitments. Returns BLOCKED status
                         if external_repo is not checked out locally.
  - none              :: auto-pass (operator gate by hand).

Zero deps on the rest of the outreach pipeline beyond outreach_task_spec.
"""

from __future__ import annotations

import json
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]

from outreach_task_spec import TaskSpec


@dataclass
class GateVerdict:
    passed: bool
    score: int | None = None
    reasons: list[str] = field(default_factory=list)
    next_action: str = "retry"  # "ready_for_user" | "retry" | "escalate" | "blocked"


# ---------------------------------------------------------------------------
# claude_review
# ---------------------------------------------------------------------------


def _evaluate_claude_review(task: TaskSpec) -> GateVerdict:
    return GateVerdict(
        passed=True,
        score=None,
        reasons=["claude_review disabled in task runner; operator/writeback review is the gate"],
        next_action="ready_for_user",
    )


def _extract_json(text: str) -> dict | None:
    text = (text or "").strip()
    if not text:
        return None
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, re.DOTALL)
    candidate = fence.group(1) if fence else None
    if candidate is None:
        first = text.find("{")
        last = text.rfind("}")
        if first == -1 or last == -1 or last <= first:
            return None
        candidate = text[first : last + 1]
    try:
        return json.loads(candidate)
    except json.JSONDecodeError:
        return None


# ---------------------------------------------------------------------------
# checklist_files
# ---------------------------------------------------------------------------


def _evaluate_checklist_files(task: TaskSpec) -> GateVerdict:
    paths = task.gate.must_exist or task.deliverable_paths
    if not paths:
        return GateVerdict(passed=False, reasons=["no deliverable paths"], next_action="escalate")

    reasons: list[str] = []
    failures = 0

    for rel in paths:
        p = Path(rel)
        if not p.is_absolute():
            p = REPO_ROOT / p
        if not p.exists():
            reasons.append(f"missing: {rel}")
            failures += 1
            continue
        try:
            sz = p.stat().st_size
        except OSError as exc:
            reasons.append(f"stat failed on {rel}: {exc}")
            failures += 1
            continue
        min_sz = task.gate.min_size_bytes.get(rel, 0)
        if sz < min_sz:
            reasons.append(f"undersize: {rel} ({sz} bytes < {min_sz} required)")
            failures += 1
            continue
        # must_contain checks (text only — skip binaries by best-effort check)
        terms = task.gate.must_contain.get(rel) or []
        if terms:
            try:
                content = p.read_text(encoding="utf-8", errors="ignore")
            except Exception as exc:
                reasons.append(f"read failed on {rel}: {exc}")
                failures += 1
                continue
            for t in terms:
                if t.lower() not in content.lower():
                    reasons.append(f"{rel} missing required substring: {t!r}")
                    failures += 1

    passed = failures == 0
    if passed:
        reasons = reasons or [f"all {len(paths)} deliverables present + meet thresholds"]
    return GateVerdict(
        passed=passed,
        score=10 if passed else max(0, 10 - failures),
        reasons=reasons[:10],
        next_action="ready_for_user" if passed else "retry",
    )


# ---------------------------------------------------------------------------
# audit_external (gh PR / issue comment audit)
# ---------------------------------------------------------------------------


def _evaluate_audit_external(task: TaskSpec) -> GateVerdict:
    repo = task.gate.gh_repo
    n = task.gate.gh_pr_or_issue
    if not repo or not n:
        return GateVerdict(
            passed=False,
            reasons=["gate.gh_repo or gate.gh_pr_or_issue not configured"],
            next_action="escalate",
        )
    if task.requires_external_repo and not (REPO_ROOT.parent / "_outreach_external" / repo.replace("/", "_")).exists():
        return GateVerdict(
            passed=False,
            reasons=[f"external repo {repo} not checked out locally; cannot land code from this host"],
            next_action="blocked",
        )
    # Best-effort comment count check — verify we replied AND no fresh changes-requested review exists.
    try:
        cp = subprocess.run(
            ["gh", "pr", "view", str(n), "--repo", repo, "--json", "reviewDecision,comments,latestReviews"],
            capture_output=True, text=True, timeout=20,
        )
    except Exception as exc:
        return GateVerdict(
            passed=False,
            reasons=[f"gh pr view failed: {exc}"],
            next_action="retry",
        )
    if cp.returncode != 0:
        return GateVerdict(
            passed=False,
            reasons=[f"gh pr view rc={cp.returncode}: {cp.stderr.strip()[:200]}"],
            next_action="retry",
        )
    try:
        info = json.loads(cp.stdout)
    except json.JSONDecodeError as exc:
        return GateVerdict(
            passed=False,
            reasons=[f"gh pr view returned non-JSON: {exc}"],
            next_action="retry",
        )
    decision = (info.get("reviewDecision") or "").upper()
    passed = decision in {"APPROVED", "REVIEW_REQUIRED"} and decision != "CHANGES_REQUESTED"
    return GateVerdict(
        passed=passed,
        score=10 if passed else 0,
        reasons=[f"gh reviewDecision={decision!r}"],
        next_action="ready_for_user" if passed else "retry",
    )


# ---------------------------------------------------------------------------
# none
# ---------------------------------------------------------------------------


def _evaluate_none(task: TaskSpec) -> GateVerdict:
    return GateVerdict(
        passed=True,
        score=None,
        reasons=["gate.kind=none — auto-pass; operator review is the gate"],
        next_action="ready_for_user",
    )


# ---------------------------------------------------------------------------
# dispatcher
# ---------------------------------------------------------------------------


_DISPATCH = {
    "claude_review": _evaluate_claude_review,
    "checklist_files": _evaluate_checklist_files,
    "audit_external": _evaluate_audit_external,
    "none": _evaluate_none,
}


def evaluate(task: TaskSpec) -> GateVerdict:
    fn = _DISPATCH.get(task.gate.kind, _evaluate_none)
    try:
        return fn(task)
    except Exception as exc:
        return GateVerdict(
            passed=False,
            reasons=[f"gate evaluator raised: {type(exc).__name__}: {exc}"],
            next_action="escalate",
        )
