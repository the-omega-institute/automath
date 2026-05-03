#!/usr/bin/env python3
"""Lifecycle classification for the Omega distillation pipeline.

The distillation runner already knows which stage should run next.  This
module adds a small, explicit failure taxonomy for unattended supervisors:
what happened, whether retrying is reasonable, and what a supervisor should do
without guessing from free-form log text.
"""

from __future__ import annotations

from typing import Any


FAILURE_KINDS: dict[str, dict[str, Any]] = {
    "none": {
        "retry_budget": 0,
        "next_action": "complete",
    },
    "incomplete": {
        "retry_budget": 0,
        "next_action": "run_pipeline",
    },
    "semantic_scan_empty": {
        "retry_budget": 1,
        "next_action": "retry_resume",
    },
    "payload_schema": {
        "retry_budget": 2,
        "next_action": "retry_resume",
    },
    "writeback_review_failed": {
        "retry_budget": 2,
        "next_action": "retry_resume",
    },
    "writeback_application_failed": {
        "retry_budget": 1,
        "next_action": "retry_resume",
    },
    "oracle_unavailable": {
        "retry_budget": 5,
        "next_action": "retry_resume",
    },
    "oracle_claim_timeout": {
        "retry_budget": 5,
        "next_action": "retry_resume",
    },
    "oracle_agent_stale": {
        "retry_budget": 5,
        "next_action": "retry_resume",
    },
    "oracle_timeout": {
        "retry_budget": 3,
        "next_action": "retry_resume",
    },
    "policy_blocked": {
        "retry_budget": 0,
        "next_action": "alert_user",
        "needs_user_intervention": True,
    },
    "done_contract_failed": {
        "retry_budget": 1,
        "next_action": "retry_resume",
    },
    "unknown": {
        "retry_budget": 1,
        "next_action": "retry_resume",
        "needs_user_intervention": True,
    },
}


def _text_contains_any(text: str, needles: tuple[str, ...]) -> bool:
    lowered = text.lower()
    return any(needle in lowered for needle in needles)


def _blocked_kind(blocked: dict[str, Any], action: dict[str, Any]) -> str:
    gate = str(action.get("gate") or blocked.get("gate") or "").lower()
    reason = str(action.get("reason") or blocked.get("reason") or "").lower()
    status = str(blocked.get("status") or "").lower()
    stage = str(blocked.get("stage") or action.get("stage") or "").upper()

    if gate == "semantic_scan_relevance":
        return "semantic_scan_empty"
    if gate == "payload_schema":
        return "payload_schema"
    if stage == "W" and status == "review_failed":
        return "writeback_review_failed"
    if gate == "writeback_review":
        return "writeback_review_failed"
    if _text_contains_any(reason, ("application plan", "line limit", "pipeline metadata")):
        return "writeback_application_failed"
    return "policy_blocked"


def _oracle_kind(oracle_status: dict[str, Any]) -> str:
    if not oracle_status:
        return ""
    reason = str(oracle_status.get("reason") or oracle_status.get("status") or "").lower()
    if "claim_timeout" in reason or "not claimed" in reason:
        return "oracle_claim_timeout"
    if "stale" in reason:
        return "oracle_agent_stale"
    if "timeout" in reason:
        return "oracle_timeout"
    if "unreachable" in reason or "submit failed" in reason or "server" in reason:
        return "oracle_unavailable"
    return ""


def derive_failure_kind(snapshot: dict[str, Any]) -> str:
    """Classify a distillation state snapshot into a stable failure kind."""
    done_contract = snapshot.get("done_contract") or {}
    if done_contract.get("passed"):
        return "none"

    oracle_kind = _oracle_kind(snapshot.get("oracle_status") or {})
    if oracle_kind:
        return oracle_kind

    action = snapshot.get("next_policy_action") or {}
    action_kind = str(action.get("action") or "").lower()
    blocked = snapshot.get("blocked") or {}
    if action_kind == "blocked" or blocked:
        return _blocked_kind(blocked, action)

    inventory = snapshot.get("inventory") or {}
    artifacts = inventory.get("artifacts") or {}
    if inventory.get("payload_error_count", 0):
        return "payload_schema"

    writeback_status = str(inventory.get("writeback_status") or "").lower()
    if writeback_status == "rejected":
        return "writeback_application_failed"
    if writeback_status == "skipped":
        return "writeback_review_failed"

    current_stage = str(snapshot.get("current_stage") or "")
    if current_stage == "DONE" and not done_contract.get("passed"):
        return "done_contract_failed"

    if artifacts and not all(artifacts.get(key) for key in ("raw_research", "section_matches", "generated_payload")):
        return "incomplete"
    if action_kind in {"run_stage", "done"}:
        return "incomplete"
    return "unknown"


def annotate(snapshot: dict[str, Any], attempts: int | None = None) -> dict[str, Any]:
    """Return lifecycle metadata for a state snapshot."""
    kind = derive_failure_kind(snapshot)
    meta = FAILURE_KINDS.get(kind, FAILURE_KINDS["unknown"])
    attempt_count = max(1, int(attempts if attempts is not None else snapshot.get("attempts") or 1))
    next_action = str(meta.get("next_action", "retry_resume"))
    if attempt_count > int(meta.get("retry_budget", 0)) and next_action == "retry_resume":
        next_action = "alert_user"
    return {
        "failure_kind": kind,
        "attempts": attempt_count,
        "retry_budget": int(meta.get("retry_budget", 0)),
        "next_action": next_action,
        "needs_user_intervention": bool(
            meta.get("needs_user_intervention") or next_action == "alert_user"
        ),
        "covered_by_existing_content": bool(meta.get("covered_by_existing_content", False)),
    }


def should_run_pipeline(lifecycle: dict[str, Any]) -> bool:
    """Return whether a supervisor should try running this source."""
    return str(lifecycle.get("next_action") or "") in {"run_pipeline", "retry_resume"}
