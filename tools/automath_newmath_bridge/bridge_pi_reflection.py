#!/usr/bin/env python3
"""Deterministic PI reflection for the NewMath -> Automath bridge.

This layer watches bridge ACK/status and writeback eligibility. It records why
Automath did or did not run Killo/golden writeback and which safe control action
should happen next. It does not edit paper or Lean content directly.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_GATE_RESULTS = SCRIPT_DIR / "out" / "bridge_gate_results.jsonl"
DEFAULT_ACK_STATUS = REPO_ROOT / "docs" / "bridge" / "newmath-bridge-ack-status.md"
DEFAULT_REPORT = REPO_ROOT / "docs" / "bridge" / "automath-newmath-pi-reflection.md"
DEFAULT_ACTIONS = REPO_ROOT / "docs" / "bridge" / "automath-newmath-pi-actions.jsonl"
DEFAULT_DISTILLATION_DIR = REPO_ROOT / "papers" / "publication" / "backflow" / ".distillation"


STATUS_ROW_RE = re.compile(r"^\|\s*`([^`]+)`\s*\|\s*([0-9]+)\s*\|")


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            text = line.strip()
            if not text:
                continue
            try:
                item = json.loads(text)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_no}: invalid JSONL row: {exc}") from exc
            if isinstance(item, dict):
                rows.append(item)
    return rows


def _write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def _ack_status_counts(path: Path) -> dict[str, int]:
    if not path.exists():
        return {}
    counts: dict[str, int] = {}
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        match = STATUS_ROW_RE.match(line.strip())
        if match:
            counts[match.group(1)] = int(match.group(2))
    return counts


def _eligible_writeback(record: dict[str, Any]) -> bool:
    if record.get("bridge_direction") != "newmath_to_automath":
        return False
    if record.get("gate_status") != "gate_passed":
        return False
    if record.get("destination_repo") != "the-omega-institute/automath":
        return False
    if (
        str(record.get("source_artifact_kind") or "") == "paper_claim"
        and record.get("readiness") in {"ready_for_local_packet", "blocked_automath_not_ready"}
        and "concrete_instances/banach/" in str(record.get("source_path") or "").lower()
    ):
        return True
    if record.get("readiness") in {"blocked_automath_not_ready", "observe_only"}:
        return False
    if record.get("operator_review_required") and record.get("status") not in {"accepted", "consumed"}:
        return False
    return True


def _direction_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        row
        for row in rows
        if row.get("bridge_direction") == "newmath_to_automath"
        and row.get("destination_repo") == "the-omega-institute/automath"
    ]


def _blocked_reason(record: dict[str, Any]) -> str:
    if record.get("gate_status") != "gate_passed":
        return str(record.get("gate_status") or "gate_not_passed")
    if record.get("readiness") in {"blocked_automath_not_ready", "observe_only"}:
        return str(record.get("readiness"))
    if record.get("operator_review_required") and record.get("status") not in {"accepted", "consumed"}:
        return "awaiting_operator_acceptance"
    return "not_selected"


def _distill_slug(value: str) -> str:
    lowered = value.strip().lower()
    slug = re.sub(r"[^a-z0-9]+", "_", lowered).strip("_")
    return slug or "distillation_source"


def _candidate_name(record: dict[str, Any]) -> str:
    source_path = str(record.get("source_path") or record.get("artifact_key") or "NewMath bridge")
    stem = Path(source_path).stem.replace("_", " ").replace("-", " ").strip()
    return f"NewMath bridge source: {stem}"


def _review_blocked_sources(eligible: list[dict[str, Any]], distillation_dir: Path) -> list[dict[str, str]]:
    blocked: list[dict[str, str]] = []
    for record in eligible:
        name = _candidate_name(record)
        state_dir = distillation_dir / _distill_slug(name)
        blocked_path = state_dir / "blocked.json"
        state_path = state_dir / "state.json"
        if not blocked_path.exists():
            if not state_path.exists():
                continue
            try:
                state_payload = json.loads(state_path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            failure_kind = str(state_payload.get("failure_kind") or "")
            if failure_kind not in {"distillation_timeout", "bridge_distillation_timeout"}:
                continue
            blocked.append(
                {
                    "source": name,
                    "stage": str(state_payload.get("current_stage") or ""),
                    "status": failure_kind,
                    "source_path": str(record.get("source_path") or ""),
                }
            )
            continue
        try:
            payload = json.loads(blocked_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(payload, dict) and payload.get("status") in {"review_failed", "distillation_timeout"}:
            blocked.append(
                {
                    "source": name,
                    "stage": str(payload.get("stage") or ""),
                    "status": str(payload.get("status") or ""),
                    "source_path": str(record.get("source_path") or ""),
                }
            )
    return blocked


def build_actions(
    gate_rows: list[dict[str, Any]],
    ack_status_counts: dict[str, int],
    *,
    review_backend: str,
    distillation_dir: Path,
) -> list[dict[str, Any]]:
    direction_rows = _direction_rows(gate_rows)
    eligible = [row for row in direction_rows if _eligible_writeback(row)]
    blocked_counts = Counter(_blocked_reason(row) for row in direction_rows if not _eligible_writeback(row))
    review_blocked = _review_blocked_sources(eligible, distillation_dir)
    actions: list[dict[str, Any]] = []

    actions.append(
        {
            "schema_version": "automath-bridge-pi-action-v1",
            "action_id": "pi:automath:killo_golden_codex_fallback",
            "action_type": "writeback_backend_policy",
            "severity": "high",
            "safe_to_apply_automatically": True,
            "automatic_effect": "use_codex_when_claude_unavailable",
            "review_backend": review_backend,
            "policy": (
                "Automath bridge writeback must enter the native Killo/golden "
                "distillation lane. With review_backend=codex-claude, Codex review "
                "is sufficient when Claude is unavailable; do not block waiting for Claude."
            ),
        }
    )

    if eligible:
        actions.append(
            {
                "schema_version": "automath-bridge-pi-action-v1",
                "action_id": "pi:automath:run_killo_golden_writeback",
                "action_type": "run_distillation_writeback",
                "severity": "high",
                "safe_to_apply_automatically": True,
                "automatic_effect": "bridge_supervisor_may_apply_writeback_adapter",
                "eligible_count": len(eligible),
                "source_paths": [str(row.get("source_path") or "") for row in eligible[:12]],
                "policy": "Only accepted/consumed NewMath-to-Automath rows can become Killo/golden distillation source candidates.",
            }
        )
        if review_blocked:
            actions.append(
                {
                    "schema_version": "automath-bridge-pi-action-v1",
                    "action_id": "pi:automath:killo_golden_review_blocked",
                    "action_type": "quality_gate_feedback",
                    "severity": "high",
                    "safe_to_apply_automatically": True,
                    "automatic_effect": "refine_bridge_source_context_and_retry",
                    "blocked_sources": review_blocked[:12],
                    "policy": (
                        "A Killo/golden review or distillation-timeout block is a "
                        "successful gate signal, not an infrastructure failure. Refine "
                        "source labels, receiving sections, scope size, and "
                        "first-distillation prompt before retrying; do not bypass the "
                        "Automath paper review gate."
                    ),
                }
            )
    else:
        actions.append(
            {
                "schema_version": "automath-bridge-pi-action-v1",
                "action_id": "pi:automath:no_eligible_writeback",
                "action_type": "selection_gate_feedback",
                "severity": "medium",
                "safe_to_apply_automatically": True,
                "automatic_effect": "continue_scanning_and_wait_for_accepted_or_consumed_rows",
                "eligible_count": 0,
                "blocked_counts": dict(sorted(blocked_counts.items())),
                "policy": (
                    "Do not fabricate Automath paper writes from observed or blocked "
                    "NewMath evidence. Keep producing receiving indexes and wait for "
                    "operator/BEDC acceptance or a sharper Automath receiving target."
                ),
            }
        )

    if ack_status_counts:
        actions.append(
            {
                "schema_version": "automath-bridge-pi-action-v1",
                "action_id": "pi:automath:consume_newmath_ack_status",
                "action_type": "global_ack_feedback",
                "severity": "info",
                "safe_to_apply_automatically": True,
                "automatic_effect": "use_ack_reasons_to_adjust_next_scan",
                "ack_status_counts": dict(sorted(ack_status_counts.items())),
                "policy": "NewMath ACK/NACK status is feedback for bridge selection and does not approve Automath paper or Lean writeback.",
            }
        )
    return actions


def render_report(
    gate_rows: list[dict[str, Any]],
    ack_status_counts: dict[str, int],
    actions: list[dict[str, Any]],
    *,
    distillation_dir: Path,
) -> str:
    direction_rows = _direction_rows(gate_rows)
    eligible = [row for row in direction_rows if _eligible_writeback(row)]
    blocked_counts = Counter(_blocked_reason(row) for row in direction_rows if not _eligible_writeback(row))
    review_blocked = _review_blocked_sources(eligible, distillation_dir)
    lines = [
        "# Automath-NewMath PI Reflection",
        "",
        "This report is the deterministic PI layer for the NewMath-to-Automath bridge.",
        "It turns global bridge and ACK signals into disciplined Killo/golden writeback control actions.",
        "It does not write Automath paper or Lean content directly.",
        "",
        "## Current Signal",
        "",
        f"- NewMath-to-Automath gate rows: `{len(direction_rows)}`",
        f"- Killo/golden writeback-eligible rows: `{len(eligible)}`",
        f"- Killo/golden review-blocked bridge sources: `{len(review_blocked)}`",
        f"- PI actions: `{len(actions)}`",
        "",
        "## Blocked Counts",
        "",
        "| Reason | Count |",
        "| --- | ---: |",
    ]
    if blocked_counts:
        for reason, count in sorted(blocked_counts.items()):
            lines.append(f"| `{reason}` | {count} |")
    else:
        lines.append("| _none_ | 0 |")
    lines.extend(["", "## NewMath ACK Status Counts", "", "| Status | Count |", "| --- | ---: |"])
    if ack_status_counts:
        for status, count in sorted(ack_status_counts.items()):
            lines.append(f"| `{status}` | {count} |")
    else:
        lines.append("| _none_ | 0 |")
    lines.extend(["", "## Killo/Golden Review Blocks", "", "| Source | Source Path |", "| --- | --- |"])
    if review_blocked:
        for item in review_blocked:
            lines.append(f"| `{item['source']}` | `{item['source_path']}` |")
    else:
        lines.append("| _none_ | _none_ |")
    lines.extend(["", "## PI Actions", "", "| Action | Effect | Severity |", "| --- | --- | --- |"])
    for action in actions:
        lines.append(
            "| `{}` | `{}` | `{}` |".format(
                action.get("action_id", ""),
                action.get("automatic_effect", ""),
                action.get("severity", ""),
            )
        )
    lines.extend(
        [
            "",
            "## Control Policy",
            "",
            "- Automath writeback is allowed only through the native Killo/golden distillation lane.",
            "- Claude unavailability is not a blocker when `review_backend=codex-claude`; Codex fallback remains within the same review prompts.",
            "- Runtime candidate packets stay under `tools/automath_newmath_bridge/inbox/` and are not committed.",
            "- Durable PI reports, ACK status, and receiving indexes are commit-worthy bridge telemetry.",
            "",
        ]
    )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run deterministic Automath bridge PI reflection")
    parser.add_argument("--gate-results", default=str(DEFAULT_GATE_RESULTS))
    parser.add_argument("--ack-status", default=str(DEFAULT_ACK_STATUS))
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--actions", default=str(DEFAULT_ACTIONS))
    parser.add_argument("--distillation-dir", default=str(DEFAULT_DISTILLATION_DIR))
    parser.add_argument("--review-backend", default="codex-claude")
    args = parser.parse_args(argv)

    gate_rows = _read_jsonl(Path(args.gate_results))
    ack_counts = _ack_status_counts(Path(args.ack_status))
    distillation_dir = Path(args.distillation_dir)
    actions = build_actions(
        gate_rows,
        ack_counts,
        review_backend=args.review_backend,
        distillation_dir=distillation_dir,
    )

    _write_jsonl(Path(args.actions), actions)
    report_path = Path(args.report)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(
        render_report(gate_rows, ack_counts, actions, distillation_dir=distillation_dir),
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "gate_rows": len(gate_rows),
                "actions": len(actions),
                "ack_status_counts": ack_counts,
                "report": str(report_path),
                "actions_path": str(Path(args.actions)),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
