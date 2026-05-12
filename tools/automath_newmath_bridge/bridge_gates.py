#!/usr/bin/env python3
"""Deterministic gates for Automath-NewMath bridge candidates.

These gates decide whether a discovered record is safe to turn into a local
writeback packet for operator review. They do not approve durable destination
writes. Paper, Lean, docs, publication, and external-send effects remain
blocked until a human records an accepted or consumed manifest entry.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

try:
    from validate_bridge_manifest import validate_record
except ModuleNotFoundError:  # pragma: no cover
    from tools.automath_newmath_bridge.validate_bridge_manifest import validate_record


SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_INPUT = SCRIPT_DIR / "inbox" / "bridge_inbox.jsonl"
DEFAULT_OUTPUT = SCRIPT_DIR / "out" / "bridge_gate_results.jsonl"

DURABLE_WRITE_PREFIXES = (
    "lean4/",
    "papers/",
    "theory/",
    "docs/dossier/",
    "tools/community-outreach/outreach_state/",
)

RUNTIME_PATH_MARKERS = (
    "tools/automath_newmath_bridge/inbox/",
    "tools/automath_newmath_bridge/out/",
    "tools/automath_newmath_bridge/state/",
    "tools/automath_newmath_bridge/logs/",
    "tools/bedc-deep/state/",
)


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    if not path.exists():
        return records
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, 1):
            stripped = line.strip()
            if not stripped:
                continue
            data = json.loads(stripped)
            if not isinstance(data, dict):
                raise ValueError(f"{path}:{line_no}: expected object")
            records.append(data)
    return records


def write_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def _is_durable_write_path(path: str) -> bool:
    return any(path.startswith(prefix) for prefix in DURABLE_WRITE_PREFIXES)


def _is_runtime_path(path: str) -> bool:
    return any(path.startswith(prefix) for prefix in RUNTIME_PATH_MARKERS)


def _is_allowed_runtime_destination(path: str) -> bool:
    return path.startswith("tools/automath_newmath_bridge/inbox/")


def gate_record(record: dict[str, Any], *, allow_publication_risk: bool = False) -> dict[str, Any]:
    issues = validate_record(record)
    warnings: list[str] = []
    passed = not issues

    source_kind = str(record.get("source_artifact_kind") or "")
    destination_path = str(record.get("destination_path") or "")
    source_path = str(record.get("source_path") or "")
    publication_risk = str(record.get("external_publication_risk") or "none")
    synthesis = record.get("synthesis") if isinstance(record.get("synthesis"), dict) else {}
    readiness = str(synthesis.get("readiness") or "")
    if not readiness:
        readiness = "needs_operator_review" if record.get("status") == "candidate" else "observe_only"

    durable_write_allowed = False
    packet_write_allowed = False

    if record.get("status") in {"accepted", "consumed"}:
        warnings.append("record already marks accepted/consumed; durable meaning must be checked against commit history")

    if _is_durable_write_path(destination_path):
        issues.append(
            "destination_path points at durable paper/Lean/docs/outreach state; bridge may only write a local review packet automatically"
        )
        passed = False

    if _is_runtime_path(source_path) or (_is_runtime_path(destination_path) and not _is_allowed_runtime_destination(destination_path)):
        issues.append("bridge record points at runtime inbox/out/state/log path; runtime artifacts must not be committed or consumed as durable source")
        passed = False

    if publication_risk in {"medium", "high"} and not allow_publication_risk:
        warnings.append("publication-risk record requires explicit operator approval before any public-facing use")

    if readiness == "observe_only":
        warnings.append("synthesis is observe_only; local packet is suppressed until readiness changes")

    if readiness.startswith("blocked"):
        warnings.append(f"synthesis readiness is {readiness}; local packet is review-only and durable write remains blocked")

    if record.get("taste_gate_required") and "taste" not in (
        str(record.get("notes", "")) + " " + str(record.get("audit_boundary", ""))
    ).lower():
        issues.append("TasteGate-required record does not name the TasteGate boundary")
        passed = False

    if source_kind == "lean_theorem" and not str(record.get("source_path", "")).endswith(".lean"):
        issues.append("lean_theorem source must point to a .lean file")
        passed = False

    if source_kind == "writeback_packet" and record.get("destination_artifact_kind") not in {
        "candidate_mechanism",
        "review_packet",
        "scope_ledger",
    }:
        issues.append("writeback_packet may only auto-produce a review/candidate packet")
        passed = False

    if passed:
        packet_write_allowed = readiness != "observe_only"
        durable_write_allowed = (
            not bool(record.get("operator_review_required"))
            and not bool(record.get("taste_gate_required"))
            and publication_risk in {"none", "low"}
            and readiness == "ready_for_durable_write"
        )

    gate_status = "gate_passed" if passed else "gate_blocked"
    return {
        "id": record.get("id"),
        "artifact_key": record.get("artifact_key", ""),
        "source_repo": record.get("source_repo"),
        "source_branch_or_ref": record.get("source_branch_or_ref"),
        "source_path": record.get("source_path"),
        "source_commit": record.get("source_commit"),
        "destination_repo": record.get("destination_repo"),
        "destination_branch_or_ref": record.get("destination_branch_or_ref"),
        "destination_path": record.get("destination_path"),
        "bridge_direction": record.get("bridge_direction"),
        "source_artifact_kind": record.get("source_artifact_kind"),
        "destination_artifact_kind": record.get("destination_artifact_kind"),
        "priority": int(record.get("priority", 0) or 0),
        "change_kind": record.get("change_kind", ""),
        "gate_status": gate_status,
        "readiness": readiness,
        "readiness_confidence": synthesis.get("readiness_confidence", ""),
        "packet_write_allowed": packet_write_allowed,
        "durable_write_allowed": durable_write_allowed,
        "operator_review_required": record.get("operator_review_required"),
        "taste_gate_required": record.get("taste_gate_required"),
        "audit_required": record.get("audit_required"),
        "external_publication_risk": publication_risk,
        "issues": issues,
        "warnings": warnings,
        "required_gates": synthesis.get("required_gates", []),
        "why_not_writeback_yet": synthesis.get("why_not_writeback_yet", ""),
        "evidence_summary": synthesis.get("evidence_summary", []),
        "next_action": (
            "write local review packet for operator decision"
            if packet_write_allowed
            else "fix gate issues before any bridge packet is written"
        ),
    }


def gate_records(records: list[dict[str, Any]], *, allow_publication_risk: bool = False) -> list[dict[str, Any]]:
    results = [gate_record(record, allow_publication_risk=allow_publication_risk) for record in records]
    results.sort(
        key=lambda item: (
            0 if item["gate_status"] == "gate_passed" else 1,
            -int(item.get("priority", 0) or 0),
            str(item.get("source_path", "")),
        )
    )
    return results


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run deterministic bridge gates")
    parser.add_argument("input", nargs="?", default=str(DEFAULT_INPUT), help="bridge inbox JSONL")
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT), help="gate result JSONL")
    parser.add_argument(
        "--allow-publication-risk",
        action="store_true",
        help="Do not warn on medium/high publication-risk records",
    )
    args = parser.parse_args(argv)

    try:
        records = read_jsonl(Path(args.input))
        results = gate_records(records, allow_publication_risk=args.allow_publication_risk)
        write_jsonl(Path(args.output), results)
    except Exception as exc:
        print(f"[bridge-gates] error: {exc}", file=sys.stderr)
        return 1

    passed = sum(1 for item in results if item.get("gate_status") == "gate_passed")
    blocked = len(results) - passed
    print(f"[bridge-gates] wrote {len(results)} result(s) to {args.output}; passed={passed} blocked={blocked}")
    return 0 if blocked == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
