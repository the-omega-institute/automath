#!/usr/bin/env python3
"""Validate Automath-NewMath bridge manifest JSONL records."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent

ARTIFACT_KINDS = {
    "proposal",
    "accepted_proposal",
    "paper_seed_stub",
    "taste_gate_witness",
    "lean_theorem",
    "paper_claim",
    "open_problem_target",
    "scope_ledger",
    "review_packet",
    "writeback_packet",
    "publication_slug",
    "pipeline_status",
    "audit_failure",
    "candidate_mechanism",
}
DIRECTIONS = {"newmath_to_automath", "automath_to_newmath", "bidirectional"}
STATUSES = {"observed", "candidate", "accepted", "consumed", "blocked", "needs_operator_review"}
REPOS = {"the-omega-institute/automath", "the-omega-institute/newmath"}
RISKS = {"none", "low", "medium", "high"}
SHA_RE = re.compile(r"^[0-9a-f]{7,40}$")
ID_RE = re.compile(r"^[a-z0-9][a-z0-9._:-]*$")
ISO_RE = re.compile(r"^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$")

REQUIRED = {
    "id",
    "record_version",
    "created_at",
    "source_repo",
    "source_branch_or_ref",
    "source_path",
    "source_commit",
    "source_artifact_kind",
    "destination_repo",
    "destination_branch_or_ref",
    "destination_path",
    "destination_artifact_kind",
    "bridge_direction",
    "status",
    "operator_review_required",
    "taste_gate_required",
    "audit_required",
    "external_publication_risk",
    "notes",
    "next_action",
}


def _read_jsonl(path: Path) -> list[tuple[int, dict[str, Any]]]:
    records: list[tuple[int, dict[str, Any]]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, 1):
            stripped = line.strip()
            if not stripped:
                continue
            try:
                data = json.loads(stripped)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_no}: invalid JSON: {exc}") from exc
            if not isinstance(data, dict):
                raise ValueError(f"{path}:{line_no}: expected JSON object")
            records.append((line_no, data))
    return records


def _bad_path(value: str) -> bool:
    return (
        not value
        or value.startswith("/")
        or "\\" in value
        or "\x00" in value
        or any(part in {"", ".", ".."} for part in value.split("/"))
    )


def validate_record(record: dict[str, Any]) -> list[str]:
    issues: list[str] = []
    missing = sorted(REQUIRED - set(record))
    for key in missing:
        issues.append(f"missing required field: {key}")
    if missing:
        return issues

    if not isinstance(record.get("record_version"), int) or record["record_version"] < 1:
        issues.append("record_version must be an integer >= 1")
    if not isinstance(record.get("id"), str) or not ID_RE.match(record["id"]):
        issues.append("id must match ^[a-z0-9][a-z0-9._:-]*$")
    if not isinstance(record.get("created_at"), str) or not ISO_RE.match(record["created_at"]):
        issues.append("created_at must be UTC ISO format YYYY-MM-DDTHH:MM:SSZ")
    if "updated_at" in record and (not isinstance(record["updated_at"], str) or not ISO_RE.match(record["updated_at"])):
        issues.append("updated_at must be UTC ISO format YYYY-MM-DDTHH:MM:SSZ")

    if record.get("source_repo") not in REPOS:
        issues.append("source_repo must be one of the bridge repositories")
    if record.get("destination_repo") not in REPOS:
        issues.append("destination_repo must be one of the bridge repositories")
    if record.get("source_repo") == record.get("destination_repo"):
        issues.append("source_repo and destination_repo must differ for a bridge record")

    if _bad_path(str(record.get("source_path", ""))):
        issues.append("source_path must be a safe relative path")
    if _bad_path(str(record.get("destination_path", ""))):
        issues.append("destination_path must be a safe relative path")
    if not SHA_RE.match(str(record.get("source_commit", ""))):
        issues.append("source_commit must be a 7-40 character hex git commit")

    if record.get("source_artifact_kind") not in ARTIFACT_KINDS:
        issues.append("source_artifact_kind is not recognized")
    if record.get("destination_artifact_kind") not in ARTIFACT_KINDS:
        issues.append("destination_artifact_kind is not recognized")
    if record.get("bridge_direction") not in DIRECTIONS:
        issues.append("bridge_direction is not recognized")
    if record.get("status") not in STATUSES:
        issues.append("status is not recognized")
    if record.get("external_publication_risk") not in RISKS:
        issues.append("external_publication_risk is not recognized")

    for key in ("operator_review_required", "taste_gate_required", "audit_required"):
        if not isinstance(record.get(key), bool):
            issues.append(f"{key} must be boolean")
    for key in ("source_branch_or_ref", "destination_branch_or_ref", "notes", "next_action"):
        if not isinstance(record.get(key), str) or not record[key].strip():
            issues.append(f"{key} must be a nonempty string")

    direction = record.get("bridge_direction")
    if direction == "newmath_to_automath":
        if record.get("source_repo") != "the-omega-institute/newmath":
            issues.append("newmath_to_automath requires NewMath as source")
        if record.get("destination_repo") != "the-omega-institute/automath":
            issues.append("newmath_to_automath requires Automath as destination")
    if direction == "automath_to_newmath":
        if record.get("source_repo") != "the-omega-institute/automath":
            issues.append("automath_to_newmath requires Automath as source")
        if record.get("destination_repo") != "the-omega-institute/newmath":
            issues.append("automath_to_newmath requires NewMath as destination")

    if record.get("status") in {"accepted", "consumed"} and record.get("operator_review_required") is not True:
        issues.append("accepted/consumed records must keep operator_review_required=true")
    if record.get("taste_gate_required") and "taste" not in (
        str(record.get("notes", "")) + " " + str(record.get("audit_boundary", ""))
    ).lower():
        issues.append("taste_gate_required=true should name the TasteGate boundary in notes or audit_boundary")
    return issues


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate bridge manifest JSONL")
    parser.add_argument("manifest", help="manifest or generated packet JSONL")
    parser.add_argument("--allow-empty", action="store_true", help="allow zero records")
    args = parser.parse_args(argv)

    path = Path(args.manifest)
    try:
        records = _read_jsonl(path)
    except Exception as exc:
        print(f"[bridge-validate] {exc}", file=sys.stderr)
        return 1

    if not records and not args.allow_empty:
        print(f"[bridge-validate] {path}: no records", file=sys.stderr)
        return 1

    issue_count = 0
    seen_ids: set[str] = set()
    for line_no, record in records:
        if record.get("id") in seen_ids:
            print(f"{path}:{line_no}: duplicate id: {record.get('id')}", file=sys.stderr)
            issue_count += 1
        seen_ids.add(str(record.get("id")))
        issues = validate_record(record)
        for issue in issues:
            print(f"{path}:{line_no}: {issue}", file=sys.stderr)
            issue_count += 1

    if issue_count:
        print(f"[bridge-validate] failed: {issue_count} issue(s)", file=sys.stderr)
        return 1
    print(f"[bridge-validate] ok: {len(records)} record(s) in {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
