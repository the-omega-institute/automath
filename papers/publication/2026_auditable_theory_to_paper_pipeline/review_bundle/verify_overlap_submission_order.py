#!/usr/bin/env python3
"""Verify the deterministic overlap/submission-order finite record.

This is a record-level check. It verifies that the current package ledger keeps
the CICM presentation route as one route and that the current audit record does
not promote a duplicated sibling submission. It does not inspect external
submission systems or decide mathematical novelty.
"""
from __future__ import annotations

import hashlib
import json
import platform
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load_json(relative: str) -> dict:
    path = ROOT / relative
    try:
        return json.loads(path.read_text(encoding="utf-8-sig"))
    except FileNotFoundError as exc:
        raise SystemExit(f"missing required file: {relative}") from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(f"invalid JSON in {relative}: {exc}") from exc


def sha256(relative: str) -> str:
    digest = hashlib.sha256()
    with (ROOT / relative).open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git_head() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except Exception:
        return "unavailable"


def main() -> int:
    errors: list[str] = []
    records = load_json("review_bundle/current_package_pass_records.json")
    audit = load_json("stage_a_audit.json")

    entries = records.get("entries", [])
    route_entries = [
        entry for entry in entries
        if "route" in entry.get("claim_kind_set", [])
    ]
    if not route_entries:
        errors.append("no route entry found in current_package_pass_records.json")

    overlap_rows = []
    for entry in route_entries:
        for row in entry.get("pass_records", []):
            if row.get("gate_name") == "overlap":
                overlap_rows.append(row)

    if not overlap_rows:
        errors.append("no overlap gate row found for route entries")

    accepted_decisions = {"pass", "bounded-pass"}
    for row in overlap_rows:
        if row.get("decision") not in accepted_decisions:
            errors.append(f"overlap gate did not pass: {row}")
        pointer = str(row.get("evidence_pointer", ""))
        if not pointer:
            errors.append("overlap gate row has no evidence pointer")

    closure = audit.get("stage_a_closure_record", {})
    if closure.get("accepted_route") != "canonical finite antichain and obstruction-basis audit calculus":
        errors.append("audit closure route does not name the antichain-basis route")
    if audit.get("verdict") != "proceed":
        errors.append("stage_a_audit.json verdict is not proceed")

    summary = {
        "command": "python review_bundle/verify_overlap_submission_order.py",
        "source_commit": git_head(),
        "source_hashes": {
            "review_bundle/current_package_pass_records.json": sha256("review_bundle/current_package_pass_records.json"),
            "stage_a_audit.json": sha256("stage_a_audit.json"),
        },
        "source_digest_manifest": "review_bundle/FINAL_DIGESTS_SHA256.md",
        "environment": f"Python {platform.python_version()} on {platform.system()} {platform.release()}",
        "route_entry_count": len(route_entries),
        "overlap_gate_count": len(overlap_rows),
        "accepted_route": closure.get("accepted_route"),
        "errors": errors,
        "exit_code": 1 if errors else 0,
        "log_path": "review_bundle/overlap_submission_order_verification_run.log",
        "boundary": "finite route/overlap record check only; no external submission-system query and no novelty judgment",
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
