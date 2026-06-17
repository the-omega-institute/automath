#!/usr/bin/env python3
"""Reconstruct the four bounded case-study rows from submitted data.

This is a deterministic reviewer-facing replay check.  It reads the submitted
review-bundle manifest, verifies that every named snapshot path exists in the
submitted bundle, reconstructs the four table rows at the historical
path-verified evidence level, and compares the result with the submitted
expected-output JSON.  It does not rerun the original workflow daemons or
artifact validators.
"""
from __future__ import annotations

import json
import platform
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "review_bundle" / "REVIEW_BUNDLE_MANIFEST.json"
EXPECTED = ROOT / "certificates" / "case_rows_expected.json"

CASE_COMPILER: dict[str, dict[str, str]] = {
    "Newmath intake isolation": {
        "gate_and_witness_surface": "promotion gate; intake seed and active-paper detector",
        "observed_issue_and_decision": "active-paper invariant failed until human promotion creates 2026_*, main.tex, and PIPELINE.md; detector blocks daemon entry",
        "safe_lesson_at_bounded_evidence_level": "candidate source packets can remain inactive; path-verified only",
    },
    "Upper-fibers overlap block": {
        "gate_and_witness_surface": "overlap/submission gate; route identity, submitted sibling, overlap ledger, board state",
        "observed_issue_and_decision": "route-disjointness invariant failed: the ledger records deferred_wait_for_prior_submission; decision blocks advancement while overlap remains; allowed next actions are closure, merge, supersession, or waiting for prior-route feedback",
        "safe_lesson_at_bounded_evidence_level": "venue selection is stateful; path-verified only",
    },
    "Fake-extension block": {
        "gate_and_witness_surface": "theorem-content gate; phase-D hard lint and theorem-content delta review",
        "observed_issue_and_decision": "substantive-theorem-growth invariant failed when edits changed files without load-bearing content; theorem-content gate rejects the extension",
        "safe_lesson_at_bounded_evidence_level": "file churn or compilation alone is not progress; path-verified only",
    },
    "Rule110 limitation gate": {
        "gate_and_witness_surface": "artifact-limitation gate; artifact status, collision-audit ledger, exhaustiveness ledger, paper-data reference",
        "observed_issue_and_decision": "artifact-consistency invariant is bounded by historical audit findings and status text; without command, commit, environment, exit code, and log path, the row is not evidence for a rerun of make test-collision-audit; limitation gate permits disclosure or blocks promotion",
        "safe_lesson_at_bounded_evidence_level": "limitations disclose or block claims; path-verified only",
    },
}

CASE_ORDER = list(CASE_COMPILER)

BOUNDARY_MARKERS = (
    "Historical",
    "path-verified",
    "no fresh",
    "no claim",
)


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT.resolve()).as_posix()


def load_json(path: Path) -> dict[str, Any]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise SystemExit(f"missing required case-row artifact: {rel(path)}") from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(f"invalid JSON in {rel(path)}: {exc}") from exc


def check_submitted_path(path_text: str) -> None:
    path = Path(path_text)
    if path.is_absolute():
        raise SystemExit(f"absolute submitted snapshot path rejected: {path_text}")
    if "\\" in path_text:
        raise SystemExit(f"backslash submitted snapshot path rejected: {path_text}")
    if ".." in path.parts:
        raise SystemExit(f"dot-dot submitted snapshot path rejected: {path_text}")
    if not (ROOT / path_text).exists():
        raise SystemExit(f"submitted snapshot path does not exist: {path_text}")


def reconstruct_rows(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    case_evidence = manifest.get("case_evidence")
    if not isinstance(case_evidence, list):
        raise SystemExit("manifest case_evidence must be a list")

    by_case = {row.get("case"): row for row in case_evidence if isinstance(row, dict)}
    if sorted(by_case) != sorted(CASE_ORDER):
        raise SystemExit(
            "manifest case_evidence cases differ from compiler case set: "
            f"{sorted(by_case)} != {sorted(CASE_ORDER)}"
        )

    reconstructed: list[dict[str, Any]] = []
    for case in CASE_ORDER:
        manifest_row = by_case[case]
        snapshots = manifest_row.get("reviewable_snapshots")
        local_paths = manifest_row.get("local_paths")
        boundary = manifest_row.get("boundary")
        if not isinstance(snapshots, list) or not all(isinstance(p, str) for p in snapshots):
            raise SystemExit(f"{case}: reviewable_snapshots must be a string list")
        if not isinstance(local_paths, list) or not all(isinstance(p, str) for p in local_paths):
            raise SystemExit(f"{case}: local_paths must be a string list")
        if len(snapshots) != len(local_paths):
            raise SystemExit(
                f"{case}: local_paths and reviewable_snapshots lengths differ: "
                f"{len(local_paths)} != {len(snapshots)}"
            )
        for snapshot in snapshots:
            check_submitted_path(snapshot)
        if not isinstance(boundary, str) or not any(marker in boundary for marker in BOUNDARY_MARKERS):
            raise SystemExit(f"{case}: boundary does not declare historical/path-only scope")

        reconstructed.append(
            {
                "case": case,
                **CASE_COMPILER[case],
                "boundary": boundary,
                "reviewable_snapshots": snapshots,
            }
        )
    return reconstructed


def verify_negative_control(expected: dict[str, Any]) -> dict[str, str]:
    control = expected.get("negative_control")
    if not isinstance(control, dict):
        raise SystemExit("expected JSON must include negative_control")
    case_evidence = control.get("case_evidence")
    expected_rejection = control.get("expected_rejection")
    if not isinstance(case_evidence, list):
        raise SystemExit("negative_control.case_evidence must be a list")
    if not isinstance(expected_rejection, str) or not expected_rejection:
        raise SystemExit("negative_control.expected_rejection must be a nonempty string")

    try:
        reconstruct_rows({"case_evidence": case_evidence})
    except SystemExit as exc:
        reason = str(exc)
        if expected_rejection not in reason:
            raise SystemExit(
                "negative control rejected for unexpected reason: "
                f"{reason!r}; expected substring {expected_rejection!r}"
            ) from exc
        return {"status": "rejected", "reason": reason}

    raise SystemExit("negative control was accepted by the case-row verifier")


def main() -> int:
    manifest = load_json(MANIFEST)
    expected = load_json(EXPECTED)
    rows = reconstruct_rows(manifest)
    negative_control = verify_negative_control(expected)

    expected_rows = expected.get("expected_rows")
    if rows != expected_rows:
        print(
            json.dumps(
                {
                    "status": "rejected",
                    "reason": "reconstructed rows differ from expected_rows",
                    "reconstructed_rows": rows,
                    "expected_rows": expected_rows,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 1

    snapshot_paths = [path for row in rows for path in row["reviewable_snapshots"]]
    log = {
        "command": "python certificates/replay_case_rows.py",
        "environment": {
            "python_version": platform.python_version(),
            "platform": platform.platform(),
            "network": "not used",
            "working_directory": rel(ROOT),
        },
        "inputs": [rel(MANIFEST), rel(EXPECTED), "review_bundle/case_snapshots/"],
        "status": "accepted",
        "exit_code": 0,
        "rows_reconstructed": len(rows),
        "snapshot_paths_checked": len(snapshot_paths),
        "reconstructed_rows": rows,
        "negative_control": negative_control,
        "boundary": expected["expected_log"]["boundary"],
    }
    print(json.dumps(log, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
