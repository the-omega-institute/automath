#!/usr/bin/env python3
"""Verify the finite source-interface record used by the manuscript.

The check is intentionally record-level.  It compares the manuscript table,
the JSON mirror, the review-bundle manifest, and the pinned source snapshot.
It does not re-prove the imported theorems or validate the external source
semantics.
"""
from __future__ import annotations

import hashlib
import json
import platform
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MAIN = ROOT / "main.tex"
RECORD = ROOT / "source_interface_record.json"
MANIFEST = ROOT / "review_bundle" / "REVIEW_BUNDLE_MANIFEST.json"

TABLE_ROW = re.compile(
    r"^\\path\{(?P<label>[^}]+)\}\s*&\s*(?P<start>\d+)--(?P<end>\d+)\s*&\s*"
    r"(?P<summary>.*?)\s*\\\\\s*$"
)


def load_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8-sig"))
    except FileNotFoundError as exc:
        raise SystemExit(f"missing required file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(f"invalid JSON in {path}: {exc}") from exc


def ensure(condition: bool, message: str, errors: list[str]) -> None:
    if not condition:
        errors.append(message)


def manuscript_table_rows() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    in_table = False
    for raw_line in MAIN.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if "\\label{tab:source-interface-record}" in line:
            in_table = True
            continue
        if in_table and line == r"\bottomrule":
            break
        if not in_table:
            continue
        match = TABLE_ROW.match(line)
        if match:
            rows.append(
                {
                    "label": match.group("label"),
                    "line_range": f"{match.group('start')}-{match.group('end')}",
                    "statement_summary": match.group("summary"),
                }
            )
    return rows


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(65536), b""):
            digest.update(block)
    return digest.hexdigest()


def git_head() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True, stderr=subprocess.DEVNULL
        ).strip()
    except Exception:
        return "unavailable"


def parse_range(line_range: str) -> tuple[int, int]:
    start_text, end_text = line_range.split("-", 1)
    return int(start_text), int(end_text)


def verify() -> tuple[dict, list[str]]:
    errors: list[str] = []
    record = load_json(RECORD)
    manifest = load_json(MANIFEST)
    snapshot_record = manifest["pinned_source_snapshot"]
    snapshot = ROOT / snapshot_record["bundle_path"]
    snapshot_lines = snapshot.read_text(encoding="utf-8-sig").splitlines()

    table_rows = manuscript_table_rows()
    json_rows = record["records"]
    table_ranges = [row["line_range"] for row in table_rows]
    json_ranges = [row["line_range"] for row in json_rows]

    ensure(table_rows == json_rows, "manuscript table rows differ from source_interface_record.json", errors)
    ensure(
        record["source_path"] == snapshot_record["original_path"],
        "JSON source_path differs from manifest original_path",
        errors,
    )
    ensure(
        record["source_commit"] == snapshot_record["source_commit"],
        "JSON source_commit differs from manifest source_commit",
        errors,
    )
    ensure(
        json_ranges == snapshot_record["line_ranges_used"],
        "JSON line ranges differ from manifest line_ranges_used",
        errors,
    )

    computed_digest = sha256(snapshot)
    computed_line_count = len(snapshot_lines)
    ensure(
        computed_digest == snapshot_record.get("sha256"),
        "snapshot SHA-256 digest differs from manifest sha256",
        errors,
    )
    ensure(
        computed_line_count == snapshot_record.get("line_count"),
        "snapshot line count differs from manifest line_count",
        errors,
    )

    label_checks: list[dict[str, object]] = []
    for row in json_rows:
        start, end = parse_range(row["line_range"])
        ensure(1 <= start <= end <= computed_line_count, f"line range out of bounds for {row['label']}", errors)
        window = "\n".join(snapshot_lines[start - 1 : end]) if end <= computed_line_count else ""
        present = (f"\\label{{{row['label']}}}" in window) or (f"\n\\label{{{row['label']}}}" in window)
        label_checks.append({"label": row["label"], "line_range": row["line_range"], "label_in_range": present})
        ensure(present, f"snapshot label not found in declared range for {row['label']}", errors)

    report = {
        "verifier": "review_bundle/verify_source_interface_record.py",
        "command": "python review_bundle/verify_source_interface_record.py",
        "source_commit": git_head(),
        "source_digest_manifest": "review_bundle/FINAL_DIGESTS_SHA256.md",
        "environment": f"Python {platform.python_version()} on {platform.system()} {platform.release()}",
        "exit_code": 0 if not errors else 1,
        "log_path": "review_bundle/source_interface_verification_run.log",
        "evidence_level": "finite record comparison only",
        "table_row_count": len(table_rows),
        "json_record_count": len(json_rows),
        "manifest_range_count": len(snapshot_record["line_ranges_used"]),
        "snapshot_path": snapshot_record["bundle_path"],
        "snapshot_sha256": computed_digest,
        "snapshot_line_count": computed_line_count,
        "label_checks": label_checks,
        "status": "pass" if not errors else "fail",
        "errors": errors,
    }
    return report, errors


def main() -> int:
    report, errors = verify()
    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
