#!/usr/bin/env python3
"""Verify the primary-claim inventory freshness record.

This script performs a finite record check only.  It verifies that the submitted
primary-claim inventory has the expected row shape, references line spans inside
the current primary source, and points each row to at least one certificate-like
surface.  It does not prove the semantics of the primary prose.
"""
from __future__ import annotations

import json
import platform
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BUNDLE = ROOT / "review_bundle"
PRIMARY = ROOT / "submission_abstract.tex"
INVENTORY = BUNDLE / "primary_claim_inventory.json"


LOCATION_RE = re.compile(r"^submission_abstract\.tex:(\d+)-(\d+)$")
CERTIFICATE_PREFIXES = (
    "sim",
    "a",
    "source_interface_record.json",
    "review_bundle/",
    "manifest:",
    "table:",
    "theorem:",
    "proposition:",
    "lemma:",
    "corollary:",
)


def load_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8-sig"))
    except FileNotFoundError as exc:
        raise SystemExit(f"missing required file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(f"invalid JSON in {path}: {exc}") from exc


def certificate_surface_exists(pointer: str) -> bool:
    if pointer.startswith(CERTIFICATE_PREFIXES):
        return True
    return (ROOT / pointer).exists()


def verify() -> tuple[list[str], dict[str, object]]:
    primary_lines = PRIMARY.read_text(encoding="utf-8-sig").splitlines()
    inventory = load_json(INVENTORY)
    rows = inventory.get("rows", [])
    errors: list[str] = []

    if inventory.get("primary_artifact") != "submission_abstract.tex":
        errors.append("primary_artifact must be submission_abstract.tex")
    if not isinstance(rows, list) or not rows:
        errors.append("rows must be a nonempty list")

    seen: set[str] = set()
    for row in rows if isinstance(rows, list) else []:
        row_id = row.get("id", "<missing>")
        if row_id in seen:
            errors.append(f"duplicate row id: {row_id}")
        seen.add(row_id)

        match = LOCATION_RE.match(str(row.get("location", "")))
        if not match:
            errors.append(f"{row_id}: invalid location format")
        else:
            start, end = map(int, match.groups())
            if start < 1 or end < start or end > len(primary_lines):
                errors.append(f"{row_id}: location outside primary source")

        for field in ("claim", "status", "evidence_level"):
            if not str(row.get(field, "")).strip():
                errors.append(f"{row_id}: missing {field}")

        certificate = row.get("certificate")
        if not isinstance(certificate, list) or not certificate:
            errors.append(f"{row_id}: certificate must be a nonempty list")
        elif not any(certificate_surface_exists(str(pointer)) for pointer in certificate):
            errors.append(f"{row_id}: no certificate-like surface found")

    expected_ids = {f"pc{i}" for i in range(1, 13)}
    if seen != expected_ids:
        errors.append(f"row id set must be pc1-pc12, got {sorted(seen)}")

    summary = {
        "command": "python review_bundle/verify_primary_claim_inventory.py",
        "environment": f"Python {platform.python_version()} on {platform.system()} {platform.release()}",
        "cwd": str(ROOT).replace("\\", "/"),
        "primary_artifact": "submission_abstract.tex",
        "inventory": "review_bundle/primary_claim_inventory.json",
        "primary_lines": len(primary_lines),
        "inventory_rows": len(rows) if isinstance(rows, list) else 0,
        "errors": len(errors),
        "exit_code": 1 if errors else 0,
    }
    return errors, summary


def main() -> int:
    errors, summary = verify()
    for key, value in summary.items():
        print(f"{key}={value}")
    for error in errors:
        print(f"error={error}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
