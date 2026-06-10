#!/usr/bin/env python3
"""Verify the primary-claim inventory freshness record.

This script performs a finite record check only.  It verifies that the submitted
primary-claim inventory has the expected row shape, references line spans inside
the current primary source, and points each row to at least one certificate-like
surface.  It does not prove the semantics of the primary prose.
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
BUNDLE = ROOT / "review_bundle"
PRIMARY = ROOT / "submission_abstract.tex"
INVENTORY = BUNDLE / "primary_claim_inventory.json"


LOCATION_RE = re.compile(r"^submission_abstract\.tex:(\d+)-(\d+)$")
EXPECTED_LOCATIONS = {
    "pc1": "submission_abstract.tex:30-51",
    "pc2": "submission_abstract.tex:57-68",
    "pc3": "submission_abstract.tex:70-72",
    "pc4": "submission_abstract.tex:71-72",
    "pc5": "submission_abstract.tex:74-77",
    "pc6": "submission_abstract.tex:76-79",
    "pc7": "submission_abstract.tex:86-102",
    "pc8": "submission_abstract.tex:104-112",
    "pc9": "submission_abstract.tex:105-114",
    "pc10": "submission_abstract.tex:105-114",
    "pc11": "submission_abstract.tex:105-114",
    "pc12": "submission_abstract.tex:105-114",
}
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


def git_head() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True, stderr=subprocess.DEVNULL
        ).strip()
    except Exception:
        return "unavailable"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(65536), b""):
            digest.update(block)
    return digest.hexdigest()


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

        expected_location = EXPECTED_LOCATIONS.get(str(row_id))
        if expected_location is not None and row.get("location") != expected_location:
            errors.append(f"{row_id}: location must be {expected_location}")

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
        "source_commit": git_head(),
        "source_hashes": {
            "submission_abstract.tex": sha256(PRIMARY),
            "review_bundle/primary_claim_inventory.json": sha256(INVENTORY),
        },
        "source_digest_manifest": "review_bundle/FINAL_DIGESTS_SHA256.md",
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
