#!/usr/bin/env python3
"""Verify exact recognition of the mandatory Stage-A theorem package in inventory files."""
from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LABELS = [
    "thm:finite-audit-antichain-basis",
    "thm:canonical-stage-a-obstruction-basis",
    "thm:no-theorem-delta-nondischarge",
    "thm:stage-a-real-block-discharge-completeness",
    "cor:current-stage-a-closure-exactness",
]
TITLES = [
    "Finite Audit Antichain Basis",
    "Canonical Stage-A Obstruction Basis",
    "No-Theorem-Delta Non-Discharge Theorem",
    "Stage-A Real-Block Discharge Completeness",
    "Current Stage-A Closure Exactness",
]
DEPENDENCIES = {
    "thm:presentation-compressed-interface",
    "thm:publication-safety-interface",
    "thm:external-interface-projection-no-free-upgrade",
    "thm:four-case-foreground-support-boundary",
    "cor:stage-a-issue-discharge-normal-form",
    "thm:six-coordinate-submission-boundary-normal-form",
    "thm:current-round-local-only-fixed-point-classifier",
}


def main() -> int:
    md = (ROOT / "theorem_inventory.md").read_text(encoding="utf-8-sig")
    raw_json = (ROOT / "theorem_inventory.json").read_text(encoding="utf-8-sig")
    data = json.loads(raw_json)
    rows = data.get("in_scope_present", [])
    by_label = {row.get("label"): row for row in rows if isinstance(row, dict)}
    errors: list[str] = []

    for label, title in zip(LABELS, TITLES):
        if label not in md:
            errors.append(f"theorem_inventory.md missing {label}")
        if title not in md:
            errors.append(f"theorem_inventory.md missing title {title}")
        row = by_label.get(label)
        if row is None:
            errors.append(f"theorem_inventory.json missing exact row {label}")
            continue
        if row.get("title") != title:
            errors.append(f"{label}: title mismatch")
        if not str(row.get("primary_route_status", "")).startswith("mandatory primary-route"):
            errors.append(f"{label}: not marked mandatory primary-route")
        row_deps = set(row.get("dependencies", []))
        missing_deps = sorted(DEPENDENCIES - row_deps)
        if missing_deps:
            errors.append(f"{label}: missing dependencies {missing_deps}")

    summary = {
        "command": "python review_bundle/verify_theorem_inventory_sync.py",
        "required_labels": LABELS,
        "required_titles": TITLES,
        "required_dependencies": sorted(DEPENDENCIES),
        "exact_primary_route_rows": sum(1 for label in LABELS if label in by_label),
        "errors": errors,
        "exit_code": 1 if errors else 0,
        "boundary": "inventory-label/title/dependency synchronization only; no semantic proof checking",
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
