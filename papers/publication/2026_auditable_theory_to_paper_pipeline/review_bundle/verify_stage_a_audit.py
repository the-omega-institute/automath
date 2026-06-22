#!/usr/bin/env python3
"""Verify stage_a_audit.json recognizes the required antichain theorem package."""
from __future__ import annotations

import hashlib
import json
import platform
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REQUIRED_LABELS = [
    "thm:finite-audit-antichain-basis",
    "thm:canonical-stage-a-obstruction-basis",
    "thm:no-theorem-delta-nondischarge",
    "thm:stage-a-real-block-discharge-completeness",
    "cor:current-stage-a-closure-exactness",
]
REQUIRED_TITLES = [
    "Finite Audit Antichain Basis",
    "Canonical Stage-A Obstruction Basis",
    "No-Theorem-Delta Non-Discharge Theorem",
    "Stage-A Real-Block Discharge Completeness",
    "Current Stage-A Closure Exactness",
]


def read_text(relative: str) -> str:
    return (ROOT / relative).read_text(encoding="utf-8-sig")


def load_json(relative: str) -> dict:
    try:
        return json.loads(read_text(relative))
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
    tex = read_text("main.tex")
    inv_md = read_text("theorem_inventory.md")
    inv_json_text = read_text("theorem_inventory.json")
    audit = load_json("stage_a_audit.json")

    for label in REQUIRED_LABELS:
        if f"\\label{{{label}}}" not in tex:
            errors.append(f"missing TeX label {label}")
        if label not in inv_md:
            errors.append(f"missing theorem_inventory.md label {label}")
        if label not in inv_json_text:
            errors.append(f"missing theorem_inventory.json label {label}")

    for title in REQUIRED_TITLES:
        if title not in tex:
            errors.append(f"missing TeX title {title}")

    resolved = [
        row for row in audit.get("resolved_blocks", [])
        if row.get("block_id") == "stage_a_audit_real_block"
    ]
    if len(resolved) != 1:
        errors.append("stage_a_audit_real_block must have exactly one resolved record")
    else:
        row = resolved[0]
        if row.get("status") not in {"resolved_by_theorem_package", "stale_resolved_by_label_recognition"}:
            errors.append("stage_a_audit_real_block status is not an accepted resolved status")
        if row.get("discharging_theorems") != REQUIRED_LABELS:
            errors.append("stage_a_audit_real_block discharging_theorems do not match required labels")
        if row.get("remaining_absent_coordinates") != []:
            errors.append("stage_a_audit_real_block remaining_absent_coordinates must be empty")

    if audit.get("verdict") != "proceed":
        errors.append("stage_a_audit.json verdict is not proceed")
    if not audit.get("ready_for_oracle_review"):
        errors.append("stage_a_audit.json ready_for_oracle_review is not true")

    proof_env_count = len(re.findall(r"\\begin\{proof\}", tex))
    summary = {
        "command": "python review_bundle/verify_stage_a_audit.py",
        "source_commit": git_head(),
        "source_hashes": {
            "main.tex": sha256("main.tex"),
            "theorem_inventory.md": sha256("theorem_inventory.md"),
            "theorem_inventory.json": sha256("theorem_inventory.json"),
            "stage_a_audit.json": sha256("stage_a_audit.json"),
        },
        "source_digest_manifest": "review_bundle/FINAL_DIGESTS_SHA256.md",
        "environment": f"Python {platform.python_version()} on {platform.system()} {platform.release()}",
        "required_labels": REQUIRED_LABELS,
        "required_titles": REQUIRED_TITLES,
        "proof_environment_count": proof_env_count,
        "errors": errors,
        "exit_code": 1 if errors else 0,
        "log_path": "review_bundle/stage_a_audit_verification_run.log",
        "boundary": "finite label, title, inventory, and audit-block recognition only; no semantic proof checking",
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
