#!/usr/bin/env python3
"""Extract labelled theorem-like environments and compare them to theorem_inventory.json.

The extractor is intentionally syntactic. It proves only that the labelled
theorem-like environments in main.tex are represented by labels in the Stage-A
inventory file; it does not prove the statements or inspect proof semantics.
"""
from __future__ import annotations

import json
import platform
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
THEOREM_ENVS = ("definition", "lemma", "proposition", "theorem", "corollary")
BEGIN_RE = re.compile(r"\\begin\{(" + "|".join(THEOREM_ENVS) + r")\}(?:\[([^\]]*)\])?")
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
INVENTORY_LABEL_RE = re.compile(r"\b(?:def|lem|prop|thm|cor|audit|prin):[A-Za-z0-9_.:-]+")


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8-sig")


def git_head() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True, stderr=subprocess.DEVNULL
        ).strip()
    except Exception:
        return "unavailable"


def extract_tex_environments(tex_path: Path) -> list[dict[str, object]]:
    lines = read_text(tex_path).splitlines()
    records: list[dict[str, object]] = []
    for line_number, line in enumerate(lines, start=1):
        match = BEGIN_RE.search(line)
        if not match:
            continue
        env = match.group(1)
        title = match.group(2) or ""
        end_line = line_number
        body_lines: list[str] = []
        end_re = re.compile(r"\\end\{" + re.escape(env) + r"\}")
        for cursor in range(line_number, len(lines) + 1):
            current = lines[cursor - 1]
            body_lines.append(current)
            if end_re.search(current):
                end_line = cursor
                break
        body = "\n".join(body_lines)
        label_match = LABEL_RE.search(body)
        records.append(
            {
                "file": tex_path.name,
                "line": line_number,
                "end_line": end_line,
                "environment": env,
                "title": title,
                "label": label_match.group(1) if label_match else None,
            }
        )
    return records


def inventory_labels(inventory_path: Path) -> set[str]:
    data = json.loads(read_text(inventory_path))
    labels: set[str] = set()
    if not isinstance(data, dict):
        raise ValueError("theorem_inventory.json root must be an object")
    for rows in data.values():
        if not isinstance(rows, list):
            continue
        for row in rows:
            if isinstance(row, dict):
                labels.update(INVENTORY_LABEL_RE.findall(str(row.get("label", ""))))
    return labels


def verify() -> tuple[list[str], dict[str, object]]:
    tex_path = ROOT / "main.tex"
    inventory_path = ROOT / "theorem_inventory.json"
    records = extract_tex_environments(tex_path)
    labels = [str(record["label"]) for record in records if record.get("label")]
    missing_labels = [record for record in records if not record.get("label")]
    duplicate_labels = sorted(label for label, count in Counter(labels).items() if count > 1)
    inventory = inventory_labels(inventory_path)
    tex_label_set = set(labels)
    omitted_from_inventory = sorted(tex_label_set - inventory)

    errors: list[str] = []
    if missing_labels:
        errors.append("unlabelled theorem-like environments present")
    if duplicate_labels:
        errors.append(f"duplicate labels present: {duplicate_labels}")
    if omitted_from_inventory:
        errors.append(f"theorem labels absent from theorem_inventory.json: {omitted_from_inventory}")

    summary: dict[str, object] = {
        "command": "python review_bundle/extract_theorem_environments.py",
        "source_commit": git_head(),
        "source_digest_manifest": "review_bundle/FINAL_DIGESTS_SHA256.md",
        "environment": f"Python {platform.python_version()} on {platform.system()} {platform.release()}",
        "cwd": str(ROOT).replace("\\", "/"),
        "tex_source": "main.tex",
        "inventory": "theorem_inventory.json",
        "theorem_like_environment_domain": list(THEOREM_ENVS),
        "environment_count": len(records),
        "labelled_environment_count": len(labels),
        "inventory_label_count": len(inventory),
        "missing_label_count": len(missing_labels),
        "duplicate_label_count": len(duplicate_labels),
        "omitted_from_inventory_count": len(omitted_from_inventory),
        "errors": len(errors),
        "exit_code": 1 if errors else 0,
        "log_path": "review_bundle/theorem_environment_extraction_run.log",
        "boundary": "syntactic theorem-like environment extraction and inventory-label coverage only; no semantic proof checking",
        "records": records,
        "omitted_from_inventory": omitted_from_inventory,
    }
    return errors, summary


def main() -> int:
    errors, summary = verify()
    print(json.dumps(summary, indent=2, sort_keys=True))
    for error in errors:
        print(f"error={error}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
