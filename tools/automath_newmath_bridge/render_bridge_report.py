#!/usr/bin/env python3
"""Render bridge manifest JSONL as a Markdown review report."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DEFAULT_INPUT = Path(__file__).resolve().parent / "bridge_manifest.jsonl"
DEFAULT_OUTPUT = Path(__file__).resolve().parent / "out" / "bridge_report.md"


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            stripped = line.strip()
            if stripped:
                records.append(json.loads(stripped))
    return records


def _cell(value: Any) -> str:
    text = str(value if value is not None else "")
    return text.replace("|", "\\|").replace("\n", " ")


def render(records: list[dict[str, Any]], source: Path) -> str:
    status_counts = Counter(str(r.get("status", "")) for r in records)
    direction_counts = Counter(str(r.get("bridge_direction", "")) for r in records)
    lines: list[str] = [
        "# Automath-NewMath bridge report",
        "",
        f"- Source JSONL: `{source}`",
        f"- Rendered at: `{_now_iso()}`",
        f"- Records: `{len(records)}`",
        "",
        "## Status summary",
        "",
        "| Status | Count |",
        "| --- | ---: |",
    ]
    for status, count in sorted(status_counts.items()):
        lines.append(f"| `{_cell(status)}` | {count} |")

    lines.extend([
        "",
        "## Direction summary",
        "",
        "| Direction | Count |",
        "| --- | ---: |",
    ])
    for direction, count in sorted(direction_counts.items()):
        lines.append(f"| `{_cell(direction)}` | {count} |")

    lines.extend([
        "",
        "## Records",
        "",
        "| ID | Direction | Status | Source | Destination | Boundaries | Next action |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ])
    for record in records:
        source_label = (
            f"{record.get('source_repo')}@{record.get('source_branch_or_ref')}:"
            f"{record.get('source_path')} ({str(record.get('source_commit', ''))[:12]})"
        )
        dest_label = (
            f"{record.get('destination_repo')}@{record.get('destination_branch_or_ref')}:"
            f"{record.get('destination_path')}"
        )
        boundaries = ", ".join(
            key
            for key, enabled in (
                ("operator", record.get("operator_review_required")),
                ("taste_gate", record.get("taste_gate_required")),
                ("audit", record.get("audit_required")),
                (f"publication:{record.get('external_publication_risk')}", True),
            )
            if enabled
        )
        lines.append(
            "| "
            + " | ".join(
                [
                    f"`{_cell(record.get('id'))}`",
                    f"`{_cell(record.get('bridge_direction'))}`",
                    f"`{_cell(record.get('status'))}`",
                    _cell(source_label),
                    _cell(dest_label),
                    _cell(boundaries),
                    _cell(record.get("next_action")),
                ]
            )
            + " |"
        )

    lines.extend([
        "",
        "## Non-actions",
        "",
        "This report is review material only. It does not sync files, accept proposals, apply writebacks, push branches, publish pages, send email, or post issues/comments.",
        "",
    ])
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Render bridge manifest report")
    parser.add_argument("input", nargs="?", default=str(DEFAULT_INPUT), help="manifest or packet JSONL")
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT), help="Markdown output path")
    args = parser.parse_args(argv)

    input_path = Path(args.input)
    output_path = Path(args.output)
    records = _read_jsonl(input_path)
    report = render(records, input_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(report, encoding="utf-8")
    print(f"[bridge-report] wrote {output_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
