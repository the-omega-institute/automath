#!/usr/bin/env python3
"""Render NewMath bridge ACK/NACK ledgers for Automath-side review."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_CONFIG = SCRIPT_DIR / "bridge_pipeline_config.json"
DEFAULT_OUTPUT = REPO_ROOT / "docs" / "bridge" / "newmath-bridge-ack-status.md"


def _load_config(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    return data if isinstance(data, dict) else {}


def _resolve_repo(config: dict[str, Any], config_path: Path) -> Path:
    repos = config.get("repositories") if isinstance(config.get("repositories"), dict) else {}
    newmath = repos.get("newmath") if isinstance(repos.get("newmath"), dict) else {}
    raw = Path(str(newmath.get("local_path") or "../newmath"))
    candidates = [raw] if raw.is_absolute() else [config_path.parent / raw, REPO_ROOT / raw, REPO_ROOT.parent / raw]
    for candidate in candidates:
        resolved = candidate.resolve()
        if (resolved / ".git").exists():
            return resolved
    return candidates[-1].resolve()


def _git_show(repo: Path, ref: str, path: str) -> str:
    proc = subprocess.run(["git", "show", f"{ref}:{path}"], cwd=str(repo), capture_output=True, text=True, check=False)
    return proc.stdout if proc.returncode == 0 else ""


def _read_jsonl(text: str) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for line in text.splitlines():
        try:
            item = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(item, dict):
            records.append(item)
    return records


def _render(ack: list[dict[str, Any]], failures: list[dict[str, Any]], *, ref: str) -> str:
    status_counts: dict[str, int] = {}
    for record in ack + failures:
        status = str(record.get("status") or "unknown")
        status_counts[status] = status_counts.get(status, 0) + 1
    lines = [
        "# NewMath Bridge ACK Status",
        "",
        f"- Source ref: `{ref}`",
        f"- ACK rows: `{len(ack)}`",
        f"- Failure rows: `{len(failures)}`",
        "",
        "## Status Counts",
        "",
        "| Status | Count |",
        "| --- | ---: |",
    ]
    for status, count in sorted(status_counts.items()):
        lines.append(f"| `{status}` | {count} |")
    lines.extend([
        "",
        "## Latest ACK/NACK Rows",
        "",
        "| Status | Target | Source | Reason |",
        "| --- | --- | --- | --- |",
    ])
    for record in (ack + failures)[-40:]:
        source = f"{record.get('source_repo')}@{record.get('source_branch_or_ref')}:{record.get('source_path')}"
        lines.append(
            "| "
            + " | ".join(
                str(cell).replace("|", "\\|")
                for cell in [
                    f"`{record.get('status', '')}`",
                    f"`{record.get('target_id', '')}`",
                    source,
                    record.get("reason") or record.get("failure_kind") or record.get("next_action") or "",
                ]
            )
            + " |"
        )
    lines.extend([
        "",
        "## Boundary",
        "",
        "This report is durable bridge telemetry only. It does not approve Automath paper or Lean writeback. Raw NewMath runtime logs remain uncommitted.",
        "",
    ])
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Render NewMath bridge ACK/NACK status")
    parser.add_argument("--config", default=str(DEFAULT_CONFIG))
    parser.add_argument("--newmath-ref", default="origin/bridge/newmath-automath-consumption")
    parser.add_argument("--ack-path", default="docs/bridge/automath-newmath-ack.jsonl")
    parser.add_argument("--failure-path", default="docs/bridge/automath-newmath-failures.jsonl")
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT))
    args = parser.parse_args(argv)
    config_path = Path(args.config).resolve()
    repo = _resolve_repo(_load_config(config_path), config_path)
    ack = _read_jsonl(_git_show(repo, args.newmath_ref, args.ack_path))
    failures = _read_jsonl(_git_show(repo, args.newmath_ref, args.failure_path))
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(_render(ack, failures, ref=args.newmath_ref), encoding="utf-8")
    print(json.dumps({"ack": len(ack), "failures": len(failures), "output": str(output)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
