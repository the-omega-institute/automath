#!/usr/bin/env python3
"""Production loop for lightweight NewMath-to-Automath bridge outputs.

The scanner and heavy loop produce ignored bridge artifacts. This loop turns
eligible NewMath-to-Automath observations into durable Automath receiving
indexes. It does not write Automath paper or Lean content; Automath paper
writeback remains owned by the Killo/golden distillation lane.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
GATE_RESULTS = SCRIPT_DIR / "out" / "bridge_gate_results.jsonl"
SYNTHESIS_RESULTS = SCRIPT_DIR / "out" / "bridge_synthesis.jsonl"
STOP_FILE = SCRIPT_DIR / ".bridge_production_loop.stop"
LOG_FILE = SCRIPT_DIR / "logs" / "bridge_production_loop.log"
INDEX_PATH = REPO_ROOT / "docs" / "bridge" / "newmath-consumption-index.md"


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def _log(message: str) -> None:
    LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {message}"
    print(line, flush=True)
    with LOG_FILE.open("a", encoding="utf-8") as handle:
        handle.write(line + "\n")


def _git(args: list[str], *, timeout: int = 120) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", *args], cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=timeout, check=False)


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            text = line.strip()
            if not text:
                continue
            data = json.loads(text)
            if isinstance(data, dict):
                rows.append(data)
    return rows


def _normalized(record: dict[str, Any], *, input_kind: str) -> dict[str, Any]:
    normalized = dict(record)
    synthesis = record.get("synthesis")
    if isinstance(synthesis, dict):
        normalized.setdefault("readiness", synthesis.get("readiness"))
        normalized.setdefault("readiness_confidence", synthesis.get("readiness_confidence"))
        normalized.setdefault("evidence_summary", synthesis.get("evidence_summary"))
        normalized.setdefault("required_gates", synthesis.get("required_gates"))
        normalized.setdefault("why_not_writeback_yet", synthesis.get("why_not_writeback_yet"))
    normalized["_bridge_input_kind"] = input_kind
    return normalized


def _load_records(args: argparse.Namespace) -> tuple[list[dict[str, Any]], str]:
    gate_records = [_normalized(record, input_kind="gate") for record in _read_jsonl(Path(args.gate_results))]
    if gate_records:
        return gate_records, "gate"
    synthesis_records = [_normalized(record, input_kind="synthesis") for record in _read_jsonl(Path(args.synthesis_results))]
    return synthesis_records, "synthesis"


def _direction_records(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        record
        for record in records
        if record.get("bridge_direction") == "newmath_to_automath"
        and record.get("destination_repo") == "the-omega-institute/automath"
    ]


def _pre_gate_passed(record: dict[str, Any]) -> bool:
    readiness = str(record.get("readiness") or "")
    if record.get("gate_status") != "gate_passed":
        return False
    if readiness != "ready_for_local_packet":
        return False
    if record.get("taste_gate_required") and not str(record.get("readiness_confidence") or ""):
        return False
    return True


def _review_only(record: dict[str, Any]) -> bool:
    return (
        record.get("_bridge_input_kind") == "synthesis"
        and record.get("bridge_direction") == "newmath_to_automath"
        and record.get("destination_repo") == "the-omega-institute/automath"
        and str(record.get("readiness") or "") == "ready_for_local_packet"
    )


def _post_gate_state(record: dict[str, Any]) -> str:
    if _review_only(record):
        return "review_only_synthesis_not_writeback_eligible"
    if not _pre_gate_passed(record):
        return "not_selected"
    if record.get("operator_review_required") and record.get("status") not in {"accepted", "consumed"}:
        return "awaiting_operator_acceptance"
    return "eligible_for_killo_golden_distillation"


def _selected(records: list[dict[str, Any]], *, limit: int) -> list[dict[str, Any]]:
    selected = [record for record in _direction_records(records) if _pre_gate_passed(record) or _review_only(record)]
    selected.sort(key=lambda item: (-int(item.get("priority_score") or 0), str(item.get("source_path") or "")))
    return selected[:limit]


def _blocked(records: list[dict[str, Any]], *, limit: int) -> list[dict[str, Any]]:
    blocked = [record for record in _direction_records(records) if not _pre_gate_passed(record) and not _review_only(record)]
    blocked.sort(key=lambda item: (-int(item.get("priority_score") or 0), str(item.get("source_path") or "")))
    return blocked[:limit]


def _readiness_bucket(readiness: str) -> str:
    if readiness == "ready_for_local_packet":
        return "review packet candidate"
    if readiness == "needs_operator_review":
        return "operator review boundary"
    if readiness == "blocked_automath_not_ready":
        return "blocked until Automath target is selected"
    return "observed"


def _render(records: list[dict[str, Any]], *, limit: int, input_kind: str) -> str:
    selected = _selected(records, limit=limit)
    blocked = _blocked(records, limit=limit)
    direction_records = _direction_records(records)
    counts: dict[str, int] = {}
    for record in direction_records:
        readiness = str(record.get("readiness") or "unknown")
        counts[readiness] = counts.get(readiness, 0) + 1
    lines = [
        "# NewMath Consumption Index",
        "",
        "This index is the Automath receiving surface for NewMath bridge evidence.",
        "It records NewMath-to-Automath candidates, readiness, and blocking",
        "reasons without writing Automath paper or Lean content. Automath durable",
        "paper writes remain behind the Killo/golden distillation lane.",
        "",
        f"Input source: `{input_kind}`.",
        "",
        f"Selection gate: `{len(selected)}` receivable item(s), `{len(blocked)}` blocked or review-only item(s).",
        "",
        "## Readiness Summary",
        "",
        "| Readiness | Count | Automath meaning |",
        "| --- | ---: | --- |",
    ]
    for readiness, count in sorted(counts.items(), key=lambda item: (-item[1], item[0])):
        lines.append(f"| `{readiness}` | {count} | {_readiness_bucket(readiness)} |")
    if not counts:
        lines.append("| _none_ | 0 | no current NewMath-to-Automath candidates |")
    lines.extend(
        [
            "",
            "## Receivable NewMath Inputs",
            "",
            "| Source | Kind | Readiness | Score | Post-gate state | Automath action |",
            "| --- | --- | --- | ---: | --- | --- |",
        ]
    )
    for record in selected:
        source = f"{record.get('source_repo')}@{record.get('source_branch_or_ref')}:{record.get('source_path')}"
        readiness = str(record.get("readiness") or "")
        action = "summarize as review packet; Killo/golden required before paper write"
        lines.append(
            "| `{}` | `{}` | `{}` | {} | `{}` | {} |".format(
                source,
                record.get("source_artifact_kind", ""),
                readiness,
                int(record.get("priority_score") or 0),
                _post_gate_state(record),
                action,
            )
        )
    if not selected:
        lines.append("| _none_ |  |  |  |  |  |")
    lines.extend(
        [
            "",
            "## Blocked Or Review-Only Inputs",
            "",
            "| Source | Kind | Readiness | Score | Blocking reason |",
            "| --- | --- | --- | ---: | --- |",
        ]
    )
    for record in blocked:
        source = f"{record.get('source_repo')}@{record.get('source_branch_or_ref')}:{record.get('source_path')}"
        readiness = str(record.get("readiness") or "")
        if readiness == "blocked_automath_not_ready":
            reason = "Automath receiving theorem or article section has not been selected"
        elif readiness == "needs_operator_review":
            reason = "operator review is required before this can become receivable"
        elif readiness == "observe_only":
            reason = "observation only"
        else:
            reason = "pre-gate did not mark the item receivable"
        lines.append(
            "| `{}` | `{}` | `{}` | {} | {} |".format(
                source,
                record.get("source_artifact_kind", ""),
                readiness,
                int(record.get("priority_score") or 0),
                reason,
            )
        )
    if not blocked:
        lines.append("| _none_ |  |  |  |  |")
    lines.extend(
        [
            "",
            "## Policy",
            "",
            "- The writeback selection gate admits only `gate_status=gate_passed` and `ready_for_local_packet` records.",
            "- `Input source: synthesis` means review-only evidence, not a deterministic gate pass.",
            "- `needs_operator_review` records a boundary, not acceptance, and is not selected for writeback.",
            "- `blocked_automath_not_ready` means NewMath evidence exists but Automath has not chosen a receiving paper/Lean target; it is never selected as returnable content.",
            "- The post-gate requires operator acceptance before any Killo/golden distillation candidate can be used.",
            "- Automath paper writeback must pass the native Killo/golden distillation and review lane.",
            "- BEDC text, seed stubs, and TasteGate witnesses must not be copied verbatim into Automath paper content.",
        ]
    )
    return "\n".join(lines) + "\n"


def _index_has_entries(text: str) -> bool:
    return "| _none_ |" not in text and "| `" in text


def _commit_if_changed(paths: list[Path], message: str, *, push: bool) -> dict[str, Any]:
    add = _git(["add", *[str(path.relative_to(REPO_ROOT)) for path in paths if path.exists()]], timeout=30)
    if add.returncode != 0:
        return {"status": "add_failed", "stderr": add.stderr.strip()}
    diff = _git(["diff", "--cached", "--quiet"], timeout=30)
    if diff.returncode == 0:
        return {"status": "nothing_to_commit"}
    commit = _git(["commit", "-m", message], timeout=120)
    if commit.returncode != 0:
        return {"status": "commit_failed", "stderr": commit.stderr.strip()}
    result: dict[str, Any] = {"status": "committed", "stdout": commit.stdout.strip()}
    if push:
        branch = _git(["branch", "--show-current"], timeout=30).stdout.strip()
        if branch.startswith("codex/"):
            pushed = _git(["push", "origin", branch], timeout=300)
            result["push"] = "ok" if pushed.returncode == 0 else pushed.stderr.strip()
        else:
            result["push"] = f"skipped non-codex branch {branch}"
    return result


def run_once(args: argparse.Namespace) -> bool:
    records, input_kind = _load_records(args)
    selected = _selected(records, limit=args.limit)
    content = _render(records, limit=args.limit, input_kind=input_kind)
    INDEX_PATH.parent.mkdir(parents=True, exist_ok=True)
    old = INDEX_PATH.read_text(encoding="utf-8") if INDEX_PATH.exists() else ""
    if not selected and _index_has_entries(old) and not args.allow_empty:
        commit = {"status": "preserved_non_empty_index"}
        _log(json.dumps({"records": len(records), "selected": 0, "input_kind": input_kind, "commit": commit}, sort_keys=True))
        return True
    if old != content:
        INDEX_PATH.write_text(content, encoding="utf-8")
    commit = _commit_if_changed([INDEX_PATH], "bridge(automath): update NewMath consumption index", push=args.push)
    _log(json.dumps({"records": len(records), "selected": len(selected), "input_kind": input_kind, "commit": commit}, sort_keys=True))
    return commit.get("status") in {"committed", "nothing_to_commit", "preserved_non_empty_index"}


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run lightweight durable NewMath-to-Automath bridge production")
    parser.add_argument("--gate-results", default=str(GATE_RESULTS))
    parser.add_argument("--synthesis-results", default=str(SYNTHESIS_RESULTS))
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--poll-interval", type=int, default=1800)
    parser.add_argument("--limit", type=int, default=45)
    parser.add_argument("--push", action="store_true")
    parser.add_argument("--allow-empty", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    while True:
        try:
            ok = run_once(args)
        except Exception as exc:
            _log(f"production pass failed: {exc}")
            ok = False
        if args.once or STOP_FILE.exists():
            return 0 if ok else 1
        time.sleep(max(60, args.poll_interval))


if __name__ == "__main__":
    raise SystemExit(main())
