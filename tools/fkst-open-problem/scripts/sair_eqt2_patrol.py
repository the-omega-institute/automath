#!/usr/bin/env python3
"""Periodic SAIR-EQT2-only FKST patrol.

This script is intentionally narrow:
- one target: SAIR-EQT2;
- no GitHub writes;
- no automatic upstream issue filing;
- only bounded self-healing for the running supervisor and generated claim-state.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import plistlib
import re
import subprocess
import sys
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
ARTIFACT_DIR = ROOT / "artifacts" / "sair-eqt2"
CLAIM_STATE = ARTIFACT_DIR / "claim_state.jsonl"
RESEARCH_RUN = ARTIFACT_DIR / "research_run.jsonl"
PATROL_JSONL = ARTIFACT_DIR / "patrol_log.jsonl"
PATROL_REPORT = ARTIFACT_DIR / "patrol_report.md"
ISSUE_CANDIDATES = ARTIFACT_DIR / "fkst_issue_candidates.jsonl"

STATUS_REPORT = ROOT / "scripts" / "sair_eqt2_status_report.py"
DRY_RUN = ROOT / "scripts" / "sair_eqt2_dry_run.py"

LABEL = "org.omega.fkst-sair-eqt2"
PATROL_LABEL = "org.omega.fkst-sair-eqt2-patrol"
PATROL_PLIST = Path("/tmp/org.omega.fkst-sair-eqt2-patrol.plist")
PATROL_STDOUT = Path("/tmp/fkst-sair-eqt2-patrol.log")
PATROL_STDERR = Path("/tmp/fkst-sair-eqt2-patrol.err")
HEALTH_JSONL = Path("/tmp/fkst-sair-eqt2-health.jsonl")

ERROR_SOURCES = [
    Path("/tmp/fkst-sair-eqt2-runtime/logs"),
    Path("/tmp/fkst-sair-eqt2-supervise.log"),
    Path("/tmp/fkst-sair-eqt2-supervise.err"),
    Path("/tmp/fkst-sair-eqt2-watch.log"),
    Path("/tmp/fkst-sair-eqt2-watch.err"),
]
ERROR_PATTERN = re.compile(
    r"DEAD_LETTER|framework failed|raised publish error|error_class=|"
    r"caught-failure|Operation not permitted|panic|thread '.*' panicked|"
    r"codex-failed|provider-|auth-degraded|quota-exhausted"
)
UPSTREAM_HINTS = [
    "has no delivery subscriptions",
    "consensus.dead_letter has no producer",
    "schema validation passed with 1 warnings",
]


def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def run(command: list[str], *, timeout: int = 900) -> dict[str, Any]:
    completed = subprocess.run(
        command,
        cwd=REPO,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )
    return {
        "command": command,
        "returncode": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
        "ok": completed.returncode == 0,
    }


def run_json(command: list[str], *, timeout: int = 900) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    result = run(command, timeout=timeout)
    if not result["ok"]:
        return None, result
    try:
        return json.loads(result["stdout"]), result
    except json.JSONDecodeError as exc:
        result["ok"] = False
        result["parse_error"] = str(exc)
        return None, result


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip():
            continue
        row = json.loads(line)
        row["_line"] = line_number
        rows.append(row)
    return rows


def quality_check() -> dict[str, Any]:
    errors: list[str] = []
    rows_summary: list[dict[str, Any]] = []
    for path in (RESEARCH_RUN, CLAIM_STATE):
        rows = read_jsonl(path)
        if not rows:
            errors.append(f"{path.relative_to(REPO)}: missing or empty")
        for row in rows:
            label = row.get("candidate_action_id") or row.get("claim_id") or row.get("id")
            encoded = json.dumps(row, ensure_ascii=False, sort_keys=True)
            row_errors = []
            if row.get("target") != "SAIR-EQT2":
                row_errors.append(f"target={row.get('target')!r}")
            for term in ("Israel", "Tolmetes", "omega-open-problem"):
                if term in encoded:
                    row_errors.append(f"forbidden term {term}")
            if path.name == "claim_state.jsonl" and "FKST consensus as mathematical proof" not in encoded:
                row_errors.append("missing proof-boundary")
            if path.name == "research_run.jsonl" and row.get("checker_status") not in {"checked", "timeout"}:
                row_errors.append(f"checker_status={row.get('checker_status')!r}")
            for item in row_errors:
                errors.append(f"{path.relative_to(REPO)}:{row['_line']}: {item}")
            rows_summary.append(
                {
                    "path": str(path.relative_to(REPO)),
                    "line": row["_line"],
                    "label": label,
                    "state": row.get("state"),
                    "checker_status": row.get("checker_status"),
                    "has_must_not_claim": "must_not_claim" in row,
                    "errors": row_errors,
                }
            )
    return {
        "ok": not errors,
        "errors": errors,
        "rows": rows_summary,
    }


def scan_error_patterns(limit: int = 40) -> dict[str, Any]:
    matches: list[dict[str, Any]] = []
    for source in ERROR_SOURCES:
        paths = []
        if source.is_dir():
            paths = sorted(source.rglob("*.log"))
        elif source.exists():
            paths = [source]
        for path in paths:
            try:
                lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
            except OSError as exc:
                matches.append({"path": str(path), "line": 0, "text": f"read failed: {exc}"})
                continue
            for line_number, line in enumerate(lines, start=1):
                if ERROR_PATTERN.search(line):
                    matches.append({"path": str(path), "line": line_number, "text": line[:1000]})
                    if len(matches) >= limit:
                        return {"ok": False, "matches": matches, "truncated": True}
    return {"ok": not matches, "matches": matches, "truncated": False}


def dry_run_compare() -> dict[str, Any]:
    return run([sys.executable, str(DRY_RUN)], timeout=900)


def regenerate_claim_state() -> dict[str, Any]:
    return run(
        [
            sys.executable,
            str(DRY_RUN),
            "--output",
            str(CLAIM_STATE),
            "--no-compare",
        ],
        timeout=900,
    )


def restart_supervisor() -> dict[str, Any]:
    return run(["launchctl", "kickstart", "-k", f"gui/{os.getuid()}/{LABEL}"], timeout=60)


def classify_issue_candidates(record: dict[str, Any]) -> list[dict[str, Any]]:
    candidates: list[dict[str, Any]] = []
    search_text = json.dumps(record, ensure_ascii=False, sort_keys=True)
    for hint in UPSTREAM_HINTS:
        if hint in search_text:
            candidates.append(
                {
                    "schema": "omega.sair_eqt2.fkst_issue_candidate.v1",
                    "detected_at": record["checked_at"],
                    "target": "SAIR-EQT2",
                    "status": "needs-user-confirmation-before-upstream-issue",
                    "hint": hint,
                    "suggested_labels": ["bug"],
                    "boundary": (
                        "This is a candidate only. Do not file upstream without "
                        "explicit user confirmation."
                    ),
                }
            )
    return candidates


def write_jsonl(path: Path, row: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def render_report(record: dict[str, Any]) -> str:
    status = record["status"]
    health = record.get("status_report", {})
    ledger = (health.get("ledger") or {}) if isinstance(health, dict) else {}
    quality = record.get("quality", {})
    errors = record.get("errors", [])
    actions = record.get("actions", [])
    lines = [
        "# SAIR-EQT2 FKST Patrol Report",
        "",
        f"- last_checked_at: `{record['checked_at']}`",
        f"- status: `{status}`",
        f"- target: `SAIR-EQT2`",
        f"- github_write: `disabled`",
        f"- ledger_samples: `{ledger.get('samples', 'n/a')}`",
        f"- runtime_age_seconds: `{ledger.get('final_runtime_age_seconds', 'n/a')}`",
        f"- quality_ok: `{str(quality.get('ok')).lower()}`",
        f"- error_pattern_matches: `{len(record.get('error_scan', {}).get('matches', []))}`",
        "",
        "## Latest Actions",
    ]
    if actions:
        lines.extend(f"- `{item['action']}`: `{item['status']}`" for item in actions)
    else:
        lines.append("- none")
    lines.extend(["", "## Errors"])
    if errors:
        lines.extend(f"- {item}" for item in errors[:40])
    else:
        lines.append("- none")
    lines.extend(["", "## Boundaries"])
    lines.extend(
        [
            "- FKST consensus is not mathematical proof.",
            "- Mathematical truth must come from Lean/checker/source-replay/git artifacts.",
            "- GitHub write automation remains disabled.",
            "- Upstream FKST issues are recorded as local candidates only until user confirms filing.",
        ]
    )
    return "\n".join(lines) + "\n"


def patrol_once() -> dict[str, Any]:
    actions: list[dict[str, Any]] = []
    errors: list[str] = []
    status_report, status_result = run_json(
        [
            sys.executable,
            str(STATUS_REPORT),
            "--append-current",
            "--json",
            "--output",
            "/tmp/fkst-sair-eqt2-patrol-status.json",
        ],
        timeout=900,
    )
    if status_report is None or status_report.get("status") != "ok":
        errors.append("status_report failed or not ok")
        restart = restart_supervisor()
        actions.append(
            {
                "action": "restart-supervisor",
                "status": "ok" if restart["ok"] else "failed",
                "returncode": restart["returncode"],
            }
        )
        if not restart["ok"]:
            errors.append((restart["stderr"] or restart["stdout"]).strip()[:1000])

    compare = dry_run_compare()
    if not compare["ok"]:
        errors.append("claim-state dry-run compare failed")
        repair = regenerate_claim_state()
        actions.append(
            {
                "action": "regenerate-claim-state",
                "status": "ok" if repair["ok"] else "failed",
                "returncode": repair["returncode"],
            }
        )
        if repair["ok"]:
            compare = dry_run_compare()
            if not compare["ok"]:
                errors.append("claim-state compare still failed after regeneration")
        else:
            errors.append((repair["stderr"] or repair["stdout"]).strip()[:1000])

    quality = quality_check()
    if not quality["ok"]:
        errors.extend(quality["errors"])

    error_scan = scan_error_patterns()
    if not error_scan["ok"]:
        errors.append("runtime error patterns matched")

    record = {
        "schema": "omega.sair_eqt2.patrol.v1",
        "checked_at": utc_now(),
        "target": "SAIR-EQT2",
        "status": "ok" if not errors else "needs_attention",
        "github_write": "disabled",
        "status_report": status_report,
        "status_result": {
            "returncode": status_result["returncode"],
            "ok": status_result["ok"],
            "stderr_excerpt": status_result["stderr"][:2000],
            "stdout_excerpt": status_result["stdout"][:2000],
        },
        "dry_run_compare": {
            "returncode": compare["returncode"],
            "ok": compare["ok"],
            "stderr_excerpt": compare["stderr"][:2000],
            "stdout_excerpt": compare["stdout"][:2000],
        },
        "quality": quality,
        "error_scan": error_scan,
        "actions": actions,
        "errors": errors,
    }
    issue_candidates = classify_issue_candidates(record)
    record["issue_candidates"] = issue_candidates

    write_jsonl(PATROL_JSONL, record)
    for candidate in issue_candidates:
        write_jsonl(ISSUE_CANDIDATES, candidate)
    PATROL_REPORT.write_text(render_report(record), encoding="utf-8")
    return record


def install_launchagent(interval_seconds: int) -> None:
    plist = {
        "Label": PATROL_LABEL,
        "ProgramArguments": [
            sys.executable,
            str(Path(__file__).resolve()),
        ],
        "WorkingDirectory": str(REPO),
        "StandardOutPath": str(PATROL_STDOUT),
        "StandardErrorPath": str(PATROL_STDERR),
        "StartInterval": interval_seconds,
        "RunAtLoad": True,
        "EnvironmentVariables": {
            "PATH": "/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin",
            "PYTHONDONTWRITEBYTECODE": "1",
        },
    }
    PATROL_PLIST.write_bytes(plistlib.dumps(plist, fmt=plistlib.FMT_XML))
    subprocess.run(
        ["launchctl", "bootout", f"gui/{os.getuid()}", str(PATROL_PLIST)],
        check=False,
        text=True,
        capture_output=True,
    )
    bootstrap = subprocess.run(
        ["launchctl", "bootstrap", f"gui/{os.getuid()}", str(PATROL_PLIST)],
        check=False,
        text=True,
        capture_output=True,
    )
    if bootstrap.returncode != 0:
        raise SystemExit(
            f"launchctl bootstrap failed: {bootstrap.stderr or bootstrap.stdout}"
        )
    kickstart = subprocess.run(
        ["launchctl", "kickstart", "-k", f"gui/{os.getuid()}/{PATROL_LABEL}"],
        check=False,
        text=True,
        capture_output=True,
    )
    if kickstart.returncode != 0:
        raise SystemExit(
            f"launchctl kickstart failed: {kickstart.stderr or kickstart.stdout}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--install-launchagent", action="store_true")
    parser.add_argument("--interval-seconds", type=int, default=1800)
    parser.add_argument("--once-json", action="store_true")
    args = parser.parse_args()

    if args.install_launchagent:
        install_launchagent(args.interval_seconds)
        print(f"installed: {PATROL_LABEL}")
        print(f"interval_seconds: {args.interval_seconds}")
        print(f"plist: {PATROL_PLIST}")
        print(f"jsonl: {PATROL_JSONL}")
        print(f"report: {PATROL_REPORT}")
        return

    record = patrol_once()
    if args.once_json:
        print(json.dumps(record, ensure_ascii=False, indent=2, sort_keys=True))
    else:
        print(f"target: SAIR-EQT2")
        print(f"checked_at: {record['checked_at']}")
        print(f"status: {record['status']}")
        print(f"actions: {len(record['actions'])}")
        print(f"errors: {len(record['errors'])}")
        print(f"jsonl: {PATROL_JSONL}")
        print(f"report: {PATROL_REPORT}")


if __name__ == "__main__":
    main()
