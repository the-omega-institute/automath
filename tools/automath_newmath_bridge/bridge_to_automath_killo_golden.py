#!/usr/bin/env python3
"""Select NewMath-to-Automath bridge records for Automath-native writeback.

The adapter does not generate LaTeX itself. It converts an already gate-passed
bridge record into an Automath distillation source candidate, then invokes the
existing `tools/distillation/supervisor.py` lane. That keeps Killo/golden
style, Claude review, writeback validation, and application planning inside the
Automath-native pipeline.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_GATE_RESULTS = SCRIPT_DIR / "out" / "bridge_gate_results.jsonl"
DEFAULT_RUNTIME_DIR = SCRIPT_DIR / "inbox" / "automath_writeback_candidates"
DEFAULT_BRANCH = "bridge/automath-newmath-consumption"


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def _git(args: list[str], *, timeout: int = 120) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )


def _git_stdout(args: list[str], *, timeout: int = 120) -> str:
    result = _git(args, timeout=timeout)
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout or "git command failed").strip())
    return result.stdout.strip()


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            text = line.strip()
            if not text:
                continue
            item = json.loads(text)
            if not isinstance(item, dict):
                raise ValueError(f"{path}:{line_no}: expected object")
            rows.append(item)
    return rows


def _safe_slug(text: str, *, limit: int = 80) -> str:
    cleaned = "".join(ch.lower() if ch.isalnum() else "-" for ch in text)
    cleaned = "-".join(part for part in cleaned.split("-") if part)
    return cleaned[:limit].strip("-") or "newmath-bridge"


def _digest(record: dict[str, Any]) -> str:
    payload = json.dumps(
        {
            "artifact_key": record.get("artifact_key"),
            "source_commit": record.get("source_commit"),
            "source_path": record.get("source_path"),
        },
        sort_keys=True,
    )
    return hashlib.sha1(payload.encode("utf-8")).hexdigest()[:12]


def _eligible(record: dict[str, Any]) -> bool:
    if record.get("bridge_direction") != "newmath_to_automath":
        return False
    if record.get("gate_status") != "gate_passed":
        return False
    if record.get("destination_repo") != "the-omega-institute/automath":
        return False
    if record.get("readiness") in {"blocked_automath_not_ready", "observe_only"}:
        return False
    if record.get("operator_review_required") and record.get("status") not in {"accepted", "consumed"}:
        return False
    return True


def _candidate_name(record: dict[str, Any]) -> str:
    source_path = str(record.get("source_path") or record.get("artifact_key") or "NewMath bridge")
    stem = Path(source_path).stem.replace("_", " ").replace("-", " ").strip()
    return f"NewMath bridge source: {stem}"


def _candidate_payload(record: dict[str, Any]) -> dict[str, Any]:
    source = f"{record.get('source_repo')}@{record.get('source_branch_or_ref')}:{record.get('source_path')}"
    evidence = record.get("evidence_summary")
    if not isinstance(evidence, list):
        evidence = []
    return {
        "schema_version": "automath-newmath-automath-writeback-candidate-v1",
        "created_at": _now_iso(),
        "status": "ready_for_automath_distillation_supervisor",
        "distillation_source_name": _candidate_name(record),
        "bridge_source": source,
        "bridge_record": record,
        "source_queue_candidate": {
            "status": "open",
            "priority": int(record.get("priority") or 70),
            "proposed_source": _candidate_name(record),
            "source_type": "bridge_packet",
            "origin": "automath_newmath_bridge",
            "target_sections": ["killo-golden", "omega paper writeback"],
            "omega_mechanisms": ["killo-golden", "NewMath bridge evidence"],
            "fit_score": 8,
            "novelty_score": 6,
            "rationale": (
                "NewMath-to-Automath bridge record passed deterministic bridge gates "
                "and operator status is accepted/consumed. Automath distillation must "
                "still perform Killo/golden validation, Claude review, and writeback "
                "application planning."
            ),
            "source_material": [source, *[str(item) for item in evidence]],
            "risks": [
                "Do not copy NewMath BEDC text verbatim.",
                "Do not expose bridge runtime packet metadata in paper LaTeX.",
                "Do not write unless Automath distillation review accepts the writeback.",
            ],
            "first_distillation_prompt": (
                "Use this NewMath bridge source as mathematical evidence only. "
                "Find an Automath-native Killo/golden receiving context, produce at "
                "most one conservative theorem-level paper writeback, and obey the "
                "existing killo-golden style and review gate."
            ),
            "next_step": "distill_source",
        },
    }


def build_candidates(records: list[dict[str, Any]], runtime_dir: Path, *, limit: int) -> list[Path]:
    runtime_dir.mkdir(parents=True, exist_ok=True)
    written: list[Path] = []
    for record in records:
        if len(written) >= limit:
            break
        if not _eligible(record):
            continue
        source_path = str(record.get("source_path") or "newmath-bridge")
        path = runtime_dir / f"{_safe_slug(source_path)}-{_digest(record)}.json"
        path.write_text(json.dumps(_candidate_payload(record), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        written.append(path)
    return written


def run_distillation_supervisor(
    *,
    branch: str,
    name: str,
    dry_run: bool,
    push_branch: bool,
    oracle_research: bool,
    oracle_deepening: bool,
) -> dict[str, Any]:
    cmd = [
        sys.executable,
        "tools/distillation/supervisor.py",
        "--branch",
        branch,
        "--once",
        "--no-sync-dev",
        "--no-refresh-source-queue",
        "--name",
        name,
        "--review-backend",
        "codex-claude",
    ]
    if dry_run:
        cmd.append("--dry-run")
    if oracle_research:
        cmd.append("--oracle-research")
    if oracle_deepening:
        cmd.append("--oracle-deepening")
    result = subprocess.run(cmd, cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=7200, check=False)
    out = {
        "status": "ran" if result.returncode == 0 else "failed",
        "returncode": result.returncode,
        "stdout_tail": result.stdout[-3000:],
        "stderr_tail": result.stderr[-3000:],
    }
    if result.returncode == 0 and push_branch and not dry_run:
        push = _git(["push", "origin", branch], timeout=300)
        out["push"] = {
            "status": "pushed" if push.returncode == 0 else "failed",
            "stdout_tail": push.stdout[-1000:],
            "stderr_tail": push.stderr[-1000:],
        }
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Automath-native Killo/golden writeback for accepted bridge records")
    parser.add_argument("--gate-results", default=str(DEFAULT_GATE_RESULTS))
    parser.add_argument("--runtime-dir", default=str(DEFAULT_RUNTIME_DIR))
    parser.add_argument("--branch", default=DEFAULT_BRANCH)
    parser.add_argument("--limit", type=int, default=1)
    parser.add_argument("--apply", action="store_true", help="Invoke Automath distillation supervisor")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--push-branch", action="store_true", help="Push the Automath bridge branch after successful writeback")
    parser.add_argument("--oracle-research", action="store_true")
    parser.add_argument("--oracle-deepening", action="store_true")
    args = parser.parse_args(argv)

    branch = _git_stdout(["branch", "--show-current"], timeout=30)
    if branch != args.branch:
        raise RuntimeError(f"Refusing to run on branch {branch!r}; expected {args.branch!r}")

    records = _read_jsonl(Path(args.gate_results))
    paths = build_candidates(records, Path(args.runtime_dir), limit=max(0, args.limit))
    summary: dict[str, Any] = {
        "candidate_packets": [str(path.relative_to(REPO_ROOT)) for path in paths],
        "apply": bool(args.apply),
        "push_branch": bool(args.push_branch),
    }
    if not paths:
        print(json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True))
        return 0
    if args.apply:
        payload = json.loads(paths[0].read_text(encoding="utf-8"))
        name = str(payload["distillation_source_name"])
        summary["distillation"] = run_distillation_supervisor(
            branch=args.branch,
            name=name,
            dry_run=args.dry_run,
            push_branch=args.push_branch,
            oracle_research=args.oracle_research,
            oracle_deepening=args.oracle_deepening,
        )
    print(json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True))
    distillation = summary.get("distillation")
    if isinstance(distillation, dict) and distillation.get("status") == "failed":
        return 1
    if isinstance(distillation, dict):
        push = distillation.get("push")
        if isinstance(push, dict) and push.get("status") == "failed":
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
