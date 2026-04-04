#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Contract helpers for the paper experiment pipeline."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence

from automation_paths import export_dir, paper_root


CONTRACT_SCHEMA_VERSION = "omega-run-all-contract-v1"
REQUIRED_CONTRACT_FILES: tuple[str, ...] = (
    "run_all_manifest.json",
    "run_all_contract_report.json",
    "run_all_contract_report.md",
    "run_all_timing.json",
)


@dataclass
class ContractValidationResult:
    ok: bool
    errors: list[str]
    missing_files: list[str]


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _nonempty(path: Path) -> bool:
    return path.is_file() and path.stat().st_size > 0


def build_run_manifest(
    *,
    run_id: str,
    force: bool,
    no_cache: bool,
    total_elapsed_s: float,
    step_records: Sequence[dict[str, Any]],
    timing_relpath: str,
) -> dict[str, Any]:
    ran = [record for record in step_records if record.get("status") == "ran"]
    skipped = [record for record in step_records if str(record.get("status", "")).startswith("skipped_")]
    return {
        "schema_version": CONTRACT_SCHEMA_VERSION,
        "pipeline": "omega-run-all",
        "run_id": run_id,
        "paper_root": str(paper_root()),
        "force": bool(force),
        "no_cache": bool(no_cache),
        "total_elapsed_s": float(total_elapsed_s),
        "timing_relpath": timing_relpath,
        "required_artifacts": list(REQUIRED_CONTRACT_FILES),
        "steps_total": len(step_records),
        "steps_ran": len(ran),
        "steps_skipped": len(skipped),
        "steps": list(step_records),
        "generated_at": _utc_now_iso(),
    }


def _collect_missing_outputs(
    *,
    root: Path,
    steps: Sequence[dict[str, Any]],
) -> list[dict[str, str]]:
    missing: list[dict[str, str]] = []
    for step in steps:
        step_name = str(step.get("name", ""))
        for rel in step.get("expected_outputs", []):
            rel_path = str(rel)
            if not _nonempty(root / rel_path):
                missing.append({"step": step_name, "path": rel_path})
    return missing


def build_contract_report(
    *,
    manifest: dict[str, Any],
) -> dict[str, Any]:
    root = Path(str(manifest["paper_root"]))
    missing_outputs = _collect_missing_outputs(root=root, steps=manifest.get("steps", []))
    timing_relpath = str(manifest.get("timing_relpath", ""))
    timing_ok = bool(timing_relpath) and _nonempty(root / timing_relpath)
    artifacts_complete = len(missing_outputs) == 0 and timing_ok
    failure_reasons: list[str] = []
    if missing_outputs:
        failure_reasons.append(
            f"{len(missing_outputs)} expected step outputs are missing or empty."
        )
    if not timing_ok:
        failure_reasons.append("run_all_timing.json is missing or empty.")

    return {
        "schema_version": CONTRACT_SCHEMA_VERSION,
        "pipeline": "omega-run-all",
        "run_id": manifest["run_id"],
        "paper_root": manifest["paper_root"],
        "artifacts_complete": artifacts_complete,
        "pass_fail": "pass" if artifacts_complete else "fail",
        "steps_total": manifest.get("steps_total", 0),
        "steps_ran": manifest.get("steps_ran", 0),
        "steps_skipped": manifest.get("steps_skipped", 0),
        "missing_outputs_total": len(missing_outputs),
        "missing_outputs": missing_outputs,
        "failure_reasons": failure_reasons,
        "timing_relpath": timing_relpath,
        "generated_at": _utc_now_iso(),
    }


def render_contract_report_markdown(
    *,
    manifest: dict[str, Any],
    report: dict[str, Any],
) -> str:
    lines = [
        "# Run-All Contract Report",
        "",
        "## Summary",
        f"- Run ID: {report.get('run_id', '')}",
        f"- Pipeline: {report.get('pipeline', '')}",
        f"- Result: {report.get('pass_fail', 'fail')}",
        f"- Artifacts Complete: {report.get('artifacts_complete', False)}",
        f"- Steps Total: {report.get('steps_total', 0)}",
        f"- Steps Ran: {report.get('steps_ran', 0)}",
        f"- Steps Skipped: {report.get('steps_skipped', 0)}",
        f"- Total Elapsed (s): {float(manifest.get('total_elapsed_s', 0.0)):.3f}",
        "",
        "## Required Contract Files",
    ]
    for name in REQUIRED_CONTRACT_FILES:
        lines.append(f"- {name}")

    lines.extend(["", "## Missing Outputs"])
    missing_outputs = report.get("missing_outputs", [])
    if missing_outputs:
        for item in missing_outputs:
            lines.append(f"- {item['step']}: {item['path']}")
    else:
        lines.append("- None")

    lines.extend(["", "## Step Status"])
    for step in manifest.get("steps", []):
        elapsed = float(step.get("elapsed_s", 0.0))
        lines.append(
            f"- {step.get('name', '')}: {step.get('status', '')} "
            f"(elapsed_s={elapsed:.3f})"
        )

    if report.get("failure_reasons"):
        lines.extend(["", "## Failure Reasons"])
        for reason in report["failure_reasons"]:
            lines.append(f"- {reason}")

    lines.append("")
    return "\n".join(lines)


def write_contract_outputs(
    *,
    manifest: dict[str, Any],
    report: dict[str, Any],
    output_dir: Path | None = None,
) -> None:
    out_dir = output_dir or export_dir()
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "run_all_manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    (out_dir / "run_all_contract_report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    (out_dir / "run_all_contract_report.md").write_text(
        render_contract_report_markdown(manifest=manifest, report=report),
        encoding="utf-8",
    )


def validate_contract_artifacts(root: Path | None = None) -> ContractValidationResult:
    base = root or export_dir()
    errors: list[str] = []
    missing_files = [name for name in REQUIRED_CONTRACT_FILES if not _nonempty(base / name)]
    for name in missing_files:
        errors.append(f"Missing required contract file: {name}")

    manifest_path = base / "run_all_manifest.json"
    report_path = base / "run_all_contract_report.json"
    manifest: dict[str, Any] | None = None
    report: dict[str, Any] | None = None

    if manifest_path.exists():
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            errors.append(f"run_all_manifest.json invalid JSON: {exc}")
    if report_path.exists():
        try:
            report = json.loads(report_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            errors.append(f"run_all_contract_report.json invalid JSON: {exc}")

    if manifest is not None and manifest.get("schema_version") != CONTRACT_SCHEMA_VERSION:
        errors.append("Manifest schema_version mismatch")
    if report is not None and report.get("schema_version") != CONTRACT_SCHEMA_VERSION:
        errors.append("Report schema_version mismatch")

    if manifest is not None:
        expected = manifest.get("required_artifacts", [])
        if sorted(expected) != sorted(REQUIRED_CONTRACT_FILES):
            errors.append("Manifest required_artifacts mismatch")
        missing_outputs = _collect_missing_outputs(
            root=Path(str(manifest.get("paper_root", paper_root()))),
            steps=manifest.get("steps", []),
        )
    else:
        missing_outputs = []

    if report is not None:
        artifacts_complete = bool(report.get("artifacts_complete", False))
        actual_complete = len(missing_outputs) == 0 and len(missing_files) == 0
        if artifacts_complete != actual_complete:
            errors.append(
                "Report artifacts_complete mismatch "
                f"(reported={artifacts_complete}, actual={actual_complete})"
            )
        if actual_complete and report.get("pass_fail") != "pass":
            errors.append("Report pass_fail should be pass when artifacts are complete")
        if (not actual_complete) and report.get("pass_fail") != "fail":
            errors.append("Report pass_fail should be fail when artifacts are incomplete")

    return ContractValidationResult(
        ok=len(errors) == 0,
        errors=errors,
        missing_files=missing_files,
    )


def cmd_validate(_: argparse.Namespace) -> int:
    result = validate_contract_artifacts()
    print(
        "[pipeline-contract] validate:"
        f" ok={result.ok}"
        f" missing_files={len(result.missing_files)}"
        f" errors={len(result.errors)}"
    )
    for error in result.errors[:50]:
        print(f"  {error}")
    return 0 if result.ok else 1


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Validate run_all contract artifacts")
    sub = p.add_subparsers(dest="command", required=True)
    validate_p = sub.add_parser("validate", help="Validate run_all contract outputs")
    validate_p.set_defaults(func=cmd_validate)
    return p


def main() -> int:
    args = parser().parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
