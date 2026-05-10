#!/usr/bin/env python3
"""Scan configured Automath/NewMath bridge sources and emit candidate records.

The scanner is read-only with respect to source repositories. It checks whether
configured paths exist at the local checkout, records the local commit for the
configured ref, and writes JSONL records that can be reviewed by an operator.
It does not sync, accept, consume, push, or publish bridge material.
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
DEFAULT_CONFIG = SCRIPT_DIR / "bridge_sources.json"
DEFAULT_OUTPUT = SCRIPT_DIR / "out" / "bridge_candidates.jsonl"


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def _load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"Expected object JSON in {path}")
    return data


def _run_git(repo: Path, args: list[str]) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=str(repo),
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        detail = proc.stderr.strip() or proc.stdout.strip()
        raise RuntimeError(f"git {' '.join(args)} failed in {repo}: {detail}")
    return proc.stdout.strip()


def _resolve_repo_path(raw: str, config_path: Path) -> Path:
    path = Path(raw)
    if not path.is_absolute():
        path = (config_path.parent / path).resolve()
        if not (path / ".git").exists():
            path = (REPO_ROOT / raw).resolve()
    return path


def _repo_commit(repo_path: Path, ref: str) -> str:
    return _run_git(repo_path, ["rev-parse", ref])


def _repo_branch(repo_path: Path) -> str:
    try:
        return _run_git(repo_path, ["branch", "--show-current"])
    except RuntimeError:
        return ""


def _record_id(source_id: str, source_commit: str, destination_ref: str) -> str:
    digest = hashlib.sha1(f"{source_id}|{source_commit}|{destination_ref}".encode("utf-8")).hexdigest()[:12]
    return f"candidate:{source_id}:{digest}"


def _path_status(repo_path: Path, rel_path: str) -> tuple[bool, str]:
    path = repo_path / rel_path
    if path.exists():
        return True, "exists"
    return False, "missing"


def build_records(config_path: Path) -> list[dict[str, Any]]:
    config = _load_json(config_path)
    repos = config.get("repositories")
    sources = config.get("sources")
    if not isinstance(repos, dict):
        raise ValueError("config.repositories must be an object")
    if not isinstance(sources, list):
        raise ValueError("config.sources must be a list")

    repo_meta: dict[str, dict[str, Any]] = {}
    for key, raw in repos.items():
        if not isinstance(raw, dict):
            raise ValueError(f"repository {key} must be an object")
        local_path = _resolve_repo_path(str(raw.get("local_path", "")), config_path)
        repo_meta[key] = {
            **raw,
            "local_path_resolved": local_path,
            "current_branch": _repo_branch(local_path),
        }

    now = _now_iso()
    records: list[dict[str, Any]] = []
    for item in sources:
        if not isinstance(item, dict):
            raise ValueError("each source item must be an object")
        source_key = str(item.get("source_repo_key", ""))
        dest_key = str(item.get("destination_repo_key", ""))
        if source_key not in repo_meta:
            raise ValueError(f"unknown source_repo_key: {source_key}")
        if dest_key not in repo_meta:
            raise ValueError(f"unknown destination_repo_key: {dest_key}")

        source_repo = repo_meta[source_key]
        dest_repo = repo_meta[dest_key]
        source_ref = str(item.get("source_ref") or source_repo.get("default_ref") or "HEAD")
        dest_ref = str(item.get("destination_ref") or dest_repo.get("bridge_ref") or dest_repo.get("default_ref") or "HEAD")
        source_path = str(item.get("source_path") or "")
        exists, path_status = _path_status(source_repo["local_path_resolved"], source_path)
        source_commit = _repo_commit(source_repo["local_path_resolved"], source_ref)
        status = str(item.get("status") or "observed")
        notes = str(item.get("notes") or "")
        if not exists:
            status = "blocked"
            notes = (notes + " " if notes else "") + f"Scanner could not find source_path locally: {source_path}"

        taste_gate_required = bool(item.get("taste_gate_required", False))
        audit_boundary = str(item.get("audit_boundary") or "")
        if not audit_boundary:
            if taste_gate_required:
                audit_boundary = (
                    "TasteGate witness and destination-specific audit remain "
                    "required before writeback or promotion."
                )
            else:
                audit_boundary = (
                    "Destination-specific audit remains required before "
                    "writeback or promotion."
                )

        record = {
            "id": _record_id(str(item.get("id")), source_commit, dest_ref),
            "record_version": 1,
            "created_at": now,
            "source_repo": str(source_repo.get("repo")),
            "source_branch_or_ref": source_ref,
            "source_path": source_path,
            "source_commit": source_commit,
            "source_artifact_kind": str(item.get("source_artifact_kind")),
            "destination_repo": str(dest_repo.get("repo")),
            "destination_branch_or_ref": dest_ref,
            "destination_path": str(item.get("destination_path") or ""),
            "destination_artifact_kind": str(item.get("destination_artifact_kind")),
            "bridge_direction": str(item.get("bridge_direction")),
            "status": status,
            "operator_review_required": bool(item.get("operator_review_required", True)),
            "taste_gate_required": taste_gate_required,
            "audit_required": bool(item.get("audit_required", True)),
            "external_publication_risk": str(item.get("external_publication_risk") or "none"),
            "review_boundary": str(item.get("review_boundary") or "Operator review required before accepted or consumed status."),
            "audit_boundary": audit_boundary,
            "notes": notes,
            "next_action": str(item.get("next_action") or "operator review"),
            "scan": {
                "source_local_path": str(source_repo["local_path_resolved"]),
                "source_path_status": path_status,
                "source_current_branch": source_repo.get("current_branch", ""),
                "destination_local_path": str(dest_repo["local_path_resolved"]),
                "destination_current_branch": dest_repo.get("current_branch", ""),
            },
        }
        records.append(record)
    return records


def write_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Scan Automath-NewMath bridge sources")
    parser.add_argument("--config", default=str(DEFAULT_CONFIG), help="bridge source config JSON")
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT), help="candidate packet JSONL")
    parser.add_argument("--no-write", action="store_true", help="print records without writing output")
    args = parser.parse_args(argv)

    config_path = Path(args.config).resolve()
    records = build_records(config_path)
    if args.no_write:
        for record in records:
            print(json.dumps(record, ensure_ascii=False, sort_keys=True))
    else:
        output_path = Path(args.output)
        write_jsonl(output_path, records)
        print(f"[bridge-scan] wrote {len(records)} records to {output_path}")
    missing = [r for r in records if r.get("scan", {}).get("source_path_status") != "exists"]
    if missing:
        print(f"[bridge-scan] warning: {len(missing)} source path(s) missing", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
