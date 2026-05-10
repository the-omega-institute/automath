#!/usr/bin/env python3
"""Run the growth-aware Automath-NewMath bridge pipeline.

This runner discovers bridgeable artifacts from both repositories by reading
configured Git refs, compares them with local bridge state, synthesizes
cross-repo readiness, emits an inbox of candidate transfer records, and renders
a transfer plan. It is intentionally non-destructive: it does not modify source
repos, accept proposals, apply writebacks, publish, send, push, or merge.
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from bridge_synthesis import build_repo_snapshot, synthesize_records
except ModuleNotFoundError:  # pragma: no cover
    from tools.automath_newmath_bridge.bridge_synthesis import build_repo_snapshot, synthesize_records


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_CONFIG = SCRIPT_DIR / "bridge_pipeline_config.json"
DEFAULT_EVENT_LOG = SCRIPT_DIR / "state" / "bridge_events.jsonl"
DEFAULT_QUEUE = SCRIPT_DIR / "out" / "bridge_agent_queue.jsonl"
SUPPRESS_STATUSES = {"consumed", "rejected", "blocked"}


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def _json(data: Any) -> str:
    return json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True)


def _load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8-sig") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"Expected object JSON in {path}")
    return data


def _load_json_or_default(path: Path, default: dict[str, Any]) -> dict[str, Any]:
    if not path.exists():
        return default
    return _load_json(path)


def _write_json(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(_json(data) + "\n", encoding="utf-8")


def _write_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def _run_git(repo: Path, args: list[str]) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=str(repo),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        detail = proc.stderr.strip() or proc.stdout.strip()
        raise RuntimeError(f"git {' '.join(args)} failed in {repo}: {detail}")
    return proc.stdout


def _resolve_repo_path(raw: str, config_path: Path) -> Path:
    path = Path(raw)
    if not path.is_absolute():
        path = (config_path.parent / path).resolve()
        if not (path / ".git").exists():
            path = (REPO_ROOT / raw).resolve()
    return path


def _repo_branch(repo_path: Path) -> str:
    return _run_git(repo_path, ["branch", "--show-current"]).strip()


def _repo_commit(repo_path: Path, ref: str) -> str:
    return _run_git(repo_path, ["rev-parse", ref]).strip()


def _repo_blob(repo_path: Path, ref: str, rel_path: str) -> str:
    try:
        return _run_git(repo_path, ["rev-parse", f"{ref}:{rel_path}"]).strip()
    except RuntimeError:
        return ""


def _ls_tree(repo_path: Path, ref: str) -> list[str]:
    out = _run_git(repo_path, ["ls-tree", "-r", "--name-only", ref])
    return [line.strip() for line in out.splitlines() if line.strip()]


def _show_text(repo_path: Path, ref: str, rel_path: str, *, limit: int = 2_000_000) -> str:
    proc = subprocess.run(
        ["git", "show", f"{ref}:{rel_path}"],
        cwd=str(repo_path),
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        return ""
    data = proc.stdout[:limit]
    return data.decode("utf-8", errors="ignore")


def _matches_any(path: str, globs: list[str]) -> bool:
    return any(fnmatch.fnmatch(path, pattern) for pattern in globs)


def _slug_for_path(path: str) -> str:
    stem = Path(path).with_suffix("").as_posix()
    slug = re.sub(r"[^A-Za-z0-9]+", "-", stem).strip("-").lower()
    return slug[:120] or "artifact"


def _record_id(rule_id: str, source_path: str, source_commit: str, direction: str) -> str:
    digest = hashlib.sha1(
        f"{rule_id}|{source_path}|{source_commit}|{direction}".encode("utf-8")
    ).hexdigest()[:16]
    return f"inbox:{rule_id}:{digest}"


def _artifact_key(source_repo: str, source_ref: str, source_path: str) -> str:
    return f"{source_repo}@{source_ref}:{source_path}"


def _candidate_hash(record: dict[str, Any]) -> str:
    payload = {
        "source_repo": record.get("source_repo"),
        "source_path": record.get("source_path"),
        "source_blob": record.get("source_blob"),
        "destination_repo": record.get("destination_repo"),
        "destination_artifact_kind": record.get("destination_artifact_kind"),
        "bridge_direction": record.get("bridge_direction"),
        "discovery_rule": record.get("discovery_rule"),
    }
    return hashlib.sha1(json.dumps(payload, sort_keys=True).encode("utf-8")).hexdigest()[:20]


def _destination_path(template: str, source_path: str) -> str:
    return template.format(slug=_slug_for_path(source_path), source_path=source_path)


def _status_for(key: str, state: dict[str, Any], default_status: str) -> str:
    artifacts = state.get("artifacts", {})
    if isinstance(artifacts, dict) and key in artifacts:
        prior = artifacts[key]
        if isinstance(prior, dict):
            return str(prior.get("status") or "observed")
    return default_status


def _classify_change(key: str, source_commit: str, source_blob: str, state: dict[str, Any]) -> str:
    artifacts = state.get("artifacts", {})
    prior = artifacts.get(key) if isinstance(artifacts, dict) else None
    if not isinstance(prior, dict):
        return "new"
    prior_blob = str(prior.get("source_blob") or prior.get("last_seen_blob") or "")
    if source_blob and prior_blob:
        return "changed" if prior_blob != source_blob else "unchanged"
    if str(prior.get("source_commit", "")) != source_commit:
        return "changed"
    return "unchanged"


def _parse_iso(text: str) -> datetime | None:
    if not text:
        return None
    try:
        return datetime.fromisoformat(text.replace("Z", "+00:00"))
    except ValueError:
        return None


def _prior_for(key: str, state: dict[str, Any]) -> dict[str, Any]:
    artifacts = state.get("artifacts", {})
    prior = artifacts.get(key) if isinstance(artifacts, dict) else None
    return prior if isinstance(prior, dict) else {}


def _state_suppression(prior: dict[str, Any], source_blob: str, *, now: datetime) -> str:
    cooldown_until = _parse_iso(str(prior.get("cooldown_until") or ""))
    if cooldown_until and cooldown_until > now:
        return f"cooldown_until:{cooldown_until.isoformat()}"
    status = str(prior.get("status") or "")
    prior_blob = str(prior.get("source_blob") or prior.get("last_seen_blob") or "")
    if status in SUPPRESS_STATUSES and prior_blob and prior_blob == source_blob:
        return f"suppressed_status:{status}"
    return ""


def _priority_score(record: dict[str, Any], prior: dict[str, Any]) -> tuple[int, list[str]]:
    score = int(record.get("priority", 0) or 0)
    reasons = [f"base:{score}"]
    change_bonus = {"new": 20, "changed": 12, "unchanged": 0}.get(str(record.get("change_kind")), 0)
    if change_bonus:
        score += change_bonus
        reasons.append(f"change:+{change_bonus}")
    kind = str(record.get("source_artifact_kind") or "")
    kind_bonus = {"taste_gate_witness": 12, "lean_theorem": 10, "accepted_proposal": 8, "paper_claim": 4}.get(kind, 0)
    if kind_bonus:
        score += kind_bonus
        reasons.append(f"{kind}:+{kind_bonus}")
    if record.get("taste_gate_required"):
        score -= 5
        reasons.append("taste_gate_pending:-5")
    if str(record.get("external_publication_risk") or "none") not in {"none", "low"}:
        score -= 10
        reasons.append("publication_risk:-10")
    attempts = int(prior.get("attempt_count", 0) or 0)
    if attempts:
        penalty = min(40, attempts * 8)
        score -= penalty
        reasons.append(f"attempts:-{penalty}")
    return score, reasons


def _repo_meta(config: dict[str, Any], config_path: Path) -> dict[str, dict[str, Any]]:
    repos = config.get("repositories")
    if not isinstance(repos, dict):
        raise ValueError("config.repositories must be an object")
    meta: dict[str, dict[str, Any]] = {}
    for key, raw in repos.items():
        if not isinstance(raw, dict):
            raise ValueError(f"repository {key} must be an object")
        local_path = _resolve_repo_path(str(raw.get("local_path", "")), config_path)
        meta[key] = {
            **raw,
            "local_path_resolved": local_path,
            "current_branch": _repo_branch(local_path),
        }
    return meta


def discover_records(
    config: dict[str, Any],
    config_path: Path,
    state: dict[str, Any],
    *,
    include_unchanged: bool,
    limit_per_rule: int,
    scan_limit_per_rule: int,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    repos = _repo_meta(config, config_path)
    rules = config.get("discovery_rules")
    if not isinstance(rules, list):
        raise ValueError("config.discovery_rules must be a list")

    now = _now_iso()
    now_dt = datetime.now(timezone.utc)
    records: list[dict[str, Any]] = []
    summary: dict[str, Any] = {"rules": {}, "refs": {}}

    for key, repo in repos.items():
        ref = str(repo.get("default_ref") or "HEAD")
        try:
            summary["refs"][key] = {
                "repo": repo.get("repo"),
                "default_ref": ref,
                "default_commit": _repo_commit(repo["local_path_resolved"], ref),
                "current_branch": repo.get("current_branch", ""),
            }
        except RuntimeError as exc:
            summary["refs"][key] = {"repo": repo.get("repo"), "error": str(exc)}

    for rule in rules:
        if not isinstance(rule, dict):
            raise ValueError("each discovery rule must be an object")
        rule_id = str(rule.get("id") or "")
        source_key = str(rule.get("source_repo_key") or "")
        dest_key = str(rule.get("destination_repo_key") or "")
        if source_key not in repos:
            raise ValueError(f"{rule_id}: unknown source_repo_key {source_key}")
        if dest_key not in repos:
            raise ValueError(f"{rule_id}: unknown destination_repo_key {dest_key}")

        source_repo = repos[source_key]
        dest_repo = repos[dest_key]
        source_ref = str(rule.get("source_ref") or source_repo.get("default_ref") or "HEAD")
        dest_ref = str(rule.get("destination_ref") or dest_repo.get("default_ref") or "HEAD")
        source_commit = _repo_commit(source_repo["local_path_resolved"], source_ref)
        paths = _ls_tree(source_repo["local_path_resolved"], source_ref)
        include_globs = [str(p) for p in rule.get("include_globs", [])]
        exclude_globs = [str(p) for p in rule.get("exclude_globs", [])]
        content_regex = str(rule.get("content_regex") or "")
        content_pattern = re.compile(content_regex) if content_regex else None

        matched: list[str] = []
        skipped_content = 0
        for path in paths:
            if scan_limit_per_rule > 0 and len(matched) >= scan_limit_per_rule:
                break
            if include_globs and not _matches_any(path, include_globs):
                continue
            if exclude_globs and _matches_any(path, exclude_globs):
                continue
            if content_pattern:
                text = _show_text(source_repo["local_path_resolved"], source_ref, path)
                if not content_pattern.search(text):
                    skipped_content += 1
                    continue
            matched.append(path)

        emitted = 0
        suppressed = 0
        change_counts = {"new": 0, "changed": 0, "unchanged": 0}
        for source_path in sorted(matched):
            artifact_key = _artifact_key(str(source_repo.get("repo")), source_ref, source_path)
            source_blob = _repo_blob(source_repo["local_path_resolved"], source_ref, source_path)
            prior = _prior_for(artifact_key, state)
            suppression = _state_suppression(prior, source_blob, now=now_dt)
            change_kind = _classify_change(artifact_key, source_commit, source_blob, state)
            change_counts[change_kind] += 1
            if suppression and not include_unchanged:
                suppressed += 1
                continue
            if change_kind == "unchanged" and not include_unchanged:
                continue
            if emitted >= limit_per_rule:
                continue
            destination_path = _destination_path(str(rule.get("destination_path_template") or ""), source_path)
            taste_gate_required = bool(rule.get("taste_gate_required", False))
            audit_boundary = (
                "TasteGate witness and destination-specific audit remain required before writeback or promotion."
                if taste_gate_required
                else "Destination-specific audit remains required before writeback or promotion."
            )
            record = {
                "id": _record_id(rule_id, source_path, source_commit, str(rule.get("bridge_direction"))),
                "record_version": 1,
                "created_at": now,
                "source_repo": str(source_repo.get("repo")),
                "source_branch_or_ref": source_ref,
                "source_path": source_path,
                "source_commit": source_commit,
                "source_blob": source_blob,
                "source_artifact_kind": str(rule.get("source_artifact_kind")),
                "destination_repo": str(dest_repo.get("repo")),
                "destination_branch_or_ref": dest_ref,
                "destination_path": destination_path,
                "destination_artifact_kind": str(rule.get("destination_artifact_kind")),
                "bridge_direction": str(rule.get("bridge_direction")),
                "status": _status_for(artifact_key, state, str(rule.get("status") or "candidate")),
                "operator_review_required": bool(rule.get("operator_review_required", True)),
                "taste_gate_required": taste_gate_required,
                "audit_required": bool(rule.get("audit_required", True)),
                "external_publication_risk": str(rule.get("external_publication_risk") or "none"),
                "review_boundary": "Operator review required before accepted or consumed status.",
                "audit_boundary": audit_boundary,
                "notes": str(rule.get("notes") or ""),
                "next_action": str(rule.get("next_action") or "operator review"),
                "scan": {
                    "source_local_path": str(source_repo["local_path_resolved"]),
                    "source_path_status": "exists",
                    "source_current_branch": str(source_repo.get("current_branch", "")),
                    "destination_local_path": str(dest_repo["local_path_resolved"]),
                    "destination_current_branch": str(dest_repo.get("current_branch", "")),
                },
                "priority": int(rule.get("priority", 50) or 50),
                "change_kind": change_kind,
                "artifact_key": artifact_key,
                "discovery_rule": rule_id,
            }
            record["candidate_hash"] = _candidate_hash(record)
            priority_score, priority_reasons = _priority_score(record, prior)
            record["priority_score"] = priority_score
            record["priority_reasons"] = priority_reasons
            records.append(record)
            emitted += 1

        summary["rules"][rule_id] = {
            "matched": len(matched),
            "emitted": emitted,
            "suppressed": suppressed,
            "skipped_content": skipped_content,
            "changes": change_counts,
            "source_ref": source_ref,
            "source_commit": source_commit,
        }

    records.sort(
        key=lambda item: (
            {"new": 0, "changed": 1, "unchanged": 2}.get(str(item.get("change_kind")), 3),
            -int(item.get("priority_score", item.get("priority", 0)) or 0),
            str(item.get("source_path", "")),
        )
    )
    return records, summary


def render_transfer_plan(records: list[dict[str, Any]], summary: dict[str, Any]) -> str:
    lines = [
        "# Automath-NewMath bridge transfer plan",
        "",
        f"- Generated at: `{_now_iso()}`",
        f"- Candidate records: `{len(records)}`",
        "",
        "## Ref Snapshot",
        "",
        "| Repo key | Repo | Ref | Commit | Current branch |",
        "| --- | --- | --- | --- | --- |",
    ]
    refs = summary.get("refs", {})
    if isinstance(refs, dict):
        for key, item in sorted(refs.items()):
            if not isinstance(item, dict):
                continue
            lines.append(
                f"| `{key}` | `{item.get('repo', '')}` | `{item.get('default_ref', '')}` | "
                f"`{str(item.get('default_commit', ''))[:12]}` | `{item.get('current_branch', '')}` |"
            )

    lines.extend([
        "",
        "## Rule Summary",
        "",
        "| Rule | Matched | Emitted | Suppressed | New | Changed | Unchanged |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ])
    rules = summary.get("rules", {})
    if isinstance(rules, dict):
        for rule_id, item in sorted(rules.items()):
            if not isinstance(item, dict):
                continue
            changes = item.get("changes", {}) if isinstance(item.get("changes"), dict) else {}
            lines.append(
                f"| `{rule_id}` | {item.get('matched', 0)} | {item.get('emitted', 0)} | {item.get('suppressed', 0)} | "
                f"{changes.get('new', 0)} | {changes.get('changed', 0)} | {changes.get('unchanged', 0)} |"
            )

    lines.extend([
        "",
        "## Transfer Candidates",
        "",
        "| Priority | Score | Change | Status | Readiness | Direction | Source | Destination | Next action |",
        "| ---: | ---: | --- | --- | --- | --- | --- | --- | --- |",
    ])
    for record in records[:200]:
        synthesis = record.get("synthesis") if isinstance(record.get("synthesis"), dict) else {}
        source = (
            f"{record.get('source_repo')}@{record.get('source_branch_or_ref')}:"
            f"{record.get('source_path')}"
        )
        destination = (
            f"{record.get('destination_repo')}@{record.get('destination_branch_or_ref')}:"
            f"{record.get('destination_path')}"
        )
        row = [
            str(record.get("priority", "")),
            str(record.get("priority_score", "")),
            f"`{record.get('change_kind', '')}`",
            f"`{record.get('status', '')}`",
            f"`{synthesis.get('readiness', 'unsynthesized')}`",
            f"`{record.get('bridge_direction', '')}`",
            source,
            destination,
            str(synthesis.get("synthesis_next_action") or record.get("next_action", "")),
        ]
        lines.append("| " + " | ".join(str(cell).replace("|", "\\|") for cell in row) + " |")

    lines.extend([
        "",
        "## Gate Boundary",
        "",
        "This plan is advisory. It does not apply transfers. Records marked `candidate` or `needs_operator_review` require operator review before any destination write. NewMath AI-origin BEDC material keeps the TasteGate boundary. Automath paper/writeback material keeps the existing omega_ci, distillation review, and publication gates.",
        "",
    ])
    return "\n".join(lines)


def update_state(state: dict[str, Any], records: list[dict[str, Any]], summary: dict[str, Any]) -> dict[str, Any]:
    updated = json.loads(json.dumps(state))
    updated["version"] = int(updated.get("version", 1) or 1)
    updated["updated_at"] = _now_iso()
    updated["last_summary"] = summary
    artifacts = updated.setdefault("artifacts", {})
    if not isinstance(artifacts, dict):
        artifacts = {}
        updated["artifacts"] = artifacts
    for record in records:
        key = str(record.get("artifact_key") or "")
        if not key:
            continue
        prior = artifacts.get(key) if isinstance(artifacts.get(key), dict) else {}
        attempt_count = int(prior.get("attempt_count", 0) or 0)
        artifacts[key] = {
            "status": prior.get("status") or record.get("status"),
            "source_repo": record.get("source_repo"),
            "source_branch_or_ref": record.get("source_branch_or_ref"),
            "source_path": record.get("source_path"),
            "source_commit": record.get("source_commit"),
            "source_blob": record.get("source_blob"),
            "source_artifact_kind": record.get("source_artifact_kind"),
            "destination_repo": record.get("destination_repo"),
            "destination_branch_or_ref": record.get("destination_branch_or_ref"),
            "destination_path": record.get("destination_path"),
            "destination_artifact_kind": record.get("destination_artifact_kind"),
            "bridge_direction": record.get("bridge_direction"),
            "last_seen_at": _now_iso(),
            "last_emitted_at": _now_iso(),
            "candidate_hash": record.get("candidate_hash"),
            "priority_score": record.get("priority_score"),
            "priority_reasons": record.get("priority_reasons", []),
            "attempt_count": attempt_count + 1,
            "discovery_rule": record.get("discovery_rule"),
            "operator_review_required": record.get("operator_review_required"),
            "taste_gate_required": record.get("taste_gate_required"),
            "audit_required": record.get("audit_required"),
        }
    return updated


def append_events(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        for record in records:
            event = {
                "event": "candidate_emitted",
                "created_at": _now_iso(),
                "artifact_key": record.get("artifact_key"),
                "candidate_hash": record.get("candidate_hash"),
                "source_blob": record.get("source_blob"),
                "change_kind": record.get("change_kind"),
                "priority_score": record.get("priority_score"),
                "status": record.get("status"),
                "discovery_rule": record.get("discovery_rule"),
            }
            handle.write(json.dumps(event, ensure_ascii=False, sort_keys=True) + "\n")


def write_agent_queue(path: Path, records: list[dict[str, Any]], *, limit: int) -> None:
    queue = []
    for record in records[: max(0, limit)]:
        queue.append(
            {
                "candidate_hash": record.get("candidate_hash"),
                "artifact_key": record.get("artifact_key"),
                "priority_score": record.get("priority_score"),
                "priority_reasons": record.get("priority_reasons", []),
                "change_kind": record.get("change_kind"),
                "status": record.get("status"),
                "source": f"{record.get('source_repo')}@{record.get('source_branch_or_ref')}:{record.get('source_path')}",
                "source_blob": record.get("source_blob"),
                "destination": f"{record.get('destination_repo')}@{record.get('destination_branch_or_ref')}:{record.get('destination_path')}",
                "allowed_actions": ["classify", "summarize", "propose_review_packet"],
                "forbidden_actions": ["write_durable_destination", "mark_accepted", "push"],
            }
        )
    _write_jsonl(path, queue)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run the growth-aware Automath-NewMath bridge pipeline")
    parser.add_argument("--config", default=str(DEFAULT_CONFIG), help="pipeline config JSON")
    parser.add_argument("--include-unchanged", action="store_true", help="emit records already seen in bridge state")
    parser.add_argument("--limit-per-rule", type=int, default=50, help="maximum emitted records per discovery rule")
    parser.add_argument(
        "--scan-limit-per-rule",
        type=int,
        default=0,
        help="maximum matched paths to scan per discovery rule; 0 keeps the full scan",
    )
    parser.add_argument("--update-state", action="store_true", help="persist observed artifacts to local bridge state")
    parser.add_argument("--no-synthesis", action="store_true", help="skip cross-repo readiness synthesis")
    parser.add_argument("--inbox", help="override inbox JSONL output path")
    parser.add_argument("--plan", help="override transfer-plan Markdown output path")
    parser.add_argument("--event-log", default=str(DEFAULT_EVENT_LOG), help="ignored JSONL event log written with --update-state")
    parser.add_argument("--queue", default=str(DEFAULT_QUEUE), help="ignored top-K agent queue JSONL")
    parser.add_argument("--queue-limit", type=int, default=25, help="maximum records written to the agent queue")
    args = parser.parse_args(argv)

    config_path = Path(args.config).resolve()
    config = _load_json(config_path)
    state_path = REPO_ROOT / str(config.get("state_path"))
    inbox_path = Path(args.inbox) if args.inbox else REPO_ROOT / str(config.get("inbox_path"))
    plan_path = Path(args.plan) if args.plan else REPO_ROOT / str(config.get("transfer_plan_path"))

    state = _load_json_or_default(
        state_path,
        {"version": 1, "created_at": _now_iso(), "updated_at": "", "artifacts": {}},
    )
    records, summary = discover_records(
        config,
        config_path,
        state,
        include_unchanged=args.include_unchanged,
        limit_per_rule=max(1, args.limit_per_rule),
        scan_limit_per_rule=max(0, args.scan_limit_per_rule),
    )
    if not args.no_synthesis:
        snapshot = build_repo_snapshot(config, config_path)
        records = synthesize_records(records, snapshot)
        summary["synthesis"] = {
            "enabled": True,
            "automath_commit": snapshot["repos"]["automath"]["commit"],
            "newmath_commit": snapshot["repos"]["newmath"]["commit"],
            "newmath_constant_lean_files": snapshot["newmath_constants"]["lean_hit_count"],
            "newmath_constant_paper_files": snapshot["newmath_constants"]["paper_hit_count"],
            "automath_killo_golden_files": snapshot["automath_surfaces"]["killo_golden_path_count"],
        }
    else:
        summary["synthesis"] = {"enabled": False}
    _write_jsonl(inbox_path, records)
    write_agent_queue(Path(args.queue), records, limit=max(0, args.queue_limit))
    plan = render_transfer_plan(records, summary)
    plan_path.parent.mkdir(parents=True, exist_ok=True)
    plan_path.write_text(plan, encoding="utf-8")
    if args.update_state:
        _write_json(state_path, update_state(state, records, summary))
        append_events(Path(args.event_log), records)
        state_msg = f"updated state {state_path}; appended events to {args.event_log}"
    else:
        state_msg = "state unchanged (pass --update-state to persist observations)"
    print(f"[bridge-pipeline] wrote {len(records)} inbox record(s) to {inbox_path}")
    print(f"[bridge-pipeline] wrote agent queue to {args.queue}")
    print(f"[bridge-pipeline] wrote transfer plan to {plan_path}")
    print(f"[bridge-pipeline] {state_msg}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"[bridge-pipeline] error: {exc}", file=sys.stderr)
        raise SystemExit(1)
