#!/usr/bin/env python3
"""Synthesize Automath-NewMath bridge readiness from both repos.

Discovery records say "this artifact exists." Synthesis says whether the two
growing repos currently have enough matching evidence and gates for any next
step. The output is still advisory and local-only; it never writes durable
paper, Lean, docs, or manifest status.
"""

from __future__ import annotations

import argparse
import fnmatch
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_CONFIG = SCRIPT_DIR / "bridge_pipeline_config.json"
DEFAULT_INPUT = SCRIPT_DIR / "inbox" / "bridge_inbox.jsonl"
DEFAULT_OUTPUT = SCRIPT_DIR / "out" / "bridge_synthesis.jsonl"
DEFAULT_REPORT = SCRIPT_DIR / "out" / "bridge_synthesis_report.md"

LEAN_DECL_RE = re.compile(r"^\s*(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev)\s+([A-Za-z0-9_'.]+)", re.M)
PAPER_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
LEAN_CHECKED_RE = re.compile(r"\\leanchecked\{([^}]+)\}")


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def _load_json(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"Expected object JSON in {path}")
    return data


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    if not path.exists():
        return records
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, 1):
            stripped = line.strip()
            if not stripped:
                continue
            data = json.loads(stripped)
            if not isinstance(data, dict):
                raise ValueError(f"{path}:{line_no}: expected object")
            records.append(data)
    return records


def _write_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def _run_git(repo: Path, args: list[str], *, binary: bool = False) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=str(repo),
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).decode("utf-8", errors="ignore").strip()
        raise RuntimeError(f"git {' '.join(args)} failed in {repo}: {detail}")
    if binary:
        return proc.stdout.decode("utf-8", errors="ignore")
    return proc.stdout.decode("utf-8", errors="replace")


def _resolve_repo_path(raw: str, config_path: Path) -> Path:
    path = Path(raw)
    if not path.is_absolute():
        path = (config_path.parent / path).resolve()
        if not (path / ".git").exists():
            path = (REPO_ROOT / raw).resolve()
    return path


def _repo_meta(config: dict[str, Any], config_path: Path) -> dict[str, dict[str, Any]]:
    repos = config.get("repositories")
    if not isinstance(repos, dict):
        raise ValueError("config.repositories must be an object")
    meta: dict[str, dict[str, Any]] = {}
    for key, raw in repos.items():
        if not isinstance(raw, dict):
            continue
        path = _resolve_repo_path(str(raw.get("local_path", "")), config_path)
        ref = str(raw.get("default_ref") or "HEAD")
        meta[str(key)] = {
            **raw,
            "path": path,
            "default_ref": ref,
            "commit": _run_git(path, ["rev-parse", ref]).strip(),
        }
    return meta


def _ls_tree(repo: Path, ref: str, globs: list[str]) -> list[str]:
    out = _run_git(repo, ["ls-tree", "-r", "--name-only", ref])
    paths = [line.strip() for line in out.splitlines() if line.strip()]
    if not globs:
        return paths
    return [p for p in paths if any(fnmatch.fnmatch(p, g) for g in globs)]


def _show(repo: Path, ref: str, rel_path: str, *, limit: int = 700_000) -> str:
    proc = subprocess.run(
        ["git", "show", f"{ref}:{rel_path}"],
        cwd=str(repo),
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        return ""
    return proc.stdout[:limit].decode("utf-8", errors="ignore")


def _first(items: list[str], limit: int = 8) -> list[str]:
    return items[:limit]


def _scan_newmath_constants(repo: Path, ref: str) -> dict[str, Any]:
    lean_paths = _ls_tree(repo, ref, ["lean4/BEDC/Derived/**/*.lean"])
    paper_paths = _ls_tree(repo, ref, ["papers/bedc/parts/concrete_instances/**/*.tex"])
    lean_hits: list[dict[str, Any]] = []
    paper_hits: list[dict[str, Any]] = []
    declarations: list[str] = []
    leanchecked: list[str] = []
    labels: list[str] = []

    for path in lean_paths:
        text = _show(repo, ref, path)
        if not re.search(r"RealConstant|constant|Constant", text):
            continue
        decls = LEAN_DECL_RE.findall(text)
        selected_decls = [d for d in decls if re.search(r"RealConstant|constant|Constant", d)]
        declarations.extend(selected_decls)
        lean_hits.append({
            "path": path,
            "declarations": _first(selected_decls, 10),
            "has_taste_gate_symbol": "taste_gate" in text,
        })

    for path in paper_paths:
        text = _show(repo, ref, path)
        if not re.search(r"RealConstant|constant rational|constant-rational|Constant", text):
            continue
        labels.extend(PAPER_LABEL_RE.findall(text))
        leanchecked.extend(LEAN_CHECKED_RE.findall(text))
        paper_hits.append({
            "path": path,
            "labels": _first(PAPER_LABEL_RE.findall(text), 6),
            "leanchecked": _first(LEAN_CHECKED_RE.findall(text), 6),
            "has_closurestatus": "\\begin{closurestatus}" in text,
            "has_origin_ai": "\\origin{ai}" in text,
        })

    taste_gate_paths = []
    for path in _ls_tree(repo, ref, ["lean4/BEDC/Derived/**/TasteGate.lean"]):
        text = _show(repo, ref, path)
        if "def taste_gate" in text:
            taste_gate_paths.append(path)

    return {
        "lean_hit_count": len(lean_hits),
        "paper_hit_count": len(paper_hits),
        "sample_lean_hits": _first([h["path"] for h in lean_hits], 12),
        "sample_paper_hits": _first([h["path"] for h in paper_hits], 12),
        "sample_declarations": _first(sorted(set(declarations)), 16),
        "sample_labels": _first(sorted(set(labels)), 16),
        "sample_leanchecked": _first(sorted(set(leanchecked)), 16),
        "taste_gate_paths": _first(taste_gate_paths, 20),
    }


def _scan_newmath_supervisor(repo: Path, ref: str) -> dict[str, Any]:
    path = "tools/bedc-deep/supervisor.py"
    text = _show(repo, ref, path)
    probes = {
        "low_water_refill": "low-water" in text or "low_water" in text,
        "loning_watch": "loning_watch" in text,
        "reject_clusters": "stage2_reject_clusters" in text,
        "pi_review": "run_pi_review" in text,
        "auto_commit": "commit_and_push_if_changed" in text,
        "dev_sync_resolver": "dev_sync_resolver" in text,
    }
    return {
        "path": path,
        "present": bool(text),
        "patterns": probes,
        "pattern_count": sum(1 for ok in probes.values() if ok),
    }


def _scan_automath_surfaces(repo: Path, ref: str) -> dict[str, Any]:
    golden_paths = _ls_tree(
        repo,
        ref,
        [
            "lean4/Omega/**/*Killo*.lean",
            "lean4/Omega/**/*Golden*.lean",
            "lean4/Omega/**/*golden*.lean",
        ],
    )
    theorem_labels: list[str] = []
    for path in golden_paths[:80]:
        text = _show(repo, ref, path)
        theorem_labels.extend([d for d in LEAN_DECL_RE.findall(text) if d.startswith("paper_")])

    gate_files = {
        "omega_ci": "lean4/scripts/omega_ci.py",
        "codex_formalize": "lean4/scripts/codex_formalize.py",
        "distillation": "tools/distillation/distill.py",
        "distillation_supervisor": "tools/distillation/supervisor.py",
        "oracle_pipeline": "tools/chatgpt-oracle/oracle_pipeline.py",
    }
    gates: dict[str, dict[str, Any]] = {}
    for key, path in gate_files.items():
        text = _show(repo, ref, path)
        gates[key] = {
            "path": path,
            "present": bool(text),
            "has_gate_language": bool(re.search(r"gate|audit|review|validate|compile", text, re.I)),
        }
    distill_text = _show(repo, ref, "tools/distillation/distill.py")
    return {
        "killo_golden_path_count": len(golden_paths),
        "sample_killo_golden_paths": _first(golden_paths, 16),
        "sample_paper_theorems": _first(sorted(set(theorem_labels)), 16),
        "gate_surfaces": gates,
        "has_killo_golden_trace_re": "KILLO_GOLDEN_TRACE_RE" in distill_text,
    }


def build_repo_snapshot(config: dict[str, Any], config_path: Path) -> dict[str, Any]:
    repos = _repo_meta(config, config_path)
    automath = repos["automath"]
    newmath = repos["newmath"]
    newmath_ref = str(newmath.get("default_ref") or "HEAD")
    automath_ref = str(automath.get("default_ref") or "HEAD")
    return {
        "created_at": _now_iso(),
        "repos": {
            "automath": {
                "repo": automath.get("repo"),
                "ref": automath_ref,
                "commit": automath.get("commit"),
            },
            "newmath": {
                "repo": newmath.get("repo"),
                "ref": newmath_ref,
                "commit": newmath.get("commit"),
            },
        },
        "newmath_constants": _scan_newmath_constants(newmath["path"], newmath_ref),
        "newmath_supervisor": _scan_newmath_supervisor(newmath["path"], newmath_ref),
        "automath_surfaces": _scan_automath_surfaces(automath["path"], automath_ref),
    }


def _readiness_for(record: dict[str, Any], snapshot: dict[str, Any]) -> dict[str, Any]:
    rule = str(record.get("discovery_rule") or "")
    direction = str(record.get("bridge_direction") or "")
    source_path = str(record.get("source_path") or "")
    newmath_constants = snapshot["newmath_constants"]
    automath_surfaces = snapshot["automath_surfaces"]
    newmath_supervisor = snapshot["newmath_supervisor"]

    readiness = "observe_only"
    confidence = "medium"
    required_gates = ["operator_review", "bridge_manifest_update"]
    reasons: list[str] = []
    next_action = "keep observing until an operator promotes a manifest record"

    if rule == "newmath.bedc_supervisor_pipeline":
        readiness = "ready_for_local_packet"
        required_gates.extend(["bridge_gate", "operator_selects_adopted_patterns"])
        reasons.append("NewMath supervisor exposes low-water refill, loning watch, reject clustering, PI review, and gated write patterns.")
        next_action = "use these supervisor patterns when adjusting bridge cadence and gates"
    elif rule.startswith("newmath.real_constant"):
        readiness = "blocked_automath_not_ready"
        required_gates.extend(["newmath_taste_gate_or_closure_audit", "automath_receiving_queue_decision"])
        reasons.append(
            f"NewMath constants are visible ({newmath_constants['lean_hit_count']} Lean files, "
            f"{newmath_constants['paper_hit_count']} paper files), but Automath has no selected receiving paper/Lean target."
        )
        if automath_surfaces["killo_golden_path_count"]:
            reasons.append(
                f"Automath has {automath_surfaces['killo_golden_path_count']} Killo/golden Lean surfaces for comparison, not automatic consumption."
            )
        next_action = "write only a local review packet if gates pass; do not write Automath paper or Lean"
    elif "taste_gate" in rule or "ai_seed" in rule or "accepted_proposals" in rule:
        readiness = "needs_operator_review"
        required_gates.extend(["newmath_taste_gate", "destination_audit"])
        reasons.append("BEDC AI-origin or accepted material keeps the NewMath TasteGate/operator boundary.")
        next_action = "operator decides whether Automath consumes the pattern, not the content"
    elif rule.startswith("automath.killo") or "paper_claim" in rule or "distillation" in rule:
        readiness = "ready_for_local_packet"
        required_gates.extend(["automath_omega_ci_or_distillation_gate", "newmath_destination_review"])
        reasons.append("Automath source has existing gate surfaces and can be summarized for NewMath review.")
        next_action = "create NewMath-side review packet only; do not create a NewMath proposal automatically"
    elif rule == "automath.pipeline_gate_surfaces":
        readiness = "ready_for_local_packet"
        required_gates.extend(["operator_maps_gate_to_newmath_lane"])
        reasons.append("Automath gate surfaces are protocol material suitable for NewMath-side bridge planning.")
        next_action = "compare Automath gates with BEDC supervisor and choose shared gate names"
    else:
        reasons.append("No special synthesis rule matched; discovery record remains observed/candidate only.")

    if direction == "newmath_to_automath" and "constant" in source_path.lower():
        readiness = "blocked_automath_not_ready"
        confidence = "high"

    can_write_local_packet = readiness in {"ready_for_local_packet", "needs_operator_review", "blocked_automath_not_ready"}
    durable_write_allowed = False
    why_not = (
        "Durable write is blocked until an operator records accepted/consumed status in the manifest and destination gates pass."
    )
    return {
        "readiness": readiness,
        "readiness_confidence": confidence,
        "can_write_local_packet": can_write_local_packet,
        "durable_write_allowed": durable_write_allowed,
        "why_not_writeback_yet": why_not,
        "required_gates": sorted(set(required_gates)),
        "evidence_summary": reasons,
        "matching_newmath_evidence": {
            "constant_lean_files": newmath_constants["sample_lean_hits"],
            "constant_paper_files": newmath_constants["sample_paper_hits"],
            "taste_gate_paths": newmath_constants["taste_gate_paths"],
            "supervisor_patterns": newmath_supervisor["patterns"],
        },
        "matching_automath_evidence": {
            "killo_golden_paths": automath_surfaces["sample_killo_golden_paths"],
            "paper_theorems": automath_surfaces["sample_paper_theorems"],
            "gate_surfaces": automath_surfaces["gate_surfaces"],
            "has_killo_golden_trace_re": automath_surfaces["has_killo_golden_trace_re"],
        },
        "synthesis_next_action": next_action,
    }


def synthesize_records(records: list[dict[str, Any]], snapshot: dict[str, Any]) -> list[dict[str, Any]]:
    enriched: list[dict[str, Any]] = []
    for record in records:
        item = json.loads(json.dumps(record))
        item["synthesis"] = _readiness_for(item, snapshot)
        if item["synthesis"]["readiness"] == "blocked_automath_not_ready":
            item["status"] = "blocked"
            item["next_action"] = item["synthesis"]["synthesis_next_action"]
        elif item["synthesis"]["readiness"] == "observe_only" and item.get("status") == "candidate":
            item["status"] = "observed"
        enriched.append(item)
    enriched.sort(
        key=lambda item: (
            {
                "ready_for_local_packet": 0,
                "needs_operator_review": 1,
                "blocked_automath_not_ready": 2,
                "observe_only": 3,
            }.get(str((item.get("synthesis") or {}).get("readiness")), 4),
            -int(item.get("priority", 0) or 0),
            str(item.get("source_path", "")),
        )
    )
    return enriched


def render_report(records: list[dict[str, Any]], snapshot: dict[str, Any]) -> str:
    counts: dict[str, int] = {}
    for record in records:
        readiness = str((record.get("synthesis") or {}).get("readiness") or "unknown")
        counts[readiness] = counts.get(readiness, 0) + 1

    lines = [
        "# Automath-NewMath bridge synthesis report",
        "",
        f"- Generated at: `{_now_iso()}`",
        f"- Records: `{len(records)}`",
        f"- Automath ref: `{snapshot['repos']['automath']['ref']}` `{str(snapshot['repos']['automath']['commit'])[:12]}`",
        f"- NewMath ref: `{snapshot['repos']['newmath']['ref']}` `{str(snapshot['repos']['newmath']['commit'])[:12]}`",
        "",
        "## Readiness Counts",
        "",
        "| Readiness | Count |",
        "| --- | ---: |",
    ]
    for key, value in sorted(counts.items()):
        lines.append(f"| `{key}` | {value} |")

    constants = snapshot["newmath_constants"]
    automath = snapshot["automath_surfaces"]
    supervisor = snapshot["newmath_supervisor"]
    lines.extend([
        "",
        "## Cross-Repo Evidence",
        "",
        f"- NewMath constant Lean files: `{constants['lean_hit_count']}`",
        f"- NewMath constant paper files: `{constants['paper_hit_count']}`",
        f"- NewMath TasteGate witness files: `{len(constants['taste_gate_paths'])}`",
        f"- NewMath supervisor pattern count: `{supervisor['pattern_count']}`",
        f"- Automath Killo/golden Lean files: `{automath['killo_golden_path_count']}`",
        f"- Automath has KILLO_GOLDEN_TRACE_RE: `{automath['has_killo_golden_trace_re']}`",
        "",
        "## Candidate Decisions",
        "",
        "| Readiness | Direction | Source | Destination | Next action |",
        "| --- | --- | --- | --- | --- |",
    ])
    for record in records[:200]:
        synthesis = record.get("synthesis") or {}
        lines.append(
            "| "
            + " | ".join(
                str(cell).replace("|", "\\|")
                for cell in [
                    f"`{synthesis.get('readiness', '')}`",
                    f"`{record.get('bridge_direction', '')}`",
                    f"{record.get('source_repo')}@{record.get('source_branch_or_ref')}:{record.get('source_path')}",
                    f"{record.get('destination_repo')}@{record.get('destination_branch_or_ref')}:{record.get('destination_path')}",
                    synthesis.get("synthesis_next_action") or record.get("next_action", ""),
                ]
            )
            + " |"
        )
    lines.extend([
        "",
        "## Boundary",
        "",
        "This synthesis is a gate input, not approval. `blocked_automath_not_ready` means NewMath evidence exists but Automath has not selected a receiving queue or destination audit. `ready_for_local_packet` means a local ignored review packet may be generated after deterministic gates. No result here authorizes push, publication, external send, paper write, Lean write, or automatic acceptance.",
        "",
    ])
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Synthesize bridge readiness across Automath and NewMath")
    parser.add_argument("--config", default=str(DEFAULT_CONFIG), help="bridge pipeline config JSON")
    parser.add_argument("--input", default=str(DEFAULT_INPUT), help="bridge inbox JSONL")
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT), help="synthesized JSONL output")
    parser.add_argument("--report", default="", help="markdown synthesis report")
    args = parser.parse_args(argv)

    try:
        config_path = Path(args.config).resolve()
        config = _load_json(config_path)
        records = _read_jsonl(Path(args.input))
        snapshot = build_repo_snapshot(config, config_path)
        enriched = synthesize_records(records, snapshot)
        _write_jsonl(Path(args.output), enriched)
        report_path = Path(args.report) if args.report else REPO_ROOT / str(config.get("synthesis_report_path") or DEFAULT_REPORT)
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(render_report(enriched, snapshot), encoding="utf-8")
    except Exception as exc:
        print(f"[bridge-synthesis] error: {exc}", file=sys.stderr)
        return 1

    print(f"[bridge-synthesis] wrote {len(enriched)} record(s) to {args.output}")
    print(f"[bridge-synthesis] wrote report to {report_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
