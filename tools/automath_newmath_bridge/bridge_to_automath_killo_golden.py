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
import re
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
DISTILLATION_DIR = REPO_ROOT / "papers" / "publication" / "backflow" / ".distillation"
LATEX_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")


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


def _source_repo_path(record: dict[str, Any]) -> Path | None:
    repo = str(record.get("source_repo") or "")
    if repo == "the-omega-institute/newmath":
        return (REPO_ROOT.parent / "newmath").resolve()
    if repo == "the-omega-institute/automath":
        return REPO_ROOT
    return None


def _source_text(record: dict[str, Any], *, max_chars: int = 80000) -> str:
    repo_path = _source_repo_path(record)
    source_ref = str(record.get("source_branch_or_ref") or "HEAD")
    source_path = str(record.get("source_path") or "")
    if not repo_path or not source_path:
        return ""
    try:
        proc = subprocess.run(
            ["git", "-C", str(repo_path), "show", f"{source_ref}:{source_path}"],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return ""
    if proc.returncode == 0:
        return proc.stdout[:max_chars]
    local = repo_path / source_path
    if local.exists():
        return local.read_text(encoding="utf-8", errors="replace")[:max_chars]
    return ""


def _source_labels(record: dict[str, Any]) -> list[str]:
    return LATEX_LABEL_RE.findall(_source_text(record))[:12]


def _bridge_prompt_revision(record: dict[str, Any]) -> str:
    receiving = _automath_receiving_context(record) or {}
    payload = {
        "source_path": record.get("source_path"),
        "source_commit": record.get("source_commit"),
        "target_sections": receiving.get("target_sections", []),
        "omega_mechanisms": receiving.get("omega_mechanisms", []),
        "first_distillation_prompt": receiving.get("first_distillation_prompt", ""),
        "scope_contract_seed": receiving.get("scope_contract_seed", {}),
    }
    return hashlib.sha1(json.dumps(payload, sort_keys=True).encode("utf-8")).hexdigest()[:12]


def _automath_receiving_context(record: dict[str, Any]) -> dict[str, Any] | None:
    source_path = str(record.get("source_path") or "").lower()
    if "concrete_instances/banach/singleton_certificate.tex" in source_path:
        return {
            "status": "found",
            "target_sections": ["pom"],
            "evidence_paths": [
                "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/body/pom/sec__pom.tex",
                "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/appendix/operator_algebra/app__op-algebra.tex",
            ],
            "omega_mechanisms": [
                "pom",
                "finite audit obligation",
                "empty-history singleton certificate",
            ],
            "scope_contract_seed": {
                "max_families": 1,
                "allowed_target_sections": ["pom"],
                "forbidden_sections": [
                    "circle_dimension_phase_gate",
                    "recursive_addressing",
                    "typed_address_biaxial_completion",
                    "fold_residual_time",
                    "principles",
                    "spg",
                    "zeta_finite_part",
                ],
                "required_disposition": "one tiny lemma or explicit no-fit rejection",
            },
            "rationale": (
                "The NewMath singleton-certificate source is narrow enough for a "
                "single Automath POM receiving test. It should not reopen the broader "
                "Banach bounded-operator bridge."
            ),
            "first_distillation_prompt": (
                "Narrow retry for the NewMath singleton_certificate bridge source. "
                "Extract at most one Automath-native POM finite-audit obligation: an "
                "empty-history singleton certificate or explicit no-fit rejection. "
                "Use only the source labels and evidence_paths as prior evidence. Do "
                "not discuss Banach theory, bounded-operator carriers, circle dimension "
                "phase gates, recursive addressing, SPG, zeta finite part, or any "
                "future split candidates. If the existing POM notation cannot state the "
                "certificate in one small theorem-family/writeback, return blocked."
            ),
        }
    if "concrete_instances/banach/" in source_path:
        return {
            "status": "found",
            "target_sections": [
                "circle_dimension_phase_gate",
                "pom",
            ],
            "evidence_paths": [
                "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/appendix/operator_algebra/app__op-algebra.tex",
                "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/body/circle_dimension_phase_gate/cor__circle-dimension-phase-gate-bare-circle-not-complete.tex",
            ],
            "omega_mechanisms": [
                "circle_dimension_phase_gate",
                "pom",
                "bounded-operator carrier",
                "finite audit obligation",
            ],
            "rationale": (
                "NewMath Banach bounded-operator material has an Automath receiving "
                "surface in operator-algebra and carrier/certificate sections. "
                "The bridge may generate a distillation source, but Killo/golden "
                "review must still decide whether a theorem-level writeback is valid."
            ),
            "first_distillation_prompt": (
                "Use the NewMath Banach source as prior evidence only. Inspect the "
                "source labels and translate at most one minimal Automath-native "
                "carrier-certificate obligation into the circle_dimension_phase_gate "
                "or pom core sections. Treat operator-algebra files listed in "
                "evidence_paths as evidence context, not as direct writeback routes. "
                "Do not copy BEDC text verbatim; if the Automath target lacks the "
                "required notation, return a blocked/rejected writeback rather than "
                "inventing a broad Banach theory."
            ),
        }
    return None


def _auto_promote_for_killo(record: dict[str, Any]) -> bool:
    if record.get("bridge_direction") != "newmath_to_automath":
        return False
    if record.get("gate_status") != "gate_passed":
        return False
    if record.get("destination_repo") != "the-omega-institute/automath":
        return False
    if str(record.get("source_artifact_kind") or "") != "paper_claim":
        return False
    if record.get("readiness") not in {"ready_for_local_packet", "blocked_automath_not_ready"}:
        return False
    if not _automath_receiving_context(record):
        return False
    return bool(_source_labels(record))


def _eligible(record: dict[str, Any]) -> bool:
    if record.get("bridge_direction") != "newmath_to_automath":
        return False
    if record.get("gate_status") != "gate_passed":
        return False
    if record.get("destination_repo") != "the-omega-institute/automath":
        return False
    if _auto_promote_for_killo(record):
        return True
    if record.get("readiness") in {"blocked_automath_not_ready", "observe_only"}:
        return False
    if record.get("operator_review_required") and record.get("status") not in {"accepted", "consumed"}:
        return False
    return True


def _candidate_name(record: dict[str, Any]) -> str:
    source_path = str(record.get("source_path") or record.get("artifact_key") or "NewMath bridge")
    stem = Path(source_path).stem.replace("_", " ").replace("-", " ").strip()
    return f"NewMath bridge source: {stem}"


def _candidate_block_status(record: dict[str, Any]) -> str:
    state_dir = DISTILLATION_DIR / _distill_slug(_candidate_name(record))
    current_revision = _bridge_prompt_revision(record)
    blocked_path = state_dir / "blocked.json"
    if blocked_path.exists():
        try:
            payload = json.loads(blocked_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            payload = {}
        if isinstance(payload, dict):
            blocked_revision = str(payload.get("bridge_prompt_revision") or "")
            if blocked_revision and blocked_revision != current_revision:
                return ""
            source_path = str(record.get("source_path") or "").lower()
            if not blocked_revision and "concrete_instances/banach/singleton_certificate.tex" in source_path:
                return ""
            return str(payload.get("status") or "")
    state_path = state_dir / "state.json"
    if not state_path.exists():
        return ""
    try:
        state_payload = json.loads(state_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return ""
    if not isinstance(state_payload, dict):
        return ""
    candidate_path = state_dir / "source_candidate.json"
    candidate_revision = ""
    if candidate_path.exists():
        try:
            candidate_payload = json.loads(candidate_path.read_text(encoding="utf-8"))
            if isinstance(candidate_payload, dict):
                candidate_revision = str(candidate_payload.get("bridge_prompt_revision") or "")
        except (OSError, json.JSONDecodeError):
            candidate_revision = ""
    if candidate_revision and candidate_revision != current_revision:
        return ""
    if state_payload.get("current_stage") in {"R", "W", "E"} and state_payload.get("failure_kind") in {
        "bridge_distillation_timeout",
        "review_failed",
        "writeback_review_failed",
    }:
        return str(state_payload.get("failure_kind") or "blocked")
    if state_payload.get("current_stage") == "W" and candidate_revision == current_revision:
        return "writeback_in_progress"
    if state_payload.get("current_stage") == "W" and not candidate_revision:
        return "writeback_in_progress"
    return ""


def _candidate_payload(record: dict[str, Any]) -> dict[str, Any]:
    source = f"{record.get('source_repo')}@{record.get('source_branch_or_ref')}:{record.get('source_path')}"
    evidence = record.get("evidence_summary")
    if not isinstance(evidence, list):
        evidence = []
    labels = _source_labels(record)
    receiving = _automath_receiving_context(record) or {}
    auto_promoted = _auto_promote_for_killo(record)
    target_sections = receiving.get("target_sections") or ["killo-golden", "omega paper writeback"]
    omega_mechanisms = receiving.get("omega_mechanisms") or ["killo-golden", "NewMath bridge evidence"]
    revision = _bridge_prompt_revision(record)
    return {
        "schema_version": "automath-newmath-automath-writeback-candidate-v1",
        "created_at": _now_iso(),
        "status": "ready_for_automath_distillation_supervisor",
        "bridge_prompt_revision": revision,
        "distillation_source_name": _candidate_name(record),
        "bridge_source": source,
        "bridge_record": record,
        "auto_promoted_for_killo_golden": auto_promoted,
        "source_paper_labels": labels,
        "receiving_context": receiving,
        "source_queue_candidate": {
            "status": "open",
            "priority": int(record.get("priority") or 70),
            "proposed_source": _candidate_name(record),
            "source_type": "bridge_packet",
            "origin": "automath_newmath_bridge",
            "bridge_prompt_revision": revision,
            "target_sections": target_sections,
            "omega_mechanisms": omega_mechanisms,
            "scope_contract_seed": receiving.get("scope_contract_seed", {}),
            "fit_score": 8,
            "novelty_score": 6,
            "rationale": (
                str(receiving.get("rationale") or "").strip()
                or (
                    "NewMath-to-Automath bridge record passed deterministic bridge gates "
                    "and operator status is accepted/consumed. Automath distillation must "
                    "still perform Killo/golden validation, Claude review, and writeback "
                    "application planning."
                )
            ),
            "source_material": [source, *[f"source label: {label}" for label in labels], *[str(item) for item in evidence]],
            "risks": [
                "Do not copy NewMath BEDC text verbatim.",
                "Do not expose bridge runtime packet metadata in paper LaTeX.",
                "Do not write unless Automath distillation review accepts the writeback.",
                "Auto-promotion only creates a distillation source; it is not paper acceptance.",
            ],
            "first_distillation_prompt": (
                str(receiving.get("first_distillation_prompt") or "").strip()
                or (
                    "Use this NewMath bridge source as mathematical evidence only. "
                    "Find an Automath-native Killo/golden receiving context, produce at "
                    "most one conservative theorem-level paper writeback, and obey the "
                    "existing killo-golden style and review gate."
                )
            ),
            "next_step": "distill_source",
        },
    }


def build_candidates(
    records: list[dict[str, Any]],
    runtime_dir: Path,
    *,
    limit: int,
    retry_blocked: bool = False,
) -> list[Path]:
    if not runtime_dir.is_absolute():
        runtime_dir = REPO_ROOT / runtime_dir
    runtime_dir.mkdir(parents=True, exist_ok=True)
    written: list[Path] = []
    for record in records:
        if len(written) >= limit:
            break
        if not _eligible(record):
            continue
        if not retry_blocked and _candidate_block_status(record) in {
            "distillation_timeout",
            "bridge_distillation_timeout",
            "review_failed",
            "writeback_review_failed",
            "writeback_in_progress",
        }:
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
    review_backend: str,
    dry_run: bool,
    push_branch: bool,
    oracle_research: bool,
    oracle_deepening: bool,
    timeout_seconds: int,
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
        review_backend,
    ]
    if dry_run:
        cmd.append("--dry-run")
    if oracle_research:
        cmd.append("--oracle-research")
    if oracle_deepening:
        cmd.append("--oracle-deepening")
    try:
        result = subprocess.run(
            cmd,
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=max(60, timeout_seconds),
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        return {
            "status": "writeback_blocked_by_distillation_timeout",
            "returncode": None,
            "review_blocked": False,
            "timeout_seconds": max(60, timeout_seconds),
            "stdout_tail": (exc.stdout or "")[-3000:] if isinstance(exc.stdout, str) else "",
            "stderr_tail": (exc.stderr or "")[-3000:] if isinstance(exc.stderr, str) else "",
        }
    combined_output = f"{result.stdout}\n{result.stderr}"
    review_blocked = result.returncode != 0 and (
        "Stage W failed review gate" in combined_output
        or "Pipeline stopped at stage W" in combined_output
        or '"status": "review_failed"' in combined_output
        or "'status': 'review_failed'" in combined_output
    )
    out = {
        "status": (
            "ran"
            if result.returncode == 0
            else "writeback_blocked_by_killo_golden_review"
            if review_blocked
            else "failed"
        ),
        "returncode": result.returncode,
        "review_blocked": review_blocked,
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


def _distill_slug(value: str) -> str:
    lowered = value.strip().lower()
    slug = re.sub(r"[^a-z0-9]+", "_", lowered).strip("_")
    return slug or "distillation_source"


def record_timeout_block(name: str, distillation: dict[str, Any]) -> None:
    state_dir = DISTILLATION_DIR / _distill_slug(name)
    state_dir.mkdir(parents=True, exist_ok=True)
    payload = {
        "stage": "W",
        "status": "distillation_timeout",
        "timeout_seconds": distillation.get("timeout_seconds"),
        "resume_stage": "W",
        "bridge_prompt_revision": distillation.get("bridge_prompt_revision"),
        "updated_at": _now_iso(),
    }
    (state_dir / "blocked.json").write_text(
        json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    state_path = state_dir / "state.json"
    if not state_path.exists():
        return
    try:
        state_data = json.loads(state_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return
    if not isinstance(state_data, dict):
        return
    state_data["current_stage"] = "W"
    state_data["updated_at"] = _now_iso()
    state_data["failure_kind"] = "bridge_distillation_timeout"
    state_data["next_action"] = "narrow_bridge_scope_before_retry"
    blocked = state_data.get("blocked")
    if not isinstance(blocked, dict):
        blocked = {}
    blocked["bridge_timeout"] = payload
    state_data["blocked"] = blocked
    feedback = state_data.get("prior_feedback")
    if not isinstance(feedback, list):
        feedback = []
    feedback.append(
        f"Bridge distillation timed out after {distillation.get('timeout_seconds')} seconds; narrow scope before retry."
    )
    state_data["prior_feedback"] = feedback[-20:]
    state_path.write_text(
        json.dumps(state_data, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def seed_distillation_source(payload: dict[str, Any]) -> Path:
    name = str(payload["distillation_source_name"])
    state_dir = DISTILLATION_DIR / _distill_slug(name)
    state_dir.mkdir(parents=True, exist_ok=True)
    source_candidate = dict(payload["source_queue_candidate"])
    source_candidate["queue_id"] = f"bridge:{_digest(payload.get('bridge_record') or {})}"
    source_candidate["bridge_packet"] = {
        "bridge_source": payload.get("bridge_source"),
        "source_paper_labels": payload.get("source_paper_labels", []),
        "receiving_context": payload.get("receiving_context", {}),
        "auto_promoted_for_killo_golden": payload.get("auto_promoted_for_killo_golden", False),
        "bridge_prompt_revision": payload.get("bridge_prompt_revision", ""),
    }
    (state_dir / "source_candidate.json").write_text(
        json.dumps(source_candidate, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    state_path = state_dir / "state.json"
    if not state_path.exists():
        state_path.write_text(
            json.dumps(
                {
                    "name": name,
                    "current_stage": "R",
                    "round_number": 0,
                    "prior_feedback": [],
                    "scores": {},
                    "created_at": _now_iso(),
                    "updated_at": _now_iso(),
                    "depth_cycle": 0,
                    "completed_families": [],
                    "scope_contract": {},
                    "policy_state": {},
                    "open_debts": [],
                    "split_candidates": [],
                    "blocked": {},
                    "failure_kind": "unknown",
                    "attempts": 1,
                    "retry_budget": 0,
                    "next_action": "run_pipeline",
                    "lifecycle_flags": {},
                },
                ensure_ascii=False,
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
    else:
        try:
            state_data = json.loads(state_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            state_data = {}
        blocked_path = state_dir / "blocked.json"
        blocked_data: dict[str, Any] = {}
        if blocked_path.exists():
            try:
                raw_blocked = json.loads(blocked_path.read_text(encoding="utf-8"))
                if isinstance(raw_blocked, dict):
                    blocked_data = raw_blocked
            except (OSError, json.JSONDecodeError):
                blocked_data = {}
        prompt_revision = str(payload.get("bridge_prompt_revision") or "")
        blocked_revision = str(blocked_data.get("bridge_prompt_revision") or "")
        revision_changed = prompt_revision and prompt_revision != blocked_revision
        if (
            isinstance(state_data, dict)
            and state_data.get("current_stage") in {"W", "E"}
            and (
                blocked_data.get("status") == "review_failed"
                or blocked_data.get("status") == "distillation_timeout"
                or state_data.get("failure_kind") in {"review_failed", "writeback_review_failed"}
                or (revision_changed and state_data.get("failure_kind") == "bridge_distillation_timeout")
            )
        ):
            for artifact_name in (
                "raw_research.json",
                "section_matches.json",
                "global_evidence_pack.json",
                "generated_payload.json",
                "writeback_response.json",
                "blocked.json",
            ):
                artifact_path = state_dir / artifact_name
                if artifact_path.exists():
                    artifact_path.unlink()
            state_data["current_stage"] = "R"
            state_data["round_number"] = 0
            state_data["updated_at"] = _now_iso()
            state_data["next_action"] = "rerun_pipeline_from_bridge_reseed"
            state_data["failure_kind"] = "bridge_reseed_after_review_block"
            state_data["scores"] = {}
            state_data["depth_cycle"] = 0
            state_data["completed_families"] = []
            state_data["scope_contract"] = {}
            state_data["open_debts"] = []
            state_data["split_candidates"] = []
            state_data["blocked"] = {}
            feedback = state_data.get("prior_feedback")
            if not isinstance(feedback, list):
                feedback = []
            feedback.append(
                "Bridge reseeded source_candidate with refined receiving context after Killo/golden review/timeout block."
            )
            state_data["prior_feedback"] = feedback[-20:]
            state_path.write_text(
                json.dumps(state_data, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
    return state_dir / "source_candidate.json"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Automath-native Killo/golden writeback for accepted bridge records")
    parser.add_argument("--gate-results", default=str(DEFAULT_GATE_RESULTS))
    parser.add_argument("--runtime-dir", default=str(DEFAULT_RUNTIME_DIR))
    parser.add_argument("--branch", default=DEFAULT_BRANCH)
    parser.add_argument("--limit", type=int, default=1)
    parser.add_argument("--apply", action="store_true", help="Invoke Automath distillation supervisor")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--push-branch", action="store_true", help="Push the Automath bridge branch after successful writeback")
    parser.add_argument(
        "--review-backend",
        choices=["codex", "codex-claude", "claude"],
        default="codex-claude",
        help="Automath distillation reviewer backend; codex-claude falls back to Codex when Claude is unavailable",
    )
    parser.add_argument("--oracle-research", action="store_true")
    parser.add_argument("--oracle-deepening", action="store_true")
    parser.add_argument(
        "--retry-blocked",
        action="store_true",
        help="Retry candidates already blocked by Killo/golden review or bridge distillation timeout",
    )
    parser.add_argument(
        "--distillation-timeout-seconds",
        type=int,
        default=2700,
        help="Bound one Automath distillation invocation so the bridge supervisor cannot be monopolized by one source",
    )
    args = parser.parse_args(argv)

    branch = _git_stdout(["branch", "--show-current"], timeout=30)
    if branch != args.branch:
        raise RuntimeError(f"Refusing to run on branch {branch!r}; expected {args.branch!r}")

    records = _read_jsonl(Path(args.gate_results))
    paths = build_candidates(
        records,
        Path(args.runtime_dir),
        limit=max(0, args.limit),
        retry_blocked=args.retry_blocked,
    )
    summary: dict[str, Any] = {
        "candidate_packets": [str(path.relative_to(REPO_ROOT)) for path in paths],
        "apply": bool(args.apply),
        "push_branch": bool(args.push_branch),
        "review_backend": args.review_backend,
        "fallback_policy": (
            "Automath distillation owns review fallback. With review_backend=codex-claude, "
            "Codex review remains sufficient when Claude is unavailable or quota-limited."
        ),
    }
    if not paths:
        summary["status"] = "no_eligible_records"
        summary["reason"] = (
            "No NewMath-to-Automath records passed bridge gates with accepted/consumed "
            "operator status, so Killo/golden writeback was not attempted."
        )
        print(json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True))
        return 0
    if args.apply:
        payload = json.loads(paths[0].read_text(encoding="utf-8"))
        name = str(payload["distillation_source_name"])
        summary["seeded_source_candidate"] = str(seed_distillation_source(payload).relative_to(REPO_ROOT))
        summary["distillation"] = run_distillation_supervisor(
            branch=args.branch,
            name=name,
            review_backend=args.review_backend,
            dry_run=args.dry_run,
            push_branch=args.push_branch,
            oracle_research=args.oracle_research,
            oracle_deepening=args.oracle_deepening,
            timeout_seconds=args.distillation_timeout_seconds,
        )
        distillation = summary["distillation"]
        if isinstance(distillation, dict):
            distillation["bridge_prompt_revision"] = payload.get("bridge_prompt_revision")
        if distillation.get("status") == "writeback_blocked_by_killo_golden_review":
            summary["status"] = "writeback_blocked_by_killo_golden_review"
            summary["next_pi_action"] = (
                "Treat this as a normal Automath gate result. PI should refine the "
                "bridge source, receiving context, or Killo/golden prompt before retrying."
            )
        elif distillation.get("status") == "writeback_blocked_by_distillation_timeout":
            record_timeout_block(name, distillation)
            summary["status"] = "writeback_blocked_by_distillation_timeout"
            summary["next_pi_action"] = (
                "Treat this as a normal bridge watchdog result. PI should narrow the "
                "source scope, reduce prompt size, or defer this source before retrying."
            )
        elif distillation.get("status") == "ran":
            summary["status"] = "writeback_supervisor_completed"
        else:
            summary["status"] = "writeback_supervisor_failed"
    else:
        summary["status"] = "candidate_packets_written"
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
