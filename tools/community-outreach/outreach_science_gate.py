#!/usr/bin/env python3
"""Deterministic science-contract gates for open-problem outreach targets.

The outreach/openproblem pipeline is allowed to scan broad sources, but a target
may only consume deep-reasoning budget after it has a concrete mathematical
contract: what contribution type is being pursued, what evidence would count,
what artifact should be produced, and when the pipeline should write back or
close the target.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
TARGETS_DIR = SCRIPT_DIR / "targets"
STATE_DIR = SCRIPT_DIR / "outreach_state"
BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"
LEDGER_NAME = "science_gate.json"

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_board_parser import TodoSpec, parse_board  # noqa: E402
from outreach_profile import OutreachProfile, load_profile  # noqa: E402


CONTRACT_READY = "CONTRACT_READY"
NEEDS_CONTRACT = "NEEDS_CONTRACT"
NEEDS_EVIDENCE = "NEEDS_EVIDENCE"
WRITEBACK_READY = "WRITEBACK_READY"
CLOSE_TARGET = "CLOSE_TARGET"
BOARD_SKIPPED = "BOARD_SKIPPED"

BOARD_SKIP_TERMS = (
    "closed",
    "discarded",
    "overtaken",
    "solved",
    "handoff",
    "not outreach",
    "submitted",
)

WRITEBACK_TERMS = (
    "proved",
    "proof complete",
    "counterexample",
    "construction verified",
    "verified certificate",
    "certificate verified",
    "all checks pass",
    "reproducible",
    "breakthrough",
    "q.e.d",
)

COLLABORATION_WRITEBACK_TERMS = (
    "operator review",
    "draft ready",
    "reply draft",
    "email draft",
    "next contact",
    "specific ask",
    "collaboration plan",
    "thread summary",
)

CLOSE_TERMS = (
    "literature closed",
    "already solved",
    "overtaken",
    "not a stated open problem",
    "wrong target",
    "no progress",
    "two consecutive",
    "stuck",
)

CONTINUE_RESEARCH_TERMS = (
    "continue rather than write back",
    "continue rather than writeback",
    "continue rather than close",
    "continue rather than close or write back",
    "continue rather than close or writeback",
    "no outreach comment",
    "no outreach is justified",
    "not justify outreach",
    "not ready for outreach",
    "not prove the conjectural",
    "does not prove the conjectural",
    "does not improve",
    "primary target remains open",
    "next mathematically useful move",
    "next progress-lowering step",
)

PROGRESS_TERMS = (
    "lemma",
    "proposition",
    "theorem",
    "proof",
    "calculation",
    "construction",
    "counterexample",
    "certificate",
    "bound",
    "verified",
    "obstruction",
    "reduction",
)

MATH_LANE_TYPES = {"theorem", "counterexample", "construction", "research_note"}
FRONTIER_LANE_TYPES = {"certificate", "computational_record"}
COLLABORATION_LANE_TYPES = {"collaboration_packet"}
AUDIT_LANE_TYPES = {"source_audit_note"}

CONTRACT_SCORE_MIN = 7
PROGRESS_SCORE_MIN = 7
VERIFIABILITY_SCORE_MIN = 7


@dataclass
class ContractQuality:
    score: int = 0
    novelty_score: int = 0
    verifiability_score: int = 0
    progress_metric_score: int = 0
    artifact_score: int = 0
    bridge_score: int = 0
    surface_score: int = 0
    diagnostics: list[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        return asdict(self)


@dataclass
class ScienceGateVerdict:
    todo_id: str
    slug: str
    status: str
    contribution_type: str = ""
    terminal_artifact: str = ""
    verifier: str = ""
    progress_metric: str = ""
    origin: str = ""
    closure_status: str = ""
    verification_status: str = ""
    outreach_status: str = ""
    next_action: str = "hold"
    retry_budget: int = 0
    failure_kind: str = "none"
    reasons: list[str] = field(default_factory=list)
    missing: list[str] = field(default_factory=list)
    evidence_paths: list[str] = field(default_factory=list)
    taste_diagnostics: list[str] = field(default_factory=list)
    target_lane: str = ""
    contract_quality: dict = field(default_factory=dict)
    writeback_ready: bool = False
    close_ready: bool = False

    def to_dict(self) -> dict:
        return asdict(self)


def _read_text(path: Path, max_chars: int = 120000) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")[:max_chars]
    except OSError:
        return ""


def _artifact_path(slug: str, artifact: str) -> Path:
    p = Path(artifact)
    if p.is_absolute():
        return p
    return REPO_ROOT / p


def _rel_repo_path(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _is_draft_artifact(path_text: str) -> bool:
    name = Path(path_text).name.lower()
    return "draft" in name or name in {"submission.md", "email.md"}


def _validate_evidence_file(todo: TodoSpec, rel_path: str, path: Path) -> list[str]:
    name = Path(rel_path).name.lower()
    if name == "results.json":
        return _validate_results_json(todo, rel_path, path)
    if name.endswith(".json"):
        try:
            json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            return [f"invalid evidence JSON: {rel_path}: {exc}"]
    return []


def _target_has_runnable_reproducer(target_dir: Path) -> bool:
    """Return whether target evidence includes a local executable proof/check.

    Research prose and JSON summaries are useful audit artifacts, but they are
    not enough for exact numerical certificates. For frontier/certificate
    claims the pipeline must preserve a small local reproducer or formal file
    that a reviewer can run independently of the LLM transcript.
    """
    runnable_suffixes = {".py", ".lean", ".sh", ".sage", ".ipynb"}
    for path in target_dir.glob("*"):
        if not path.is_file():
            continue
        name = path.name.lower()
        if name in {LEDGER_NAME, "outreach_impact_gate.json", "profile.json", "freshness_judge.json"}:
            continue
        if path.suffix.lower() in runnable_suffixes:
            return True
    return False


def _needs_local_reproducer(contribution_type: str, target_lane: str, combined_text: str) -> bool:
    """Detect exact computational/certificate claims that need local replay.

    This intentionally keys off strong words used by our packets. It avoids
    blocking ordinary source-audit notes, while catching the dangerous case:
    an LLM-produced exact LP/dual/certificate narrative with no executable
    evidence on disk.
    """
    ctype = (contribution_type or "").strip()
    if target_lane != "frontier_lane" and ctype not in FRONTIER_LANE_TYPES:
        return False
    lower = (combined_text or "").lower()
    exact_markers = (
        "exact primal witness",
        "dual multipliers",
        "stationarity residual",
        "objective value decimal",
        "exact_value_rational",
        "singleton interval",
        "rational feasible witness",
        "active lp",
        "lp value",
        "verified certificate",
        "certificate verified",
        "mismatch_count",
        "unsat certificate",
    )
    return any(marker in lower for marker in exact_markers)


def _validate_results_json(todo: TodoSpec, rel_path: str, path: Path) -> list[str]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [f"invalid results.json: {rel_path}: {exc}"]
    errors: list[str] = []
    if not isinstance(data, dict):
        return [f"invalid results.json: {rel_path}: top-level value is not an object"]
    if todo.slug() == "arxiv_2603_21645_2":
        params = data.get("parameters")
        if not isinstance(params, dict):
            errors.append(f"invalid results.json: {rel_path}: missing parameters object")
        else:
            if int(params.get("c_min", -1)) != 0:
                errors.append(f"invalid results.json: {rel_path}: parameters.c_min must be 0")
            if int(params.get("c_max", -1)) < 128:
                errors.append(f"invalid results.json: {rel_path}: parameters.c_max must be at least 128")
        verification = data.get("verification")
        if not isinstance(verification, dict):
            errors.append(f"invalid results.json: {rel_path}: missing verification object")
        elif int(verification.get("mismatch_count", 1)) != 0:
            errors.append(f"invalid results.json: {rel_path}: verification.mismatch_count must be 0")
        counts = data.get("state_counts")
        if not isinstance(counts, list) or len(counts) < 129:
            errors.append(f"invalid results.json: {rel_path}: state_counts must cover at least c=0..128")
        else:
            seen: dict[int, int] = {}
            for row in counts:
                if not isinstance(row, dict):
                    continue
                try:
                    c = int(row.get("c"))
                    states = int(row.get("min_states"))
                except (TypeError, ValueError):
                    continue
                seen[c] = states
            missing_c = [c for c in range(129) if c not in seen]
            if missing_c:
                errors.append(
                    f"invalid results.json: {rel_path}: missing state_counts for "
                    f"c={','.join(str(c) for c in missing_c[:10])}"
                )
            if any(states <= 0 for states in seen.values()):
                errors.append(f"invalid results.json: {rel_path}: state counts must be positive")
    return errors


def _target_state(slug: str) -> dict:
    path = STATE_DIR / f"{slug}.json"
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def ledger_path(slug: str) -> Path:
    return TARGETS_DIR / slug / LEDGER_NAME


def load_ledger(slug: str) -> dict:
    try:
        return json.loads(ledger_path(slug).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def _latest_deep_run(state: dict) -> dict:
    runs = state.get("oracle_deep_runs") or []
    if not isinstance(runs, list) or not runs:
        return {}
    latest = runs[-1]
    return latest if isinstance(latest, dict) else {}


def _deep_response_text(run: dict, max_chars: int = 120000) -> str:
    parts: list[str] = []
    for turn in run.get("turns") or []:
        if not isinstance(turn, dict):
            continue
        response = str(turn.get("response") or "")
        if response:
            parts.append(_read_text(Path(response), max_chars=40000))
        contribution = str(turn.get("contribution") or "")
        if contribution:
            parts.append(contribution)
        if sum(len(p) for p in parts) >= max_chars:
            break
    return "\n\n".join(parts)[:max_chars]


def _deep_run_transport_failed(run: dict) -> bool:
    if not run:
        return False
    final = str(run.get("final_verdict") or "").upper()
    turns = run.get("turns") or []
    if final != "FAILED":
        return False
    if not isinstance(turns, list) or not turns:
        return True
    for turn in turns:
        if not isinstance(turn, dict):
            continue
        err = str(turn.get("error") or "").lower()
        response_chars = int(turn.get("response_chars") or 0)
        if response_chars > 0 and not any(
            marker in err
            for marker in ("timeout", "extraction", "cancelled", "transport", "empty response")
        ):
            return False
    return True


def _has_any(text: str, terms: tuple[str, ...]) -> bool:
    lower = text.lower()
    return any(term in lower for term in terms)


def _explicitly_requests_more_research(text: str) -> bool:
    return _has_any(text, CONTINUE_RESEARCH_TERMS)


def _target_lane(contribution_type: str) -> str:
    ctype = (contribution_type or "").strip()
    if ctype in FRONTIER_LANE_TYPES:
        return "frontier_lane"
    if ctype in COLLABORATION_LANE_TYPES:
        return "collaboration_lane"
    if ctype in AUDIT_LANE_TYPES:
        return "audit_lane"
    if ctype in MATH_LANE_TYPES:
        return "math_lane"
    return "unknown_lane"


def _contract_lane(contract) -> str:
    explicit = str(getattr(contract, "target_lane", "") or "").strip()
    if explicit in {"math_lane", "frontier_lane", "collaboration_lane", "audit_lane"}:
        return explicit
    return _target_lane(str(getattr(contract, "contribution_type", "") or ""))


def _quality_floor(contract) -> int:
    try:
        return int(getattr(contract, "contract_quality_floor", CONTRACT_SCORE_MIN) or CONTRACT_SCORE_MIN)
    except (TypeError, ValueError):
        return CONTRACT_SCORE_MIN


def _specificity_score(text: str, *, terms: tuple[str, ...] = ()) -> int:
    text = (text or "").strip()
    lower = text.lower()
    if not text:
        return 0
    score = 2
    if len(text) >= 80:
        score += 2
    if len(text) >= 160:
        score += 1
    if re.search(r"\b(arxiv|github|doi|http|erdos|tao|lean|results\.json|certificate|verifier)\b", lower):
        score += 2
    if terms and any(term in lower for term in terms):
        score += 2
    if re.search(r"\b(exact|explicit|dated|reproducible|checkable|certificate|proof|counterexample)\b", lower):
        score += 1
    if re.search(r"[:;]", text) and ("+" in text or "," in text):
        score += 1
    return min(score, 10)


def _contract_quality(todo: TodoSpec, profile: OutreachProfile) -> ContractQuality:
    contract = profile.science_contract
    if contract is None:
        return ContractQuality(diagnostics=["missing science_contract"])
    taste = contract.taste_obligations
    novelty_text = taste.novelty_witness if taste else ""
    reproducibility_text = taste.reproducibility_witness if taste else ""
    layer_text = taste.layer_separation_witness if taste else ""
    verifier_text = " ".join([
        contract.verifier,
        " ".join(str(x) for x in contract.evidence_required),
        reproducibility_text,
    ])
    progress_text = contract.progress_metric
    artifact_text = " ".join([
        contract.terminal_artifact,
        " ".join(str(x) for x in profile.expected_artifacts),
        " ".join(str(x) for x in profile.canonical_draft_paths),
    ])
    bridge_text = " ".join([
        todo.omega_fit_detail or "",
        json.dumps(profile.main_paper_bridge, ensure_ascii=False),
    ])
    surface_text = " ".join([
        profile.final_display_form,
        profile.success_gate,
        " ".join(str(x) for x in contract.writeback_when),
        " ".join(str(x) for x in contract.close_when),
        layer_text,
    ])
    novelty = _specificity_score(
        novelty_text,
        terms=("fresh", "stale", "duplicate", "source", "dated", "already", "newer", "open"),
    )
    verifiability = _specificity_score(
        verifier_text,
        terms=("verifier", "certificate", "proof", "results.json", "reproducible", "check", "lean"),
    )
    progress = _specificity_score(
        progress_text,
        terms=("count", "metric", "reduce", "gap", "turn", "certificate", "conflict", "lemma", "unresolved", "unsupported"),
    )
    artifact = _specificity_score(
        artifact_text,
        terms=("research.md", "results.json", "submission_draft", "certificate", "proof"),
    )
    bridge = _specificity_score(
        bridge_text,
        terms=("omega", "automath", "lean", "zmod", "crt", "kernel", "combinatorics"),
    )
    surface = _specificity_score(
        surface_text,
        terms=("operator", "approval", "draft", "email", "paper", "forum", "comment", "archive"),
    )
    diagnostics: list[str] = []
    if novelty < 7:
        diagnostics.append(f"novelty_score={novelty} < 7")
    if verifiability < VERIFIABILITY_SCORE_MIN:
        diagnostics.append(f"verifiability_score={verifiability} < {VERIFIABILITY_SCORE_MIN}")
    if progress < PROGRESS_SCORE_MIN:
        diagnostics.append(f"progress_metric_score={progress} < {PROGRESS_SCORE_MIN}")
    if artifact < 7:
        diagnostics.append(f"artifact_score={artifact} < 7")
    if surface < 7:
        diagnostics.append(f"surface_score={surface} < 7")
    if any(term in " ".join([verifier_text, progress_text, surface_text]).lower() for term in ("placeholder", "to be filled", "tbd", "unknown")):
        diagnostics.append("contract contains placeholder-like text")

    lane = _contract_lane(contract)
    if lane == "collaboration_lane":
        collab_text = surface_text.lower()
        if not any(term in collab_text for term in ("collaboration", "reply", "email", "thread", "ask", "next contact")):
            diagnostics.append("collaboration lane missing explicit ask/thread/next-contact gate")
    if lane == "frontier_lane":
        frontier_text = verifier_text.lower()
        if not any(term in frontier_text for term in ("score", "certificate", "verify", "verifier", "results.json", "reproduce")):
            diagnostics.append("frontier lane missing score/verifier/certificate gate")
    if lane == "math_lane":
        math_text = verifier_text.lower()
        if not any(term in math_text for term in ("proof", "theorem", "lemma", "counterexample", "construction", "certificate")):
            diagnostics.append("math lane missing proof/theorem/counterexample/construction verifier")

    hard_scores = [novelty, verifiability, progress, artifact, surface]
    score = int(round(sum(hard_scores) / len(hard_scores)))
    return ContractQuality(
        score=score,
        novelty_score=novelty,
        verifiability_score=verifiability,
        progress_metric_score=progress,
        artifact_score=artifact,
        bridge_score=bridge,
        surface_score=surface,
        diagnostics=diagnostics,
    )


def _contains_contract_text(text: str, profile: OutreachProfile) -> list[str]:
    missing: list[str] = []
    contract = profile.science_contract
    if contract is None:
        return ["science_contract"]
    if contract.contribution_type and contract.contribution_type.lower() not in text.lower():
        missing.append(f"contribution_type marker: {contract.contribution_type}")
    for item in contract.evidence_required:
        words = [w.lower() for w in re.findall(r"[A-Za-z0-9_]{5,}", str(item))]
        if words and not any(w in text.lower() for w in words[:4]):
            missing.append(f"evidence mention: {str(item)[:80]}")
    return missing


def _taste_diagnostics(profile: OutreachProfile) -> list[str]:
    contract = profile.science_contract
    if contract is None:
        return ["missing science_contract"]
    taste = contract.taste_obligations
    if taste is None:
        return ["missing taste_obligations"]
    diagnostics: list[str] = []
    fields = {
        "novelty_witness": taste.novelty_witness,
        "no_hidden_assumption_witness": taste.no_hidden_assumption_witness,
        "reproducibility_witness": taste.reproducibility_witness,
        "layer_separation_witness": taste.layer_separation_witness,
    }
    weak_terms = ("placeholder", "to be filled", "tbd", "unknown", "n/a")
    for key, value in fields.items():
        if len((value or "").strip()) < 40:
            diagnostics.append(f"{key} too short")
        if any(term in (value or "").lower() for term in weak_terms):
            diagnostics.append(f"{key} placeholder-like")
    return diagnostics


def _next_action(status: str, *, writeback_ready: bool, close_ready: bool) -> tuple[str, int, str]:
    if status == BOARD_SKIPPED:
        return "skip", 0, "board_skipped"
    if status == NEEDS_CONTRACT:
        return "profile_judge", 2, "missing_contract"
    if status == WRITEBACK_READY or writeback_ready:
        return "operator_review", 0, "none"
    if status == CLOSE_TARGET or close_ready:
        return "operator_archive_review", 0, "math_stuck_or_closed"
    if status == NEEDS_EVIDENCE:
        return "deep_reason", 3, "needs_evidence"
    if status == CONTRACT_READY:
        return "deep_reason", 3, "none"
    return "hold", 0, "unknown"


def contract_from_profile(todo: TodoSpec) -> ScienceGateVerdict:
    profile, errors = load_profile(todo.slug())
    if profile is None:
        return ScienceGateVerdict(
            todo_id=todo.todo_id,
            slug=todo.slug(),
            status=NEEDS_CONTRACT,
            next_action="profile_judge",
            retry_budget=2,
            failure_kind="missing_contract",
            reasons=["valid profile is required before science gate can run"],
            missing=errors,
        )
    contract = profile.science_contract
    if contract is None:
        return ScienceGateVerdict(
            todo_id=todo.todo_id,
            slug=todo.slug(),
            status=NEEDS_CONTRACT,
            next_action="profile_judge",
            retry_budget=2,
            failure_kind="missing_contract",
            reasons=["profile has no science_contract"],
            missing=["science_contract"],
        )
    taste_diagnostics = _taste_diagnostics(profile)
    target_lane = _contract_lane(contract)
    quality = _contract_quality(todo, profile)
    floor = _quality_floor(contract)
    quality_diagnostics = quality.diagnostics
    if taste_diagnostics:
        return ScienceGateVerdict(
            todo_id=todo.todo_id,
            slug=todo.slug(),
            status=NEEDS_CONTRACT,
            contribution_type=contract.contribution_type,
            terminal_artifact=contract.terminal_artifact,
            verifier=contract.verifier,
            progress_metric=contract.progress_metric,
            origin=contract.origin,
            closure_status=contract.closure_status,
            verification_status=contract.verification_status,
            outreach_status=contract.outreach_status,
            next_action="profile_judge",
            retry_budget=2,
            failure_kind="taste_gate_failed",
            reasons=["science_contract exists but taste obligations are not gate-clean"],
            missing=[f"taste gate: {d}" for d in taste_diagnostics],
            taste_diagnostics=taste_diagnostics,
            target_lane=target_lane,
            contract_quality=quality.to_dict(),
        )
    if target_lane == "unknown_lane" or quality.score < floor or quality_diagnostics:
        missing = [f"contract quality: {d}" for d in quality_diagnostics]
        if quality.score < floor:
            missing.insert(0, f"contract quality score {quality.score}/10 < {floor}/10")
        if target_lane == "unknown_lane":
            missing.insert(0, f"unknown contribution lane for {contract.contribution_type!r}")
        return ScienceGateVerdict(
            todo_id=todo.todo_id,
            slug=todo.slug(),
            status=NEEDS_CONTRACT,
            contribution_type=contract.contribution_type,
            terminal_artifact=contract.terminal_artifact,
            verifier=contract.verifier,
            progress_metric=contract.progress_metric,
            origin=contract.origin,
            closure_status=contract.closure_status,
            verification_status=contract.verification_status,
            outreach_status=contract.outreach_status,
            next_action="profile_judge",
            retry_budget=2,
            failure_kind="contract_quality_failed",
            reasons=["science_contract exists but is not specific enough to run without hallucination"],
            missing=missing,
            taste_diagnostics=taste_diagnostics,
            target_lane=target_lane,
            contract_quality=quality.to_dict(),
        )
    return ScienceGateVerdict(
        todo_id=todo.todo_id,
        slug=todo.slug(),
        status=CONTRACT_READY,
        contribution_type=contract.contribution_type,
        terminal_artifact=contract.terminal_artifact,
        verifier=contract.verifier,
        progress_metric=contract.progress_metric,
        origin=contract.origin,
        closure_status=contract.closure_status,
        verification_status=contract.verification_status,
        outreach_status=contract.outreach_status,
        next_action="deep_reason",
        retry_budget=3,
        reasons=["science_contract is schema-valid"],
        target_lane=target_lane,
        contract_quality=quality.to_dict(),
    )


def evaluate(todo: TodoSpec, *, include_pending_review: bool = False) -> ScienceGateVerdict:
    board_blob = " ".join([todo.status or "", todo.type_ or ""]).lower()
    skip_terms = BOARD_SKIP_TERMS
    if include_pending_review:
        skip_terms = tuple(term for term in BOARD_SKIP_TERMS if term != "pending user approval")
    if any(term in board_blob for term in skip_terms):
        return ScienceGateVerdict(
            todo_id=todo.todo_id,
            slug=todo.slug(),
            status=BOARD_SKIPPED,
            next_action="skip",
            retry_budget=0,
            failure_kind="board_skipped",
            reasons=["board status/type indicates skipped, closed, handoff, or already awaiting approval"],
        )
    profile, errors = load_profile(todo.slug())
    if profile is None:
        return ScienceGateVerdict(
            todo_id=todo.todo_id,
            slug=todo.slug(),
            status=NEEDS_CONTRACT,
            next_action="profile_judge",
            retry_budget=2,
            failure_kind="missing_contract",
            reasons=["valid target-specific profile required"],
            missing=errors,
        )
    contract = profile.science_contract
    if contract is None:
        return ScienceGateVerdict(
            todo_id=todo.todo_id,
            slug=todo.slug(),
            status=NEEDS_CONTRACT,
            next_action="profile_judge",
            retry_budget=2,
            failure_kind="missing_contract",
            reasons=["profile missing science_contract"],
            missing=["science_contract"],
        )
    taste_diagnostics = _taste_diagnostics(profile)
    target_lane = _contract_lane(contract)
    quality = _contract_quality(todo, profile)
    floor = _quality_floor(contract)
    contract_blockers: list[str] = []
    if taste_diagnostics:
        contract_blockers.extend(f"taste gate: {d}" for d in taste_diagnostics)
    if target_lane == "unknown_lane":
        contract_blockers.append(f"unknown contribution lane for {contract.contribution_type!r}")
    if quality.score < floor:
        contract_blockers.append(f"contract quality score {quality.score}/10 < {floor}/10")
    contract_blockers.extend(f"contract quality: {d}" for d in quality.diagnostics)

    artifact = _artifact_path(todo.slug(), contract.terminal_artifact)
    target_dir = TARGETS_DIR / todo.slug()
    evidence_paths: list[str] = []
    missing: list[str] = []
    reasons: list[str] = []
    artifact_text = ""

    terminal_rel = _rel_repo_path(artifact)
    if artifact.exists() and artifact.is_file():
        evidence_paths.append(terminal_rel)
        artifact_text = _read_text(artifact)
    else:
        missing.append(f"terminal artifact missing: {contract.terminal_artifact}")

    missing_required_artifacts: list[str] = []
    invalid_required_artifacts: list[str] = []
    expected_seen: set[str] = set()
    for rel in profile.expected_artifacts:
        p = _artifact_path(todo.slug(), rel)
        rel_path = _rel_repo_path(p)
        if rel_path in expected_seen:
            continue
        expected_seen.add(rel_path)
        if p.exists() and p.is_file():
            evidence_paths.append(rel_path)
            invalid_required_artifacts.extend(_validate_evidence_file(todo, rel_path, p))
        elif not _is_draft_artifact(rel_path):
            missing_required_artifacts.append(f"expected artifact missing: {rel_path}")

    # Evidence requirements often name concrete files like results.json even
    # when a profile forgot to list them in expected_artifacts. Treat those as
    # disk-level gates; the model saying "I created results.json" is not enough.
    target_dir = TARGETS_DIR / todo.slug()
    required_file_names: set[str] = set()
    evidence_blob = "\n".join(str(x) for x in contract.evidence_required)
    for match in re.findall(r"\b[A-Za-z0-9_.-]+\.(?:json|csv|py|lean|md|tex)\b", evidence_blob):
        if _is_draft_artifact(match):
            continue
        required_file_names.add(match)
    for name in sorted(required_file_names):
        p = target_dir / name
        rel_path = _rel_repo_path(p)
        if p.exists() and p.is_file():
            evidence_paths.append(rel_path)
            invalid_required_artifacts.extend(_validate_evidence_file(todo, rel_path, p))
        elif rel_path not in expected_seen and rel_path != terminal_rel:
            missing_required_artifacts.append(f"required evidence file missing: {rel_path}")

    if missing_required_artifacts:
        missing.extend(missing_required_artifacts)
    if invalid_required_artifacts:
        missing.extend(invalid_required_artifacts)

    state = _target_state(todo.slug())
    deep_run = _latest_deep_run(state)
    deep_text = _deep_response_text(deep_run)
    transport_failed = _deep_run_transport_failed(deep_run)
    combined = "\n\n".join([artifact_text, deep_text])

    if artifact_text:
        missing.extend(_contains_contract_text(artifact_text, profile))
    if not combined.strip():
        missing.append("no artifact or oracle deep reasoning text available")

    if _needs_local_reproducer(contract.contribution_type, target_lane, combined):
        if not _target_has_runnable_reproducer(target_dir):
            missing.append(
                "frontier/certificate exact numerical claim lacks a local runnable reproducer "
                f"in {_rel_repo_path(target_dir)}"
            )

    final_verdict = str(deep_run.get("final_verdict") or "").upper()
    writeback_ready = False
    close_ready = False
    continue_research = _explicitly_requests_more_research(combined)
    evidence_disk_ready = not missing_required_artifacts and not invalid_required_artifacts
    if continue_research:
        reasons.append("artifact explicitly says the target should continue rather than be written back")
    elif target_lane == "collaboration_lane":
        if artifact_text and _has_any(combined, COLLABORATION_WRITEBACK_TERMS):
            writeback_ready = True
    else:
        if artifact_text and evidence_disk_ready and _has_any(combined, WRITEBACK_TERMS):
            writeback_ready = True
        if final_verdict == "BREAKTHROUGH" and artifact.exists() and evidence_disk_ready:
            writeback_ready = True
    has_close_signal = _has_any(combined, CLOSE_TERMS) or final_verdict == "STUCK"
    # Missing disk evidence means the target has not reached a scientific
    # terminal state. Do not route incomplete targets to operator archive just
    # because a draft or oracle response contains "stuck/no progress" language;
    # the research loop must keep deepening until evidence is produced or a
    # verified closure/staleness artifact exists.
    if (
        not continue_research
        and (
        (has_close_signal and evidence_disk_ready and artifact_text)
        or (
            final_verdict == "FAILED"
            and not transport_failed
            and evidence_disk_ready
            and artifact_text
        )
        )
    ):
        close_ready = True

    if contract_blockers:
        status = NEEDS_CONTRACT
        missing = contract_blockers + missing
        reasons.append("science contract exists but quality/lane/taste gate is not RUN-clean")
    elif missing:
        status = NEEDS_EVIDENCE
        reasons.append("science contract exists but evidence is incomplete")
    elif writeback_ready:
        status = WRITEBACK_READY
        reasons.append("artifact/deep run contains writeback evidence")
    elif close_ready:
        status = CLOSE_TARGET
        reasons.append("artifact/deep run indicates closure or hard obstruction")
    elif transport_failed:
        status = NEEDS_EVIDENCE
        reasons.append("latest oracle deep run failed at transport/extraction layer, not as a mathematical closure")
    else:
        status = CONTRACT_READY
        reasons.append("contract exists; evidence does not yet satisfy writeback/close")

    next_action, retry_budget, failure_kind = _next_action(
        status, writeback_ready=writeback_ready, close_ready=close_ready
    )
    return ScienceGateVerdict(
        todo_id=todo.todo_id,
        slug=todo.slug(),
        status=status,
        contribution_type=contract.contribution_type,
        terminal_artifact=contract.terminal_artifact,
        verifier=contract.verifier,
        progress_metric=contract.progress_metric,
        origin=contract.origin,
        closure_status=contract.closure_status,
        verification_status=contract.verification_status,
        outreach_status=contract.outreach_status,
        next_action=next_action,
        retry_budget=retry_budget,
        failure_kind=failure_kind,
        reasons=reasons,
        missing=missing[:12],
        evidence_paths=sorted(set(evidence_paths)),
        taste_diagnostics=taste_diagnostics,
        target_lane=target_lane,
        contract_quality=quality.to_dict(),
        writeback_ready=writeback_ready,
        close_ready=close_ready,
    )


def science_contract_block(profile: OutreachProfile | None) -> str:
    if profile is None or profile.science_contract is None:
        return "(missing science_contract; do not deep-reason until one is supplied)"
    c = profile.science_contract
    lines = [
        f"Contribution type: {c.contribution_type}",
        f"Target lane: {_contract_lane(c)}",
        f"Contract quality floor: {_quality_floor(c)}/10",
        f"Origin: {c.origin}",
        f"Closure status: {c.closure_status}",
        f"Verification status: {c.verification_status}",
        f"Outreach status: {c.outreach_status}",
        f"Terminal artifact: {c.terminal_artifact}",
        f"Verifier: {c.verifier}",
        f"Progress metric: {c.progress_metric}",
        "Taste obligations:",
        f"- Novelty witness: {(c.taste_obligations.novelty_witness if c.taste_obligations else '(missing)')}",
        f"- No hidden assumption witness: {(c.taste_obligations.no_hidden_assumption_witness if c.taste_obligations else '(missing)')}",
        f"- Reproducibility witness: {(c.taste_obligations.reproducibility_witness if c.taste_obligations else '(missing)')}",
        f"- Layer separation witness: {(c.taste_obligations.layer_separation_witness if c.taste_obligations else '(missing)')}",
        "Evidence required:",
        *[f"- {x}" for x in c.evidence_required],
        "Write back only when:",
        *[f"- {x}" for x in c.writeback_when],
        "Close or re-scope when:",
        *[f"- {x}" for x in c.close_when],
        f"No-progress patience turns: {c.no_progress_patience_turns}",
    ]
    return "\n".join(lines)


def audit_board(
    path: Path = BOARD_PATH,
    *,
    include_pending_review: bool = False,
) -> tuple[int, list[str], list[ScienceGateVerdict]]:
    todos = parse_board(path)
    rows = [evaluate(todo, include_pending_review=include_pending_review) for todo in todos.values()]
    diagnostics: list[str] = []
    for row in rows:
        if row.status == BOARD_SKIPPED:
            continue
        if row.status == CONTRACT_READY and row.taste_diagnostics:
            diagnostics.append(f"{row.todo_id}: CONTRACT_READY but taste diagnostics present")
        if row.writeback_ready and row.outreach_status == "sent":
            diagnostics.append(f"{row.todo_id}: writeback_ready target already marked sent; archive/close explicitly")
        if row.writeback_ready and row.next_action != "operator_review":
            diagnostics.append(f"{row.todo_id}: writeback_ready must route to operator_review")
        if row.outreach_status in {"draft_ready", "approved", "sent"} and row.closure_status in {"seed", "scoped_target"}:
            diagnostics.append(
                f"{row.todo_id}: outreach_status={row.outreach_status} cannot upgrade mathematical closure={row.closure_status}"
            )
        if row.verification_status in {"operator_approved"} and row.closure_status in {"seed", "scoped_target"}:
            diagnostics.append(
                f"{row.todo_id}: operator approval is verification/outreach only, not mathematical closure"
            )
        if row.target_lane == "collaboration_lane" and row.closure_status not in {"seed", "scoped_target", "partial_progress"}:
            diagnostics.append(
                f"{row.todo_id}: collaboration_lane cannot mark mathematical closure={row.closure_status}"
            )
        if row.target_lane == "collaboration_lane" and row.writeback_ready and row.outreach_status == "not_drafted":
            diagnostics.append(
                f"{row.todo_id}: collaboration_lane writeback_ready requires draftable/draft_ready outreach_status"
            )
        if row.status == NEEDS_CONTRACT and row.failure_kind == "taste_gate_failed":
            diagnostics.append(f"{row.todo_id}: taste gate failed before run: {'; '.join(row.taste_diagnostics)}")
        if row.status == CONTRACT_READY:
            q = row.contract_quality or {}
            if int(q.get("score") or 0) < CONTRACT_SCORE_MIN:
                diagnostics.append(f"{row.todo_id}: CONTRACT_READY but contract_quality.score < {CONTRACT_SCORE_MIN}")
        if row.status in {CONTRACT_READY, NEEDS_EVIDENCE, WRITEBACK_READY} and row.target_lane == "unknown_lane":
            diagnostics.append(f"{row.todo_id}: runnable status has unknown target lane")
    return (0 if not diagnostics else 1), diagnostics, rows


def write_ledgers(rows: list[ScienceGateVerdict]) -> list[Path]:
    written: list[Path] = []
    for row in rows:
        if row.status == BOARD_SKIPPED:
            continue
        path = ledger_path(row.slug)
        path.parent.mkdir(parents=True, exist_ok=True)
        previous = load_ledger(row.slug)
        prior_history = previous.get("history") if isinstance(previous.get("history"), list) else []
        payload = row.to_dict()
        payload.update({
            "schema_version": "outreach-science-gate-ledger-v1",
            "checked_at": _now_iso(),
            "ledger_path": str(path.relative_to(REPO_ROOT)),
        })
        event = {
            "checked_at": payload["checked_at"],
            "status": row.status,
            "next_action": row.next_action,
            "failure_kind": row.failure_kind,
            "closure_status": row.closure_status,
            "verification_status": row.verification_status,
            "outreach_status": row.outreach_status,
            "target_lane": row.target_lane,
            "contract_quality_score": (row.contract_quality or {}).get("score"),
            "missing": row.missing[:6],
        }
        payload["history"] = (prior_history + [event])[-25:]
        tmp = path.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        tmp.replace(path)
        written.append(path)
    return written


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--todo-id", default="", help="only judge one T-NN")
    parser.add_argument("--json", action="store_true", help="emit JSON")
    parser.add_argument("--audit", action="store_true", help="fail nonzero on harness invariant violations")
    parser.add_argument("--write-ledger", action="store_true", help="write targets/<slug>/science_gate.json ledgers")
    parser.add_argument(
        "--include-pending-review",
        action="store_true",
        help="re-evaluate targets already marked Pending User Approval instead of returning BOARD_SKIPPED",
    )
    args = parser.parse_args(argv)

    todos = parse_board(BOARD_PATH)
    rows = []
    for tid, todo in todos.items():
        if args.todo_id and tid != args.todo_id:
            continue
        rows.append(evaluate(todo, include_pending_review=args.include_pending_review))
    rows.sort(key=lambda r: (r.status, r.todo_id))
    if args.audit:
        rc, diagnostics, audit_rows = audit_board(
            BOARD_PATH,
            include_pending_review=args.include_pending_review,
        )
        if args.json:
            print(json.dumps({
                "ok": rc == 0,
                "diagnostics": diagnostics,
                "histogram": _histogram(audit_rows),
            }, ensure_ascii=False, indent=2))
            return rc
        if diagnostics:
            print("[science-gate] audit FAIL")
            for msg in diagnostics:
                print(f"- {msg}")
        else:
            print("[science-gate] audit OK")
        return rc
    if args.write_ledger:
        written = write_ledgers(rows)
        if args.json:
            print(json.dumps({
                "count": len(written),
                "written": [str(p.relative_to(REPO_ROOT)) for p in written],
            }, ensure_ascii=False, indent=2))
        else:
            print(f"wrote {len(written)} science gate ledger(s)")
            for pth in written:
                print(str(pth.relative_to(REPO_ROOT)))
        return 0
    if args.json:
        print(json.dumps([r.to_dict() for r in rows], ensure_ascii=False, indent=2))
        return 0
    if not rows:
        print("No matching targets.")
        return 0
    for row in rows:
        print(
            f"{row.todo_id} {row.status:16} {row.contribution_type or '-'} :: {row.slug} "
            f"[closure={row.closure_status or '-'} verification={row.verification_status or '-'} "
            f"outreach={row.outreach_status or '-'} lane={row.target_lane or '-'} "
            f"q={(row.contract_quality or {}).get('score', '-')} next={row.next_action}]"
        )
        if row.missing:
            print("  missing: " + "; ".join(row.missing))
        if row.taste_diagnostics:
            print("  taste: " + "; ".join(row.taste_diagnostics))
        if row.reasons:
            print("  reason: " + "; ".join(row.reasons))
    return 0


def _histogram(rows: list[ScienceGateVerdict]) -> dict[str, int]:
    out: dict[str, int] = {}
    for row in rows:
        out[row.status] = out.get(row.status, 0) + 1
    return out


if __name__ == "__main__":
    raise SystemExit(main())
