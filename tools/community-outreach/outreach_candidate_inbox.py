#!/usr/bin/env python3
"""Local inbox for automatically discovered open-problem candidates.

Discovery tools should write candidates here first, not directly into
RESEARCH_BOARD. A candidate graduates to board/profile only after deterministic
schema checks and an explicit profile/deep-judge step.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
STATE_DIR = SCRIPT_DIR / "outreach_state"
INBOX = STATE_DIR / "candidate_inbox.jsonl"

REQUIRED = {
    "title",
    "source_url",
    "statement",
    "rationale",
    "final_display_form",
    "success_gate",
}

MIN_ACADEMIC_IMPACT_SCORE = 36

HIGH_IMPACT_PATTERNS = (
    r"\b(conjecture|problem|open problem|famous|longstanding|classical|major|central)\b",
    r"\b(classification|rigidity|extremal|extremality|obstruction|impossibility)\b",
    r"\b(certificate|verifier|reproducib|audit|exact|formal|checker)\b",
    r"\b(erdos|hindman|ramsey|tao|mixon|sidon|singmaster|aimpl|openproblemgarden|mathoverflow)\b",
)

LOW_IMPACT_ARXIV_PATTERNS = (
    r"\b(recent arxiv|new arxiv|arxiv followup|follow-up to arxiv)\b",
    r"\b(small table|one more case|slightly larger|minor extension|incremental)\b",
    r"\b(author question|private note|email the author)\b",
)


@dataclass
class CandidateGate:
    passed: bool
    score: int
    lane: str = "standard"
    reasons: list[str] = field(default_factory=list)
    missing: list[str] = field(default_factory=list)
    risk_flags: list[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        return asdict(self)


def _id_for(candidate: dict) -> str:
    raw = "|".join(str(candidate.get(k) or "") for k in ("title", "source_url", "statement"))
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:12]


def validate_candidate(candidate: dict) -> list[str]:
    errors = []
    for key in sorted(REQUIRED):
        if not str(candidate.get(key) or "").strip():
            errors.append(f"missing {key}")
    if not str(candidate.get("source_url") or "").startswith(("http://", "https://")):
        errors.append("source_url must be http(s)")
    return errors


def academic_impact_gate(candidate: dict) -> CandidateGate:
    """Deterministic pre-board gate for broad discovery outputs.

    This does not prove the problem is important. It blocks obvious low-quality
    board-fill candidates before they consume profile/deep-reasoning budget.
    """
    missing = validate_candidate(candidate)
    reasons: list[str] = []
    risk_flags: list[str] = []
    score = 0

    ctype = str(candidate.get("type") or "").upper()
    if ctype in {"DECIDABLE", "EXISTENCE", "CLASSIFICATION", "EXTREMALITY", "OBSTRUCTION", "RIGIDITY"}:
        score += 5
    else:
        missing.append("type must be a concrete mathematical contribution class")

    statement = str(candidate.get("statement") or "")
    source_url = str(candidate.get("source_url") or "")
    rationale = str(candidate.get("rationale") or "")
    untouched = str(candidate.get("untouched_evidence") or "")
    omega_fit = str(candidate.get("omega_fit_detail") or "")
    first_step = str(candidate.get("first_attack_step") or "")
    final_display = str(candidate.get("final_display_form") or "")
    success_gate = str(candidate.get("success_gate") or "")
    combined = " ".join(
        [
            statement,
            source_url,
            rationale,
            untouched,
            omega_fit,
            first_step,
            final_display,
            success_gate,
            str(candidate.get("title") or ""),
        ]
    )

    if len(statement) >= 80 and re.search(r"\b(prove|show|classify|construct|decide|bound|exists?|counterexample)\b", statement, re.I):
        score += 6
        reasons.append("statement is specific")
    else:
        missing.append("specific one-sentence mathematical statement")

    if re.search(r"(arxiv\.org|github\.com|doi\.org|terrytao\.wordpress|openproblem|problemsilike|aimpl|mathoverflow|wordpress|x\.com|twitter\.com)", source_url, re.I):
        score += 5
        reasons.append("source is inspectable")
    else:
        missing.append("credible inspectable public source URL")

    if len(untouched) >= 60 and re.search(r"\b(open|not closed|no .*202[4-6]|fresh|current|ai|sota|gap|unresolved)\b", untouched, re.I):
        score += 5
        reasons.append("freshness/untouched evidence present")
    else:
        missing.append("freshness or untouched evidence")

    if len(omega_fit) >= 80:
        score += 3
        if re.search(r"(lean4/Omega|Omega/|Automath|ZMod|CRT|certificate|verifier|finite|combinatorics)", omega_fit, re.I):
            score += 3
            reasons.append("has plausible Automath/Omega bridge")
        else:
            risk_flags.append("weak Automath bridge; allowed only if topic impact is high")
    else:
        missing.append("plausible bridge or later-bridge plan")

    try:
        fit_score = int(candidate.get("fit_score") or 0)
    except (TypeError, ValueError):
        fit_score = 0
    try:
        topic_score = int(candidate.get("topic_score") or 0)
    except (TypeError, ValueError):
        topic_score = 0
    try:
        effort_days = int(candidate.get("effort_estimate_days") or 0)
    except (TypeError, ValueError):
        effort_days = 0

    high_impact_hits = sum(1 for pat in HIGH_IMPACT_PATTERNS if re.search(pat, combined, re.I))
    if high_impact_hits >= 2:
        score += 6
        reasons.append("has high-impact/open-frontier signals")
    elif high_impact_hits == 1:
        score += 2
        risk_flags.append("only one high-impact signal; check this is not a low-value follow-up")
    else:
        missing.append("high-impact signal such as named conjecture, public frontier, verifier gap, or classification problem")

    source_is_arxiv = bool(re.search(r"arxiv\.org", source_url, re.I))
    low_impact_arxiv_hits = sum(1 for pat in LOW_IMPACT_ARXIV_PATTERNS if re.search(pat, combined, re.I))
    if source_is_arxiv and low_impact_arxiv_hits and high_impact_hits < 2:
        score -= 8
        risk_flags.append("arXiv-only low-impact derivative follow-up")
    if source_is_arxiv and topic_score < 8:
        score -= 4
        risk_flags.append("arXiv source without high topic score; arXiv is information, not priority")

    if topic_score >= 9:
        score += 9
        reasons.append("exceptional topic impact")
    elif topic_score >= 8:
        score += 7
        reasons.append("high topic impact")
    elif topic_score >= 6:
        score += 4
    else:
        missing.append("topic_score >= 8 unless there is an exceptional certificate/verifier gap")

    if fit_score >= 5:
        score += 3
    elif topic_score >= 9:
        score += 1
        risk_flags.append("low current fit accepted only because topic_score is very high")
    else:
        missing.append("fit_score >= 5 or exceptional topic_score")

    long_horizon = effort_days > 21 and topic_score >= 9
    if 1 <= effort_days <= 21:
        score += 3
    elif long_horizon:
        score += 1
        reasons.append("long-horizon high-impact candidate")
        risk_flags.append("long-horizon: requires PI scoping before board graduation")
    else:
        risk_flags.append("effort estimate outside 1-21 day research packet")

    if len(first_step) >= 50 and re.search(r"\b(prove|compute|construct|certify|enumerate|derive|bound|verify|falsify|extract|write|audit|check)\b", first_step, re.I):
        score += 4
    else:
        missing.append("bounded first attack step with a concrete verb")

    if len(final_display) >= 30 and len(success_gate) >= 50:
        score += 4
    else:
        missing.append("final display form and success gate")

    weak_phrases = ("interesting direction", "explore", "investigate", "could be related", "maybe", "tbd", "unknown")
    blob = " ".join([statement, rationale, first_step, success_gate]).lower()
    if any(p in blob for p in weak_phrases):
        risk_flags.append("generic or placeholder-like language")
        score -= 4
    if str(candidate.get("risk_level") or "").lower() == "high" and topic_score < 9:
        risk_flags.append("high risk without exceptional topic impact")
        score -= 3
    if "arxiv" in source_url.lower() and re.search(r"\bemail\b", final_display, re.I) and topic_score < 9:
        risk_flags.append("low-impact arXiv author-email target; prefer serious notes or public artifacts")
        score -= 5

    lane = "long_horizon_review" if long_horizon else "standard"
    passed = score >= MIN_ACADEMIC_IMPACT_SCORE and not missing
    if not passed and score >= MIN_ACADEMIC_IMPACT_SCORE:
        reasons.append("score high but mandatory fields are not gate-clean")
    return CandidateGate(passed=passed, score=score, lane=lane, reasons=reasons, missing=missing, risk_flags=risk_flags)


def add_candidate(candidate: dict, *, source: str) -> dict:
    errors = validate_candidate(candidate)
    gate = academic_impact_gate(candidate)
    if not gate.passed:
        errors.extend(f"academic gate: {m}" for m in gate.missing)
        errors.extend(f"academic gate risk: {m}" for m in gate.risk_flags)
    row = {
        "candidate_id": _id_for(candidate),
        "source": source,
        "received_at_epoch": time.time(),
        "status": gate.lane if gate.passed and gate.lane != "standard" else ("needs_profile_judge" if not errors else "invalid"),
        "errors": errors,
        "academic_impact_gate": gate.to_dict(),
        "candidate": candidate,
    }
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    with open(INBOX, "a", encoding="utf-8") as f:
        f.write(json.dumps(row, ensure_ascii=False) + "\n")
    return row


def list_candidates() -> list[dict]:
    if not INBOX.exists():
        return []
    by_id: dict[str, dict] = {}
    order: list[str] = []
    for line in INBOX.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        cid = row.get("candidate_id")
        if not cid:
            continue
        if cid not in by_id:
            order.append(cid)
        by_id[cid] = row
    return [by_id[cid] for cid in order]


def append_event(candidate_id: str, *, status: str, note: str = "", metadata: dict | None = None) -> dict:
    """Append a status event for an existing candidate.

    The inbox is JSONL append-only so discovery history is preserved. Readers
    keep the latest row per candidate_id.
    """
    if not candidate_id:
        raise ValueError("candidate_id required")
    existing = {row.get("candidate_id"): row for row in list_candidates()}
    base = existing.get(candidate_id)
    if not base:
        raise KeyError(f"candidate {candidate_id} not found")
    row = {
        **base,
        "received_at_epoch": time.time(),
        "status": status,
        "note": note,
        "metadata": metadata or {},
    }
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    with open(INBOX, "a", encoding="utf-8") as f:
        f.write(json.dumps(row, ensure_ascii=False) + "\n")
    return row


def get_candidate(candidate_id: str) -> dict | None:
    for row in list_candidates():
        if row.get("candidate_id") == candidate_id:
            return row
    return None


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="cmd", required=True)
    add = sub.add_parser("add-json", help="add one candidate from a JSON file")
    add.add_argument("path")
    add.add_argument("--source", default="manual")
    sub.add_parser("list")
    mark = sub.add_parser("mark", help="append a status event for a candidate")
    mark.add_argument("candidate_id")
    mark.add_argument("--status", required=True)
    mark.add_argument("--note", default="")
    args = p.parse_args(argv)
    if args.cmd == "add-json":
        payload = json.loads(Path(args.path).read_text(encoding="utf-8"))
        rows = payload.get("candidates") if isinstance(payload, dict) else None
        if isinstance(rows, list):
            added = [add_candidate(c, source=args.source) for c in rows if isinstance(c, dict)]
            print(json.dumps(added, ensure_ascii=False, indent=2))
            return 0
        print(json.dumps(add_candidate(payload, source=args.source), ensure_ascii=False, indent=2))
        return 0
    if args.cmd == "list":
        print(json.dumps(list_candidates(), ensure_ascii=False, indent=2))
        return 0
    if args.cmd == "mark":
        print(json.dumps(append_event(args.candidate_id, status=args.status, note=args.note), ensure_ascii=False, indent=2))
        return 0
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
