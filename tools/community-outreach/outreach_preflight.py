#!/usr/bin/env python3
"""Local preflight judgment for outreach open-problem targets.

This module is deliberately offline and deterministic. It answers the question
the operator needs answered before any expensive agent loop starts:

    What is this target's final display form, and should the pipeline run it?

The research loop imports this module so it can refuse to spend cycles on
closed, formalization-only, unprofiled, or display-less board entries. The CLI
is also useful while the supervisor is stopped.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"
TARGETS_DIR = SCRIPT_DIR / "targets"

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_board_parser import TodoSpec, parse_board  # noqa: E402
from outreach_profile import load_profile  # noqa: E402
from outreach_science_gate import CONTRACT_READY, contract_from_profile  # noqa: E402


RUN = "RUN"
DROP = "DROP"
HANDOFF = "HANDOFF"
NEEDS_PROFILE = "NEEDS_PROFILE"
NEEDS_BOARD_UPDATE = "NEEDS_BOARD_UPDATE"
WAIT_USER = "WAIT_USER"

ACTIONABLE_VERDICTS = {RUN}

REGISTERED_SUPERVISOR_PROFILES: set[str] = set()

SKIP_STATUS_PATTERNS = (
    "CLOSED",
    "DISCARDED",
    "OVERTAKEN",
    "SOLVED",
    "Submitted",
    "OPERATOR_DEPRIORITIZED",
    "OPERATOR PAUSED",
    "PAUSED",
    "SHELVED",
)

HANDOFF_PATTERNS = (
    "handoff",
    "formalization-only",
    "formalization only",
    "not outreach",
    "pure formalization",
)

CLOSED_PATTERNS = (
    "solved",
    "disproved",
    "overtaken",
    "literature closed",
    "not open",
)

PUBLISHABLE_DISPLAY_PATTERNS = (
    "paper",
    "short note",
    "research note",
    "research memo",
    "public artifact",
    "public certificate",
    "certificate package",
    "certificate archive",
    "certificate registry",
    "verifier",
    "reproducible",
    "registry",
    "forum",
    "github",
    "blog comment",
    "arxiv",
    "appendix",
    "theorem",
    "counterexample",
    "construction",
    "classification",
    "obstruction",
)

PRIVATE_CONTACT_PATTERNS = (
    "author email",
    "private email",
    "email_authors",
    "email authors",
    "workshop_author_email",
    "private outreach",
)

PUBLISHABLE_MIN_TOPIC_SCORE = 8
PUBLISHABLE_MIN_TOTAL_SCORE = 16
PUBLISHABLE_MIN_NOVELTY_SCORE = 8

LOW_IMPACT_SOURCE_PATTERNS = (
    "arxiv.org",
)

HIGH_IMPACT_SOURCE_PATTERNS = (
    "github.com/google-deepmind/formal-conjectures",
    "formal-conjectures",
)

FRONTIER_TITLE_PATTERNS = (
    "hadwiger",
    "ramsey",
    "r(5,5)",
    "hadamard",
    "maxdet",
    "projective plane",
    "barnette",
    "certificate frontier",
    "formal conjecture",
)


@dataclass
class DisplayPlan:
    kind: str
    venue: str
    artifact: str
    audience: str
    success_gate: str


@dataclass
class PreflightVerdict:
    todo_id: str
    slug: str
    title: str
    verdict: str
    display: DisplayPlan
    reasons: list[str] = field(default_factory=list)
    missing: list[str] = field(default_factory=list)
    risk_flags: list[str] = field(default_factory=list)
    score: int = 0

    def to_dict(self) -> dict:
        d = asdict(self)
        return d


def _contains_any(text: str, patterns: tuple[str, ...]) -> bool:
    lower = (text or "").lower()
    return any(pat.lower() in lower for pat in patterns)


def _status_skip(status: str) -> bool:
    return _contains_any(status, SKIP_STATUS_PATTERNS)


def _closed_signal(todo: TodoSpec) -> bool:
    status = (todo.status or "").lower()
    type_ = (todo.type_ or "").lower()
    untouched = (todo.untouched or "").lower()
    if _status_skip(todo.status):
        return True
    if re.search(r"\b(closed|solved|disproved|discarded|overtaken)\b", status):
        return True
    if re.match(r"\s*(disproved|solved|theorem)\b", type_):
        return True
    if "not open" in type_ or "not a stated open problem" in type_:
        return True
    if any(s in untouched for s in ("not open", "已被证明", "猜想已被证明", "proved)", "proved ")):
        return True
    return False


def _display_plan(todo: TodoSpec) -> DisplayPlan:
    sub = todo.submission_target()
    slug = todo.slug()
    source = todo.source or ""
    explicit_display = getattr(todo, "final_display", "") or ""
    explicit_gate = getattr(todo, "success_gate", "") or ""
    profile_display = ""
    profile_gate = ""
    profile, errors = load_profile(slug)
    if profile is not None and not errors:
        profile_display = profile.final_display_form
        profile_gate = profile.success_gate
    display = explicit_display or profile_display
    gate = explicit_gate or profile_gate
    if "erdosproblems.com" in source:
        return DisplayPlan(
            kind=display or "forum_comment_plus_registry_update",
            venue=sub["venue"],
            artifact=f"tools/community-outreach/targets/{slug}/submission_draft.md",
            audience="problem-page readers and erdosproblems maintainers",
            success_gate=gate or "final markdown preview approved by operator; claim scoped to proof/certificate actually produced",
        )
    if "openproblemgarden.org" in source:
        return DisplayPlan(
            kind=display or "opg_comment_or_author_email",
            venue=sub["venue"],
            artifact=f"tools/community-outreach/targets/{slug}/submission_draft.md",
            audience="OPG maintainers, original proposers, and adjacent specialists",
            success_gate=gate or "operator-approved comment/email with exact theorem statement and reproducible artifact links",
        )
    if "arxiv.org" in source:
        return DisplayPlan(
            kind=display or "author_email_or_followup_note",
            venue=sub["venue"],
            artifact=f"tools/community-outreach/targets/{slug}/research_note.tex",
            audience="paper authors and potential follow-up readers",
            success_gate=gate or "self-contained note or precise author email; no external claim without bibliography check",
        )
    if "terrytao.wordpress.com" in source:
        return DisplayPlan(
            kind=display or "blog_comment",
            venue=sub["venue"],
            artifact=f"tools/community-outreach/targets/{slug}/blog_comment.md",
            audience="blog thread participants",
            success_gate=gate or "operator-approved comment that states the narrow contribution and caveats",
        )
    if "aimpl.org" in source:
        return DisplayPlan(
            kind=display or "workshop_author_email",
            venue=sub["venue"],
            artifact=f"tools/community-outreach/targets/{slug}/author_email.md",
            audience="AimPL problem authors or workshop contacts",
            success_gate=gate or "operator-approved email with reproducible scripts/proofs attached or linked",
        )
    return DisplayPlan(
        kind=display or "unknown_outreach_surface",
        venue=sub["venue"],
        artifact=f"tools/community-outreach/targets/{slug}/submission_draft.md",
        audience="profile-specified audience" if display else "unknown",
        success_gate=gate or "must be specified before running research loop",
    )


def _has_registered_profile(todo: TodoSpec) -> bool:
    if todo.todo_id in REGISTERED_SUPERVISOR_PROFILES:
        return True
    profile, errors = load_profile(todo.slug())
    return profile is not None and not errors


def _freshness_judge_errors(slug: str) -> list[str]:
    path = TARGETS_DIR / slug / "freshness_judge.json"
    if not path.exists():
        return [f"freshness_judge missing: {path.relative_to(SCRIPT_DIR)}"]
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [f"freshness_judge unreadable: {exc}"]
    if data.get("verdict") != "pass":
        return [f"freshness_judge verdict is {data.get('verdict')!r}, expected pass"]
    if not data.get("checked_at"):
        return ["freshness_judge missing checked_at"]
    if not data.get("judge"):
        return ["freshness_judge missing judge"]
    return []


def _profile_target_lane(profile) -> str:
    contract = getattr(profile, "science_contract", None)
    return str(getattr(contract, "target_lane", "") or "").strip()


def _is_collaboration_lane(todo: TodoSpec, profile) -> bool:
    lane = _profile_target_lane(profile)
    if lane == "collaboration_lane":
        return True
    haystack = " ".join(
        [
            todo.title or "",
            todo.status or "",
            todo.type_ or "",
            getattr(todo, "final_display", "") or "",
            getattr(profile, "final_display_form", "") if profile is not None else "",
        ]
    ).lower()
    return bool(re.search(r"\b(collaboration|collaborator|paper[- ]trade|email thread)\b", haystack))


def _has_publishable_terminal_surface(text: str) -> bool:
    lower = " ".join(str(text or "").lower().split())
    return any(pat in lower for pat in PUBLISHABLE_DISPLAY_PATTERNS)


def _looks_private_only_terminal_surface(text: str) -> bool:
    lower = " ".join(str(text or "").lower().split())
    if not lower:
        return False
    has_private = any(pat in lower for pat in PRIVATE_CONTACT_PATTERNS)
    return has_private and not _has_publishable_terminal_surface(lower)


def _contract_quality_value(science_gate, key: str, default: int = 0) -> int:
    quality = getattr(science_gate, "contract_quality", {}) or {}
    if isinstance(quality, dict):
        value = quality.get(key, default)
    else:
        value = getattr(quality, key, default)
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _is_high_impact_public_source(todo: TodoSpec) -> bool:
    source = (todo.source or "").lower()
    title = (todo.title or "").lower()
    if any(pat in source for pat in HIGH_IMPACT_SOURCE_PATTERNS):
        return True
    return any(pat in title for pat in FRONTIER_TITLE_PATTERNS)


def _is_derivative_recent_arxiv_only(todo: TodoSpec, display_blob: str) -> bool:
    source = (todo.source or "").lower()
    text = " ".join(
        [
            todo.title or "",
            todo.statement or "",
            todo.untouched or "",
            display_blob or "",
        ]
    ).lower()
    if not any(pat in source for pat in LOW_IMPACT_SOURCE_PATTERNS):
        return False
    if _is_high_impact_public_source(todo):
        return False
    derivative_markers = (
        "author email",
        "author-facing",
        "follow-up",
        "small",
        "table",
        "compute",
        "recent arxiv",
        "arxiv:",
        "private outreach",
    )
    return any(marker in text for marker in derivative_markers)


def judge(todo: TodoSpec) -> PreflightVerdict:
    display = _display_plan(todo)
    reasons: list[str] = []
    missing: list[str] = []
    risk_flags: list[str] = []
    fit = todo.fit_score or 0
    topic = todo.topic_score or 0
    score = fit + topic
    status_blob = " ".join(
        [
            todo.status or "",
            todo.type_ or "",
            todo.untouched or "",
        ]
    )

    if _contains_any(status_blob, HANDOFF_PATTERNS):
        reasons.append("board marks this as formalization/handoff rather than outreach")
        return PreflightVerdict(todo.todo_id, todo.slug(), todo.title, HANDOFF, display, reasons, score=0)

    if _closed_signal(todo):
        reasons.append(f"status/prior indicates closed, solved, overtaken, or otherwise skipped: {todo.status}")
        return PreflightVerdict(todo.todo_id, todo.slug(), todo.title, DROP, display, reasons, score=0)

    if "unknown" in display.kind:
        missing.append("submission surface is unknown")

    if not todo.statement.strip():
        missing.append("precise Statement block")
    if not todo.prior.strip():
        # Freshness is an audit signal, not a hard research blocker.  The
        # harness should be allowed to start deep reasoning on a promising
        # target and let the freshness/science gates bound what can be
        # written back or sent externally.
        risk_flags.append("missing Prior block / freshness baseline")
    if not todo.omega_fit_detail.strip():
        missing.append("Omega fit detail with concrete library paths")
    if not todo.attack_plan:
        missing.append("numbered Attack plan")

    profile, profile_errors = load_profile(todo.slug())
    registered_legacy = todo.todo_id in REGISTERED_SUPERVISOR_PROFILES
    if profile is not None and profile.slug != todo.slug():
        missing.append(f"profile slug mismatch: {profile.slug} != board slug {todo.slug()}")

    if not registered_legacy and (profile is None or profile_errors):
        missing.append("valid target-specific profile.json")
    elif profile is not None and profile.slug == todo.slug() and (profile.freshness_required or profile.oracle_judge_required):
        freshness_errors = _freshness_judge_errors(todo.slug())
        if freshness_errors:
            risk_flags.extend(f"freshness gate warning: {e}" for e in freshness_errors)
    if profile is not None and profile.slug == todo.slug():
        display_blob = " ".join(
            [
                display.kind or "",
                display.artifact or "",
                display.audience or "",
                display.success_gate or "",
                profile.final_display_form or "",
                profile.fallback_contribution or "",
            ]
        )
        if not _is_collaboration_lane(todo, profile):
            if not _has_publishable_terminal_surface(display_blob):
                missing.append("publishable/public terminal artifact for non-collaboration target")
            elif _looks_private_only_terminal_surface(display_blob):
                missing.append("non-collaboration target cannot terminate in private/author email only")
        science_gate = contract_from_profile(todo)
        if science_gate.status != CONTRACT_READY:
            missing.extend(f"science gate: {m}" for m in science_gate.missing)
            risk_flags.append(f"science_gate={science_gate.status}")
        elif not _is_collaboration_lane(todo, profile):
            lane = getattr(science_gate, "target_lane", "") or _profile_target_lane(profile)
            novelty = _contract_quality_value(science_gate, "novelty_score")
            frontier_like = lane == "frontier_lane" or _is_high_impact_public_source(todo)
            if topic < PUBLISHABLE_MIN_TOPIC_SCORE and not frontier_like:
                missing.append(
                    f"publishable-value gate: topic_score={topic} < {PUBLISHABLE_MIN_TOPIC_SCORE}"
                )
            if score < PUBLISHABLE_MIN_TOTAL_SCORE and not frontier_like:
                missing.append(
                    f"publishable-value gate: fit+topic={score} < {PUBLISHABLE_MIN_TOTAL_SCORE}"
                )
            if novelty < PUBLISHABLE_MIN_NOVELTY_SCORE and not frontier_like:
                missing.append(
                    f"publishable-value gate: novelty_score={novelty} < {PUBLISHABLE_MIN_NOVELTY_SCORE}"
                )
            if _is_derivative_recent_arxiv_only(todo, display_blob) and not frontier_like:
                missing.append("publishable-value gate: derivative arXiv follow-up needs explicit public significance")

    if fit < 7:
        risk_flags.append(f"low Omega fit ({fit}/10)")
    if topic < 5:
        risk_flags.append(f"low topic value ({topic}/10)")
    if re.search(r"\bhigh\b", todo.risk or "", re.IGNORECASE):
        risk_flags.append("board risk is high")

    if missing:
        verdict = NEEDS_PROFILE if any("profile" in m for m in missing) else NEEDS_BOARD_UPDATE
        reasons.append("preflight missing required run metadata/artifacts")
        return PreflightVerdict(
            todo.todo_id, todo.slug(), todo.title, verdict, display,
            reasons=reasons, missing=missing, risk_flags=risk_flags, score=score,
        )

    reasons.append("has open-problem surface, display plan, runnable profile, and science contract")
    return PreflightVerdict(
        todo.todo_id, todo.slug(), todo.title, RUN, display,
        reasons=reasons, risk_flags=risk_flags, score=score,
    )


def judge_board(path: Path = BOARD_PATH) -> list[PreflightVerdict]:
    todos = parse_board(path)
    verdicts = [judge(t) for t in todos.values()]
    verdicts.sort(key=lambda v: (v.verdict != RUN, -v.score, v.todo_id))
    return verdicts


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--todo-id", default="", help="only judge one T-NN")
    p.add_argument("--json", action="store_true", help="emit JSON")
    p.add_argument("--actionable-only", action="store_true", help="show only RUN entries")
    args = p.parse_args(argv)

    rows = judge_board()
    if args.todo_id:
        rows = [r for r in rows if r.todo_id == args.todo_id]
    if args.actionable_only:
        rows = [r for r in rows if r.verdict in ACTIONABLE_VERDICTS]

    if args.json:
        print(json.dumps([r.to_dict() for r in rows], ensure_ascii=False, indent=2))
        return 0

    if not rows:
        print("No matching targets.")
        return 0

    for r in rows:
        print(f"{r.todo_id} {r.verdict:18} score={r.score:2d} slug={r.slug} :: {r.title}")
        print(f"  display: {r.display.kind} -> {r.display.artifact}")
        if r.reasons:
            print("  reason: " + "; ".join(r.reasons))
        if r.missing:
            print("  missing: " + "; ".join(r.missing))
        if r.risk_flags:
            print("  risks: " + "; ".join(r.risk_flags))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
