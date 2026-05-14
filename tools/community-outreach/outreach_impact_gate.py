#!/usr/bin/env python3
"""Structured outreach-impact gate for completed research targets.

Science gate decides whether the mathematics/evidence is ready. This gate
decides the best operator-reviewed public surface once the science gate is
ready: short note, author email, forum/registry comment, GitHub comment, X
thread, paper writeback, or a multi-channel packet.

It never sends anything. It writes a ledger under targets/<slug>/ so the
supervisor/research loop can surface a concrete review plan to the operator.
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
BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"
LEDGER_NAME = "outreach_impact_gate.json"

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_board_parser import TodoSpec, parse_board  # noqa: E402
from outreach_profile import load_profile  # noqa: E402
from outreach_science_gate import (  # noqa: E402
    BOARD_SKIPPED as SCIENCE_BOARD_SKIPPED,
    CLOSE_TARGET,
    WRITEBACK_READY,
    evaluate as science_gate_evaluate,
    ledger_path as science_ledger_path,
)


NEEDS_RESEARCH = "NEEDS_RESEARCH"
IMPACT_PLAN_READY = "IMPACT_PLAN_READY"
NEEDS_PUBLICATION_VALUE = "NEEDS_PUBLICATION_VALUE"
CLOSE_OR_ARCHIVE = "CLOSE_OR_ARCHIVE"
BOARD_SKIPPED = "BOARD_SKIPPED"


@dataclass
class ImpactGateVerdict:
    todo_id: str
    slug: str
    title: str
    status: str
    science_status: str
    primary_channel: str = ""
    channels: list[str] = field(default_factory=list)
    audience: str = ""
    draft_paths: list[str] = field(default_factory=list)
    channel_sequence: list[dict] = field(default_factory=list)
    impact_contract: dict = field(default_factory=dict)
    prohibited_actions: list[str] = field(default_factory=list)
    impact_score: int = 0
    rationale: list[str] = field(default_factory=list)
    required_before_send: list[str] = field(default_factory=list)
    operator_approval_required: bool = True
    next_action: str = "continue_research"

    def to_dict(self) -> dict:
        return asdict(self)


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def ledger_path(slug: str) -> Path:
    return TARGETS_DIR / slug / LEDGER_NAME


def _target_file(slug: str, name: str) -> str:
    return f"tools/community-outreach/targets/{slug}/{name}"


def _source_channel(todo: TodoSpec) -> tuple[str, str]:
    source = (todo.source or "").lower()
    if "arxiv.org" in source:
        return "author_email", "paper authors and adjacent arXiv readers"
    if "github.com" in source:
        return "github_comment", "issue/PR maintainers and repository contributors"
    if "erdosproblems.com" in source:
        return "registry_comment", "problem-page readers and maintainers"
    if "openproblemgarden.org" in source:
        return "opg_comment", "OPG maintainers, proposers, and nearby specialists"
    if "problemsilike.com" in source:
        return "problem_page_comment", "Problems I Like readers, problem owner, and nearby specialists"
    if "terrytao.wordpress.com" in source or "wordpress.com" in source:
        return "blog_comment", "blog-thread participants and specialist readers"
    if "aimpl" in source:
        return "author_email", "workshop problem authors and collaborators"
    if "x.com" in source or "twitter.com" in source:
        return "x_reply_or_thread", "X thread readers plus source author"
    return "private_author_email", "source authors or maintainers"


def _artifact_text(slug: str, max_chars: int = 120000) -> str:
    target_dir = TARGETS_DIR / slug
    parts: list[str] = []
    for name in ("research.md", "submission_draft.md", "submission_draft_final.md", "blog_comment.md", "author_email.md"):
        p = target_dir / name
        if p.exists() and p.is_file():
            try:
                parts.append(p.read_text(encoding="utf-8", errors="replace")[:40000])
            except OSError:
                pass
    return "\n\n".join(parts)[:max_chars]


def _has_strong_public_claim(text: str) -> bool:
    lower = text.lower()
    return any(
        marker in lower
        for marker in (
            "proof complete",
            "proved",
            "theorem",
            "counterexample",
            "verified certificate",
            "certificate verified",
            "reproducible",
            "breakthrough",
        )
    )


def _science_field(science, slug: str, key: str, default: str = "") -> str:
    value = getattr(science, key, "") or ""
    if value:
        return str(value)
    try:
        ledger = json.loads(science_ledger_path(slug).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return default
    return str(ledger.get(key) or default)


def _science_from_ledger(slug: str) -> dict:
    try:
        return json.loads(science_ledger_path(slug).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def _is_scoped_negative_or_obstruction(text: str) -> bool:
    """Detect useful negative packets that must not be marketed as solutions.

    These are often worth sending to authors or turning into a short note, but
    the public claim is "this route/bridge/certificate fails or is corrected",
    not "the original open problem is solved".
    """
    lower = text.lower()
    markers = (
        "no theorem is claimed",
        "theta_lower_bound_proved\": false",
        "candidate_bridge_refuted",
        "bridge is false",
        "bridge lemma",
        "counterexample",
        "failure analysis",
        "cannot be used to prove",
        "re-scope",
        "obstruction",
    )
    return any(marker in lower for marker in markers)


def _is_bounded_progress_packet(text: str) -> bool:
    lower = text.lower()
    markers = (
        "bounded computational theorem packet",
        "bounded finite computational certificate",
        "finite-domain certificate",
        "finite-domain maximum-multiplicity certificate",
        "full pascal multiplicity max",
        "exact enumeration of pascal",
        "declared finite domain",
        "coverage certificate",
        "finite theorem",
        "finite exact range",
        "global_conjecture_status\":\"not_proved_by_this_packet",
        "the all-n conjecture is not proved here",
        "does not prove conjecture",
        "not a proof of singmaster",
        "not a global claim",
    )
    return any(marker in lower for marker in markers)


def _is_publishable_channel(channel: str) -> bool:
    return channel in {
        "short_note",
        "reproducible_certificate_note",
        "registry_comment",
        "problem_page_comment",
        "opg_comment",
        "blog_comment",
        "github_comment",
        "automath_project_update",
        "x_thread",
        "paper_writeback",
    }


def _is_curated_problemsilike(todo: TodoSpec) -> bool:
    return "problemsilike.com" in (todo.source or "").lower()


def _is_collaboration_context(lane: str, display: str, todo: TodoSpec) -> bool:
    haystack = " ".join([lane, display, todo.title or "", getattr(todo, "type_", "") or "", todo.status or ""]).lower()
    return bool(re.search(r"\b(collaboration|collaborate|reply|email thread|waiting reply|frontier subset|paper-trade)\b", haystack))


def _append_unique(xs: list[str], item: str) -> None:
    if item and item not in xs:
        xs.append(item)


def _channel_sequence(primary: str, channels: list[str]) -> list[dict]:
    sequence: list[dict] = []
    for channel in channels:
        if channel == primary:
            timing = "first"
        elif channel in {"short_note", "reproducible_certificate_note", "automath_project_update"}:
            timing = "before_or_with_primary" if primary in {"author_email", "private_author_email"} else "after_primary"
        elif channel == "x_thread":
            timing = "after_reviewed_note_or_email"
        else:
            timing = "after_primary_if_operator_approves"
        sequence.append({
            "channel": channel,
            "timing": timing,
            "send_gate": "operator_approved_exact_text",
        })
    return sequence


def _impact_contract(
    *,
    primary: str,
    channels: list[str],
    science_status: str,
    contribution: str,
    strong_claim: bool,
    topic: int,
    fit: int,
    scoped_negative: bool = False,
    bounded_progress: bool = False,
) -> dict:
    disclosure = "private_first" if primary in {"author_email", "private_author_email"} else "public_first"
    if "short_note" in channels or "reproducible_certificate_note" in channels:
        disclosure = "note_or_certificate_first"
    if scoped_negative:
        claim_strength = "scoped_negative_or_obstruction_claim"
    elif bounded_progress:
        claim_strength = "bounded_finite_certificate_claim"
    else:
        claim_strength = "strong_public_claim" if strong_claim else "scoped_or_preliminary_claim"
    return {
        "goal": "maximize community impact without outrunning the mathematical evidence",
        "science_gate_required": science_status,
        "primary_channel": primary,
        "secondary_channels": [ch for ch in channels if ch != primary],
        "disclosure_order": disclosure,
        "claim_strength": claim_strength,
        "contribution_type": contribution or "unknown",
        "topic_score": topic,
        "automath_fit_score": fit,
        "operator_decision_needed": [
            "approve exact send/post text",
            "choose whether Automath/NewMath positioning belongs in this outreach packet",
            "choose whether public channels should wait for author/source response",
        ],
    }


def evaluate(todo: TodoSpec) -> ImpactGateVerdict:
    science = science_gate_evaluate(todo)
    profile, _ = load_profile(todo.slug())
    source_channel, source_audience = _source_channel(todo)
    slug = todo.slug()
    text = _artifact_text(slug)
    topic = int(todo.topic_score or 0)
    fit = int(todo.fit_score or 0)
    contribution = _science_field(science, slug, "contribution_type").lower()
    lane = _science_field(science, slug, "target_lane")
    display = str(getattr(profile, "final_display_form", "") if profile else "")
    collaboration_context = _is_collaboration_context(lane, display, todo)

    pending_review = "pending user approval" in (todo.status or "").lower()
    ledger = _science_from_ledger(slug) if pending_review else {}
    ledger_status = str(ledger.get("status") or "")
    if science.status == SCIENCE_BOARD_SKIPPED or re.search(
        r"\b(OPERATOR_DEPRIORITIZED|OPERATOR PAUSED|PAUSED|SHELVED)\b",
        todo.status or "",
        re.I,
    ):
        return ImpactGateVerdict(
            todo_id=todo.todo_id,
            slug=slug,
            title=todo.title,
            status=BOARD_SKIPPED,
            science_status=science.status,
            next_action="skip",
            rationale=["board/science gate says this target is skipped"],
        )
    effective_science_status = ledger_status or (WRITEBACK_READY if pending_review else science.status)
    if effective_science_status == CLOSE_TARGET:
        return ImpactGateVerdict(
            todo_id=todo.todo_id,
            slug=slug,
            title=todo.title,
            status=CLOSE_OR_ARCHIVE,
            science_status=science.status,
            primary_channel="internal_archive_note",
            channels=["internal_archive_note"],
            audience="operator and future pipeline agents",
            draft_paths=[_target_file(slug, "research.md")],
            channel_sequence=[{
                "channel": "internal_archive_note",
                "timing": "first",
                "send_gate": "operator_archive_review",
            }],
            impact_contract={
                "goal": "preserve negative evidence and decide whether it is useful externally",
                "science_gate_required": science.status,
                "primary_channel": "internal_archive_note",
                "secondary_channels": [],
                "disclosure_order": "internal_only_by_default",
                "operator_decision_needed": ["decide whether the obstruction is worth externalizing"],
            },
            prohibited_actions=["external_send", "public_post", "claim_problem_solved"],
            impact_score=max(1, min(5, topic // 2)),
            rationale=["science gate indicates closure, obstruction, or hard no-progress"],
            required_before_send=["Do not send externally unless the operator explicitly decides the negative result is useful."],
            next_action="operator_archive_review",
        )
    if effective_science_status != WRITEBACK_READY:
        next_action = "profile_judge" if str(science.next_action) == "profile_judge" else "continue_deep_reason"
        requirement = (
            "Create or repair a gate-clean science_contract before deep research."
            if next_action == "profile_judge"
            else "Satisfy science_gate=WRITEBACK_READY before drafting public outreach."
        )
        return ImpactGateVerdict(
            todo_id=todo.todo_id,
            slug=slug,
            title=todo.title,
            status=NEEDS_RESEARCH,
            science_status=effective_science_status,
            primary_channel="none",
            channels=[],
            audience="internal research loop",
            draft_paths=[_target_file(slug, "research.md")],
            impact_contract={
                "goal": "continue research until science gate is ready",
                "science_gate_required": WRITEBACK_READY,
                "primary_channel": "none",
                "secondary_channels": [],
                "disclosure_order": "no_external_disclosure",
                "operator_decision_needed": [],
            },
            prohibited_actions=["external_send", "public_post", "draft_as_solved_result"],
            impact_score=0,
            rationale=["science evidence is not ready; impact planning waits for a real result"],
            required_before_send=[requirement],
            next_action=next_action,
        )

    channels: list[str] = []
    rationale: list[str] = []
    _append_unique(channels, source_channel)
    rationale.append(f"source surface points to {source_channel}")

    strong_claim = _has_strong_public_claim(text)
    scoped_negative = _is_scoped_negative_or_obstruction(text)
    bounded_progress = _is_bounded_progress_packet(text)
    if bounded_progress:
        scoped_negative = False
    if scoped_negative:
        strong_claim = False
        rationale.append("artifact is a scoped negative/obstruction packet, not a solved-problem claim")
    elif bounded_progress:
        strong_claim = False
        rationale.append("artifact is a bounded progress packet; frame as finite theorem/certificate plus reduction, not as the full conjecture")
    if contribution in {"theorem", "counterexample", "construction", "research_note"} or strong_claim or scoped_negative:
        _append_unique(channels, "short_note")
        if scoped_negative:
            rationale.append("negative evidence should be preserved as a citable obstruction/certificate note")
        elif bounded_progress:
            rationale.append("bounded finite theorem/certificate should be preserved as a citable short note")
        else:
            rationale.append("mathematical claim should be preserved as a citable short note")
    if "certificate" in contribution or "computational" in contribution or "results.json" in text:
        _append_unique(channels, "reproducible_certificate_note")
        rationale.append("certificate/computation needs a reproducibility-first artifact")
    if topic >= 8 and strong_claim and not scoped_negative:
        _append_unique(channels, "x_thread")
        rationale.append("high-topic verified result deserves a concise X visibility thread after review")
    if fit >= 8 and (strong_claim or scoped_negative or bounded_progress):
        _append_unique(channels, "automath_project_update")
        if scoped_negative:
            rationale.append("Automath-facing update should frame this as gate-caught negative evidence")
        elif bounded_progress:
            rationale.append("Automath-facing update should frame this as finite verified progress and a next-proof reduction")
        else:
            rationale.append("strong Automath fit should backflow into project-facing update material")
    if collaboration_context:
        _append_unique(channels, "author_email")
        rationale.append("collaboration lane should use direct email first; secondary channels remain available after the reviewed note exists")

    serious_math_claim = strong_claim and contribution in {"theorem", "counterexample", "construction", "research_note"}
    curated_problem_result = _is_curated_problemsilike(todo) and (strong_claim or scoped_negative)
    serious_certificate = (
        "certificate" in contribution
        and strong_claim
        and not bounded_progress
        and not scoped_negative
        and topic >= 8
    )
    if (
        not collaboration_context
        and not serious_math_claim
        and not curated_problem_result
        and not serious_certificate
    ):
        if bounded_progress or scoped_negative or "computational" in contribution or "certificate" in contribution:
            return ImpactGateVerdict(
                todo_id=todo.todo_id,
                slug=slug,
                title=todo.title,
                status=NEEDS_PUBLICATION_VALUE,
                science_status=effective_science_status,
                primary_channel="none",
                channels=[],
                audience="internal research loop",
                draft_paths=[_target_file(slug, "research.md")],
                impact_contract={
                    "goal": "defer low-publication-value bounded/audit output and keep the main loop focused on real mathematical contributions",
                    "science_gate_required": WRITEBACK_READY,
                    "primary_channel": "none",
                    "secondary_channels": [],
                    "disclosure_order": "no_external_disclosure",
                    "claim_strength": (
                        "bounded_or_obstruction_record_not_publication_grade"
                        if (bounded_progress or scoped_negative)
                        else "computational_record_not_publication_grade"
                    ),
                    "operator_decision_needed": [
                        "only revive if the operator explicitly asks to publish this scoped record",
                        "otherwise continue toward a full proof, counterexample, high-impact certificate, or Problems I Like target",
                    ],
                },
                prohibited_actions=["external_send", "public_post", "draft_as_solved_result"],
                impact_score=0,
                rationale=[
                    "science gate found a locally verified scoped record, but current project policy prioritizes real mathematical contributions",
                    "bounded/audit/obstruction packets should not interrupt operator review unless they solve a curated target or support a serious public result",
                ],
                required_before_send=[
                    "Strengthen into a full proof/counterexample/high-impact certificate or combine into a serious note before outreach."
                ],
                next_action="continue_deep_reason",
            )

    if not collaboration_context and not any(_is_publishable_channel(ch) for ch in channels):
        return ImpactGateVerdict(
            todo_id=todo.todo_id,
            slug=slug,
            title=todo.title,
            status=NEEDS_PUBLICATION_VALUE,
            science_status=effective_science_status,
            primary_channel="none",
            channels=[],
            audience="internal research loop",
            draft_paths=[_target_file(slug, "research.md")],
            impact_contract={
                "goal": "upgrade the target from private follow-up to publishable/public mathematical contribution",
                "science_gate_required": WRITEBACK_READY,
                "primary_channel": "none",
                "secondary_channels": [],
                "disclosure_order": "no_external_disclosure",
                "operator_decision_needed": ["decide whether to strengthen, merge into a larger note, or archive"],
            },
            prohibited_actions=["external_send", "public_post", "private_email_as_terminal_goal"],
            impact_score=0,
            rationale=[
                "non-collaboration target lacks a publishable/public terminal artifact",
                "private email or minor follow-up is not enough for current research lanes",
            ],
            required_before_send=[
                "Strengthen into a paper/short note/public certificate/verifier/serious registry contribution before any outreach."
            ],
            next_action="continue_deep_reason",
        )

    primary = "author_email" if "author_email" in channels else (channels[0] if channels else source_channel)
    draft_paths = [_target_file(slug, "research.md")]
    for ch in channels:
        if ch in {"author_email", "private_author_email"}:
            _append_unique(draft_paths, _target_file(slug, "author_email.md"))
        elif ch in {"registry_comment", "problem_page_comment", "opg_comment", "blog_comment", "github_comment", "x_reply_or_thread"}:
            _append_unique(draft_paths, _target_file(slug, "submission_draft.md"))
        elif ch == "x_thread":
            _append_unique(draft_paths, f"tools/community-outreach/drafts/{slug}_tweet.txt")
        elif ch in {"short_note", "reproducible_certificate_note"}:
            _append_unique(draft_paths, _target_file(slug, "research_note.md"))

    required = [
        "Operator must approve the exact final text before any external send/post.",
        "Every public claim must cite the source target and link or attach reproducible evidence.",
        "Separate mathematical evidence from Automath/NewMath positioning; do not overclaim a solved open problem.",
    ]
    if scoped_negative:
        required.append("Frame the contribution as an obstruction/counterexample to a proof route unless a separate theorem proof is present.")
    if bounded_progress:
        required.append("Frame the contribution as bounded finite verified progress unless a separate all-n proof is present.")
    if "x_thread" in channels:
        required.append("X thread must be derivative of the reviewed note/email, not the first disclosure.")
    if "author_email" in channels or "private_author_email" in channels:
        required.append("Email draft must use the operator-approved sending account and remain a draft until approval.")

    impact_score = min(
        10,
        max(4, topic + (2 if strong_claim else 0) + (1 if scoped_negative else 0) + (1 if len(channels) >= 3 else 0)),
    )
    return ImpactGateVerdict(
        todo_id=todo.todo_id,
        slug=slug,
        title=todo.title,
        status=IMPACT_PLAN_READY,
            science_status=effective_science_status,
        primary_channel=primary,
        channels=channels,
        audience=source_audience,
        draft_paths=draft_paths,
        channel_sequence=_channel_sequence(primary, channels),
        impact_contract=_impact_contract(
            primary=primary,
            channels=channels,
            science_status=effective_science_status,
            contribution=contribution,
            strong_claim=strong_claim,
            topic=topic,
            fit=fit,
            scoped_negative=scoped_negative,
            bounded_progress=bounded_progress,
        ),
        prohibited_actions=[
            "send_email_without_operator_approval",
            "post_to_x_without_operator_approval",
            "post_forum_or_github_comment_without_operator_approval",
            "describe_preliminary_or_computational_evidence_as_a_full_solution",
        ],
        impact_score=impact_score,
        rationale=rationale,
        required_before_send=required,
        operator_approval_required=True,
        next_action="operator_review",
    )


def write_ledger(row: ImpactGateVerdict) -> Path:
    path = ledger_path(row.slug)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "checked_at": _now_iso(),
        **row.to_dict(),
    }
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return path


def evaluate_board(path: Path = BOARD_PATH) -> list[ImpactGateVerdict]:
    return [evaluate(todo) for todo in parse_board(path).values()]


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--todo-id", default="")
    p.add_argument("--json", action="store_true")
    p.add_argument("--write-ledger", action="store_true")
    args = p.parse_args(argv)

    rows = evaluate_board()
    if args.todo_id:
        rows = [r for r in rows if r.todo_id == args.todo_id]
    if args.write_ledger:
        for row in rows:
            write_ledger(row)
    if args.json:
        print(json.dumps([r.to_dict() for r in rows], ensure_ascii=False, indent=2))
        return 0
    for row in rows:
        print(
            f"{row.todo_id} {row.status} science={row.science_status} "
            f"primary={row.primary_channel or '-'} channels={','.join(row.channels) or '-'} :: {row.title}"
        )
        if row.rationale:
            print("  rationale: " + "; ".join(row.rationale[:3]))
        if row.required_before_send:
            print("  gate: " + row.required_before_send[0])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
