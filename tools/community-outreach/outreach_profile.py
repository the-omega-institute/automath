#!/usr/bin/env python3
"""Data schema for target-specific outreach run profiles.

A board entry cannot enter the research loop merely because it is interesting.
It needs a profile: final display form, success gate, expected artifacts, safe
first experiments, fallback contribution, and explicit no-send policy.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
TARGETS_DIR = SCRIPT_DIR / "targets"
BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_board_parser import TodoSpec, parse_board  # noqa: E402


SCHEMA_VERSION = "outreach-target-profile-v1"


@dataclass
class ExperimentSpec:
    label: str
    command: list[str] = field(default_factory=list)
    expected_outputs: list[str] = field(default_factory=list)
    success_predicate: str = ""
    timeout_s: int = 1800


@dataclass
class TasteObligations:
    novelty_witness: str
    no_hidden_assumption_witness: str
    reproducibility_witness: str
    layer_separation_witness: str


@dataclass
class ScienceContract:
    contribution_type: str
    terminal_artifact: str
    verifier: str
    progress_metric: str
    target_lane: str = ""
    contract_quality_floor: int = 7
    origin: str = "ai"
    closure_status: str = "seed"
    verification_status: str = "unverified"
    outreach_status: str = "not_drafted"
    evidence_required: list[str] = field(default_factory=list)
    writeback_when: list[str] = field(default_factory=list)
    close_when: list[str] = field(default_factory=list)
    no_progress_patience_turns: int = 2
    taste_obligations: TasteObligations | None = None


@dataclass
class OutreachProfile:
    schema_version: str
    todo_id: str
    slug: str
    title: str
    source_url: str
    final_display_form: str
    success_gate: str
    profile_status: str = "draft"
    no_external_send_without_operator_approval: bool = True
    canonical_draft_paths: list[str] = field(default_factory=list)
    expected_artifacts: list[str] = field(default_factory=list)
    first_experiments: list[ExperimentSpec] = field(default_factory=list)
    fallback_contribution: str = ""
    science_contract: ScienceContract | None = None
    main_paper_bridge: dict = field(default_factory=dict)
    oracle_judge_required: bool = True
    freshness_required: bool = True
    notes: str = ""

    def to_dict(self) -> dict:
        return asdict(self)


def profile_path_for_slug(slug: str) -> Path:
    return TARGETS_DIR / slug / "profile.json"


def load_profile(slug: str) -> tuple[OutreachProfile | None, list[str]]:
    path = profile_path_for_slug(slug)
    if not path.exists():
        return None, [f"profile missing: {path.relative_to(SCRIPT_DIR)}"]
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return None, [f"profile unreadable: {exc}"]
    return parse_profile(data)


def parse_profile(data: dict) -> tuple[OutreachProfile | None, list[str]]:
    errors = validate_profile_dict(data)
    if errors:
        return None, errors
    experiments = [
        ExperimentSpec(
            label=str(e.get("label") or ""),
            command=list(e.get("command") or []),
            expected_outputs=list(e.get("expected_outputs") or []),
            success_predicate=str(e.get("success_predicate") or ""),
            timeout_s=int(e.get("timeout_s") or 1800),
        )
        for e in (data.get("first_experiments") or [])
        if isinstance(e, dict)
    ]
    contract_data = data.get("science_contract") or {}
    contract = None
    if isinstance(contract_data, dict):
        taste_data = contract_data.get("taste_obligations") or {}
        taste = None
        if isinstance(taste_data, dict):
            taste = TasteObligations(
                novelty_witness=str(taste_data.get("novelty_witness") or ""),
                no_hidden_assumption_witness=str(taste_data.get("no_hidden_assumption_witness") or ""),
                reproducibility_witness=str(taste_data.get("reproducibility_witness") or ""),
                layer_separation_witness=str(taste_data.get("layer_separation_witness") or ""),
            )
        contract = ScienceContract(
            contribution_type=str(contract_data.get("contribution_type") or ""),
            terminal_artifact=str(contract_data.get("terminal_artifact") or ""),
            verifier=str(contract_data.get("verifier") or ""),
            progress_metric=str(contract_data.get("progress_metric") or ""),
            target_lane=str(contract_data.get("target_lane") or ""),
            contract_quality_floor=int(contract_data.get("contract_quality_floor") or 7),
            origin=str(contract_data.get("origin") or "ai"),
            closure_status=str(contract_data.get("closure_status") or "seed"),
            verification_status=str(contract_data.get("verification_status") or "unverified"),
            outreach_status=str(contract_data.get("outreach_status") or "not_drafted"),
            evidence_required=list(contract_data.get("evidence_required") or []),
            writeback_when=list(contract_data.get("writeback_when") or []),
            close_when=list(contract_data.get("close_when") or []),
            no_progress_patience_turns=int(contract_data.get("no_progress_patience_turns") or 2),
            taste_obligations=taste,
        )
    return OutreachProfile(
        schema_version=str(data.get("schema_version") or SCHEMA_VERSION),
        todo_id=str(data.get("todo_id") or ""),
        slug=str(data.get("slug") or ""),
        title=str(data.get("title") or ""),
        source_url=str(data.get("source_url") or ""),
        profile_status=str(data.get("profile_status") or "draft"),
        final_display_form=str(data.get("final_display_form") or ""),
        success_gate=str(data.get("success_gate") or ""),
        no_external_send_without_operator_approval=bool(
            data.get("no_external_send_without_operator_approval", True)
        ),
        canonical_draft_paths=list(data.get("canonical_draft_paths") or []),
        expected_artifacts=list(data.get("expected_artifacts") or []),
        first_experiments=experiments,
        fallback_contribution=str(data.get("fallback_contribution") or ""),
        science_contract=contract,
        main_paper_bridge=dict(data.get("main_paper_bridge") or {}),
        oracle_judge_required=bool(data.get("oracle_judge_required", True)),
        freshness_required=bool(data.get("freshness_required", True)),
        notes=str(data.get("notes") or ""),
    ), []


def validate_profile_dict(data: dict) -> list[str]:
    errors: list[str] = []
    required = [
        "schema_version",
        "todo_id",
        "slug",
        "title",
        "source_url",
        "profile_status",
        "final_display_form",
        "success_gate",
        "canonical_draft_paths",
        "expected_artifacts",
        "first_experiments",
        "fallback_contribution",
        "science_contract",
    ]
    for key in required:
        if key not in data or data.get(key) in ("", [], None):
            errors.append(f"missing {key}")
    if data.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"schema_version must be {SCHEMA_VERSION}")
    if data.get("profile_status") != "ready":
        errors.append("profile_status must be ready")
    if data.get("no_external_send_without_operator_approval") is not True:
        errors.append("no_external_send_without_operator_approval must be true")
    if not isinstance(data.get("first_experiments"), list):
        errors.append("first_experiments must be a list")
    else:
        for i, exp in enumerate(data.get("first_experiments") or []):
            if not isinstance(exp, dict):
                errors.append(f"first_experiments[{i}] must be object")
                continue
            if not exp.get("label"):
                errors.append(f"first_experiments[{i}] missing label")
            if not exp.get("success_predicate"):
                errors.append(f"first_experiments[{i}] missing success_predicate")
    errors.extend(_validate_science_contract(data.get("science_contract")))
    return errors


def _validate_science_contract(contract: object) -> list[str]:
    errors: list[str] = []
    if not isinstance(contract, dict):
        return ["science_contract must be an object"]
    required_text = [
        "contribution_type",
        "terminal_artifact",
        "verifier",
        "progress_metric",
    ]
    for key in required_text:
        if not str(contract.get(key) or "").strip():
            errors.append(f"science_contract missing {key}")
    contribution_type = str(contract.get("contribution_type") or "").strip()
    allowed = {
        "theorem",
        "counterexample",
        "construction",
        "certificate",
        "computational_record",
        "source_audit_note",
        "collaboration_packet",
        "research_note",
    }
    if contribution_type and contribution_type not in allowed:
        errors.append(
            "science_contract contribution_type must be one of "
            + ", ".join(sorted(allowed))
        )
    target_lane = str(contract.get("target_lane") or "").strip()
    if target_lane and target_lane not in {"math_lane", "frontier_lane", "collaboration_lane", "audit_lane"}:
        errors.append("science_contract target_lane must be math_lane, frontier_lane, collaboration_lane, or audit_lane")
    try:
        floor = int(contract.get("contract_quality_floor") or 7)
    except (TypeError, ValueError):
        floor = 0
    if floor < 7 or floor > 10:
        errors.append("science_contract contract_quality_floor must be between 7 and 10")
    origin = str(contract.get("origin") or "ai").strip()
    if origin not in {"human", "operator", "ai", "inbox", "external_thread"}:
        errors.append("science_contract origin must be human, operator, ai, inbox, or external_thread")
    closure_allowed = {"seed", "scoped_target", "partial_progress", "scoped_closed", "public_closed"}
    verification_allowed = {
        "unverified",
        "source_audited",
        "artifact_present",
        "reproducible",
        "independently_judged",
        "operator_approved",
    }
    outreach_allowed = {"not_drafted", "draftable", "draft_ready", "approved", "sent", "archived"}
    closure_status = str(contract.get("closure_status") or "seed").strip()
    verification_status = str(contract.get("verification_status") or "unverified").strip()
    outreach_status = str(contract.get("outreach_status") or "not_drafted").strip()
    if closure_status not in closure_allowed:
        errors.append("science_contract closure_status must be one of " + ", ".join(sorted(closure_allowed)))
    if verification_status not in verification_allowed:
        errors.append("science_contract verification_status must be one of " + ", ".join(sorted(verification_allowed)))
    if outreach_status not in outreach_allowed:
        errors.append("science_contract outreach_status must be one of " + ", ".join(sorted(outreach_allowed)))
    for key in ("evidence_required", "writeback_when", "close_when"):
        value = contract.get(key)
        if not isinstance(value, list) or not [x for x in value if str(x).strip()]:
            errors.append(f"science_contract {key} must be a non-empty list")
    errors.extend(_validate_taste_obligations(contract.get("taste_obligations"), origin=origin))
    try:
        patience = int(contract.get("no_progress_patience_turns") or 0)
    except (TypeError, ValueError):
        patience = 0
    if patience < 1 or patience > 5:
        errors.append("science_contract no_progress_patience_turns must be between 1 and 5")
    return errors


def _validate_taste_obligations(taste: object, *, origin: str) -> list[str]:
    errors: list[str] = []
    if origin in {"human", "operator"} and taste in (None, {}, ""):
        return errors
    if not isinstance(taste, dict):
        return ["science_contract taste_obligations must be an object for AI/inbox/external targets"]
    required = [
        "novelty_witness",
        "no_hidden_assumption_witness",
        "reproducibility_witness",
        "layer_separation_witness",
    ]
    weak_patterns = (
        r"\bplaceholder\b",
        r"\bto be filled\b",
        r"\btbd\b",
        r"\bn/a\b",
        r"\bnone\b",
        r"\bunknown\b",
    )
    for key in required:
        value = str(taste.get(key) or "").strip()
        if len(value) < 40:
            errors.append(f"science_contract taste_obligations.{key} is too short")
        if any(re.search(pattern, value, re.I) for pattern in weak_patterns):
            errors.append(f"science_contract taste_obligations.{key} is placeholder-like")
    return errors


def stub_from_todo(todo: TodoSpec) -> dict:
    slug = todo.slug()
    area = slug.split("_", 1)[0]
    return {
        "schema_version": SCHEMA_VERSION,
        "todo_id": todo.todo_id,
        "slug": slug,
        "title": todo.title,
        "source_url": todo.source,
        "profile_status": "draft",
        "final_display_form": getattr(todo, "final_display", "") or todo.submission_target()["type"],
        "success_gate": getattr(todo, "success_gate", "") or "operator-approved concrete artifact; no external send before approval",
        "no_external_send_without_operator_approval": True,
        "canonical_draft_paths": [
            f"tools/community-outreach/targets/{slug}/research.md",
            f"tools/community-outreach/targets/{slug}/submission_draft.md",
        ],
        "expected_artifacts": [
            f"tools/community-outreach/targets/{slug}/research.md",
            f"tools/community-outreach/targets/{slug}/results.json",
        ],
        "first_experiments": [
            {
                "label": "profile_judge_placeholder",
                "command": [],
                "expected_outputs": [
                    f"tools/community-outreach/targets/{slug}/research.md"
                ],
                "success_predicate": "LLM/profile judge must replace this placeholder with a concrete safe experiment or proof plan before RUN",
                "timeout_s": 1800,
            }
        ],
        "fallback_contribution": "To be filled by profile judge before RUN.",
        "science_contract": {
            "contribution_type": "research_note",
            "target_lane": "math_lane",
            "contract_quality_floor": 7,
            "terminal_artifact": f"tools/community-outreach/targets/{slug}/research.md",
            "verifier": "Replace this placeholder with an exact proof/check/certificate gate before RUN.",
            "progress_metric": "Replace this placeholder with a monotone measure of mathematical progress before RUN.",
            "origin": "ai",
            "closure_status": "seed",
            "verification_status": "unverified",
            "outreach_status": "not_drafted",
            "evidence_required": [
                "precise theorem/counterexample/certificate target",
                "dated freshness check",
                "operator-reviewable artifact on disk"
            ],
            "writeback_when": [
                "the terminal artifact satisfies the verifier and the claim is scoped"
            ],
            "close_when": [
                "freshness shows the target is closed",
                "two consecutive deep-reasoning turns add no new lemma, calculation, construction, or obstruction"
            ],
            "no_progress_patience_turns": 2
            ,
            "taste_obligations": {
                "novelty_witness": "Replace this placeholder with a concrete novelty witness before RUN.",
                "no_hidden_assumption_witness": "Replace this placeholder with the assumptions and sources allowed before RUN.",
                "reproducibility_witness": "Replace this placeholder with the exact artifact/check route before RUN.",
                "layer_separation_witness": "Replace this placeholder with the boundary between math evidence, draft text, and external send before RUN."
            }
        },
        "main_paper_bridge": {
            "required_before_run": False,
            "section_hint": "",
            "omega_modules": [],
            "backflow_surface": "to be determined after progress",
        },
        "oracle_judge_required": True,
        "freshness_required": True,
        "notes": f"Area hint: {area}. Generated stub; not RUN-ready until placeholder fields are replaced.",
    }


def write_stub(todo_id: str, *, force: bool = False) -> Path:
    todos = parse_board(BOARD_PATH)
    if todo_id not in todos:
        raise KeyError(f"{todo_id} not found")
    todo = todos[todo_id]
    path = profile_path_for_slug(todo.slug())
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and not force:
        return path
    path.write_text(json.dumps(stub_from_todo(todo), ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return path


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--todo-id", default="", help="T-NN to inspect/create profile for")
    p.add_argument("--write-stub", action="store_true")
    p.add_argument("--force", action="store_true")
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)
    if args.write_stub:
        if not args.todo_id:
            p.error("--write-stub requires --todo-id")
        path = write_stub(args.todo_id, force=args.force)
        print(str(path.relative_to(SCRIPT_DIR)))
        return 0
    if args.todo_id:
        todos = parse_board(BOARD_PATH)
        todo = todos.get(args.todo_id)
        if not todo:
            print(f"{args.todo_id} not found", file=sys.stderr)
            return 1
        profile, errors = load_profile(todo.slug())
        payload = {"todo_id": args.todo_id, "slug": todo.slug(), "valid": profile is not None, "errors": errors}
        if args.json:
            print(json.dumps(payload, ensure_ascii=False, indent=2))
        else:
            print(payload)
        return 0
    p.error("specify --todo-id")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
