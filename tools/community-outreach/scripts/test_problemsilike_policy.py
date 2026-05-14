#!/usr/bin/env python3
"""Regression tests for Problems I Like curated-source intake policy."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]


def _load(name: str, rel: str):
    path = SCRIPT_DIR / rel
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _candidate(source_url: str, *, status: str = "OPEN") -> dict:
    return {
        "title": "Problems I Like #3 demo",
        "source_url": source_url,
        "statement": "Determine whether every pair of smooth projective curves over an algebraic closure of a finite field has a common finite etale cover.",
        "rationale": f"Problems I Like curated source status {status}.",
        "final_display_form": "Internal math-lane research memo first; decide writeback after verified progress.",
        "success_gate": "No outreach unless a proof, counterexample, verified computation, or valuable obstruction memo is complete and locally checked.",
        "type": "EXISTENCE",
        "fit_score": 0,
        "topic_score": 0,
        "effort_estimate_days": 30,
        "status": status,
    }


def main() -> int:
    inbox = _load("outreach_candidate_inbox_under_test", "outreach_candidate_inbox.py")
    refill = _load("outreach_board_refill_under_test", "outreach_board_refill.py")
    parser = _load("outreach_board_parser_under_test", "outreach_board_parser.py")
    intake = _load("problemsilike_intake_under_test", "problemsilike_intake.py")

    gate = inbox.academic_impact_gate(_candidate("https://www.problemsilike.com/3"))
    if not gate.passed or gate.lane != "curated_math_source":
        raise AssertionError(f"Problems I Like OPEN low-score candidate should pass curated lane: {gate}")
    if any("topic_score" in m or "fit_score" in m for m in gate.missing):
        raise AssertionError(f"curated source leaked generic score requirements: {gate.missing}")

    generic = inbox.academic_impact_gate(_candidate("https://example.com/open-problem"))
    if generic.passed:
        raise AssertionError("non-Problems I Like low-score candidate unexpectedly passed generic gate")

    solved = inbox.academic_impact_gate(_candidate("https://www.problemsilike.com/6", status="SOLVED solved_external"))
    if solved.passed or solved.lane != "solved_external":
        raise AssertionError(f"Problems I Like solved_external original should not pass active lane: {solved}")

    existing = [("T-32", "Common finite etale cover obstruction", "https://www.problemsilike.com/3")]
    cand = refill.Candidate(
        title="Different title",
        source_url="https://www.problemsilike.com/3?utm=ignored",
        statement="Same canonical source id.",
    )
    keep, reason = refill._dedup_candidate(cand, existing)
    if keep or "canonical Problems I Like duplicate" not in reason:
        raise AssertionError(f"canonical Problems I Like dedup failed: keep={keep} reason={reason!r}")
    cand_13 = refill.Candidate(
        title="Exceptional groups as convolution monodromy",
        source_url="https://www.problemsilike.com/13",
        statement="Different canonical id.",
    )
    keep, reason = refill._dedup_candidate(cand_13, existing)
    if not keep:
        raise AssertionError(f"different Problems I Like id should not dedup by title/source: {reason}")

    todo = parser.TodoSpec(
        todo_id="T-99",
        title="Problems I Like #13 demo",
        status="Backlog",
        source="https://www.problemsilike.com/13",
        type_="open problem",
        untouched="",
        fit_score=0,
        topic_score=10,
        effort="",
        risk="",
        final_display="",
        success_gate="",
        statement="",
        prior="",
        omega_fit_detail="",
        attack_plan=[],
        worktree_inputs=[],
        deliverables=[],
        raw_block="",
    )
    if todo.slug() != "problemsilike_13":
        raise AssertionError(f"Problems I Like slug should be canonical id based: {todo.slug()}")

    snapshot = {
        "problems": [
            {
                "problem_id": 6,
                "canonical_url": "https://www.problemsilike.com/6",
                "title": "Solved original",
                "short_statement": "Solved statement.",
                "status": "SOLVED",
                "last_edited_date": "01 May 2026",
                "comments_count": 0,
                "comments_claim": "none",
                "reactions": {},
                "tags": [],
            },
            {
                "problem_id": 13,
                "canonical_url": "https://www.problemsilike.com/13",
                "title": "Exceptional groups",
                "short_statement": "Does there exist an abelian variety and subvariety with the requested exceptional group?",
                "status": "OPEN",
                "last_edited_date": "",
                "comments_count": 0,
                "comments_claim": "none",
                "reactions": {},
                "tags": [],
            },
        ]
    }
    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        tmp_path = Path(tmp)
        board = tmp_path / "RESEARCH_BOARD.md"
        board.write_text(
            """# Board

### T-01 · Existing #6

| field | value |
|---|---|
| Status | Backlog |
| Source | https://www.problemsilike.com/6 |
| Type | open problem |

**Statement.** x

### T-02 · Existing #13

| field | value |
|---|---|
| Status | Backlog |
| Source | https://www.problemsilike.com/13 |
| Type | open problem |

**Statement.** y
""",
            encoding="utf-8",
        )
        old_board = intake.BOARD_PATH
        old_targets = intake.TARGETS_DIR
        old_parser_board = parser.BOARD_PATH_DEFAULT
        intake.BOARD_PATH = board
        intake.TARGETS_DIR = tmp_path / "targets"
        parser.BOARD_PATH_DEFAULT = board
        try:
            result = intake.sync_board(snapshot, dry_run=False)
        finally:
            intake.BOARD_PATH = old_board
            intake.TARGETS_DIR = old_targets
            parser.BOARD_PATH_DEFAULT = old_parser_board
        text = board.read_text(encoding="utf-8")
        if "SOLVED_EXTERNAL" not in text:
            raise AssertionError("Problem #6 existing board entry was not marked solved_external")
        if any(a.get("action") == "append_open_problem" and a.get("problem_id") == 6 for a in result["actions"]):
            raise AssertionError("Problem #6 original was appended as an active OPEN target")
        if any(a.get("action") == "append_open_problem" and a.get("problem_id") == 13 for a in result["actions"]):
            raise AssertionError("Existing canonical #13 should not be appended again")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
