#!/usr/bin/env python3
"""Regression test for impact gate real-output standards."""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "outreach_impact_gate.py"


def _load_impact_gate():
    spec = importlib.util.spec_from_file_location("outreach_impact_gate_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


@dataclass
class Todo:
    todo_id: str = "T-44"
    title: str = "Problems I Like #4"
    source: str = "https://www.problemsilike.com/4"
    status: str = "Backlog"
    topic_score: int = 10
    fit_score: int = 5

    def slug(self) -> str:
        return "problemsilike_04"


@dataclass
class Science:
    status: str = "WRITEBACK_READY"
    next_action: str = "operator_review"
    contribution_type: str = "research_note"
    target_lane: str = "math_lane"


def _write_science_ledger(root: Path, slug: str) -> None:
    target = root / slug
    target.mkdir(parents=True, exist_ok=True)
    (target / "science_gate.json").write_text(
        json.dumps(
            {
                "status": "WRITEBACK_READY",
                "contribution_type": "research_note",
                "target_lane": "math_lane",
            }
        )
        + "\n",
        encoding="utf-8",
    )


def main() -> int:
    gate = _load_impact_gate()
    todo = Todo()
    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        old_targets = gate.TARGETS_DIR
        gate.TARGETS_DIR = Path(tmp) / "targets"
        target = gate.TARGETS_DIR / todo.slug()
        target.mkdir(parents=True)
        _write_science_ledger(gate.TARGETS_DIR, todo.slug())
        try:
            gate.science_gate_evaluate = lambda _todo: Science()

            (target / "research.md").write_text(
                """# Research

This is a failure analysis and obstruction from a toy check. It cannot be used
to prove the original problem. No theorem is claimed. This is not publication
grade.
""",
                encoding="utf-8",
            )
            verdict = gate.evaluate(todo)
            if verdict.status != gate.NEEDS_PUBLICATION_VALUE:
                raise AssertionError(
                    "ordinary Problems I Like failure analysis must not be surfaced "
                    f"as publishable: {verdict.status}"
                )

            (target / "research.md").write_text(
                """# Research

Theorem. This gives a complete obstruction and route-killing obstruction: it
rules out the standard route for the stated Problems I Like target and changes
the attack surface.

Proof complete. The obstruction is reproducible from the included verifier.
""",
                encoding="utf-8",
            )
            verdict = gate.evaluate(todo)
            if verdict.status != gate.IMPACT_PLAN_READY:
                raise AssertionError(
                    "complete publishable obstruction on a curated target should be reviewable: "
                    f"{verdict.status}"
                )
            required = "\n".join(verdict.required_before_send).lower()
            for phrase in (
                "ai assistance",
                "independently verify all mathematical claims",
                "public forum comments must be short",
            ):
                if phrase not in required:
                    raise AssertionError(f"Problems I Like public-comment policy missing {phrase!r}: {required}")
        finally:
            gate.TARGETS_DIR = old_targets
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
