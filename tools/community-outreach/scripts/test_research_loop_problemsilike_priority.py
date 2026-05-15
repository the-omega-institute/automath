#!/usr/bin/env python3
"""Regression test for Problems I Like research-loop priority."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "outreach_research_loop.py"


def _load_research_loop():
    spec = importlib.util.spec_from_file_location("outreach_research_loop_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


@dataclass
class Todo:
    todo_id: str
    title: str
    source: str
    status: str = "Backlog"
    fit_score: int = 10
    topic_score: int = 10

    def slug(self) -> str:
        if "problemsilike.com/" in self.source:
            return f"problemsilike_{int(self.source.rsplit('/', 1)[-1]):02d}"
        return "ordinary_frontier"


def _write_initial_cycle(target_root: Path, slug: str) -> None:
    target = target_root / slug
    target.mkdir(parents=True)
    for name in ("research.md", "results.json", "next_oracle_question.md", "local_repair_last.json"):
        (target / name).write_text("cycle artifact\n", encoding="utf-8")
    (target / "oracle_claim_packet_demo.md").write_text("oracle response\n", encoding="utf-8")


def main() -> int:
    loop = _load_research_loop()
    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        target_root = Path(tmp) / "targets"
        target_root.mkdir()
        old_targets = loop.TARGETS_DIR
        loop.TARGETS_DIR = target_root
        try:
            high_score_frontier = Todo(
                todo_id="T-90",
                title="High score frontier",
                source="https://example.com/frontier",
                fit_score=10,
                topic_score=10,
            )
            done_pil = Todo(
                todo_id="T-31",
                title="Problems I Like #7 done",
                source="https://www.problemsilike.com/7",
                fit_score=0,
                topic_score=10,
            )
            fresh_pil = Todo(
                todo_id="T-43",
                title="Problems I Like #2 fresh",
                source="https://www.problemsilike.com/2",
                fit_score=0,
                topic_score=10,
            )
            solved_pil = Todo(
                todo_id="T-51",
                title="Problems I Like #6 solved external",
                source="https://www.problemsilike.com/6",
                status="SOLVED_EXTERNAL",
                fit_score=0,
                topic_score=10,
            )
            _write_initial_cycle(target_root, done_pil.slug())

            ranked = sorted(
                [
                    ("T-90", high_score_frontier),
                    ("T-31", done_pil),
                    ("T-43", fresh_pil),
                ],
                key=loop._selection_priority,
            )
            if [tid for tid, _ in ranked] != ["T-43", "T-31", "T-90"]:
                raise AssertionError(f"Problems I Like priority order regressed: {ranked}")

            solved_ranked = sorted(
                [("T-90", high_score_frontier), ("T-51", solved_pil)],
                key=loop._selection_priority,
            )
            if solved_ranked[0][0] != "T-90":
                raise AssertionError("solved_external Problems I Like target was prioritized as active")

            loop.TARGETS_DIR = target_root
            profile_dir = target_root / fresh_pil.slug()
            profile_dir.mkdir(parents=True, exist_ok=True)
            (profile_dir / "profile.json").write_text(
                """{
  "schema_version": "outreach-target-profile-v1",
  "todo_id": "T-43",
  "slug": "problemsilike_02",
  "title": "Problems I Like #2",
  "source_url": "https://www.problemsilike.com/2",
  "profile_status": "ready",
  "final_display_form": "math result only",
  "success_gate": "proof or counterexample",
  "no_external_send_without_operator_approval": true,
  "canonical_draft_paths": ["tools/community-outreach/targets/problemsilike_02/research.md"],
  "expected_artifacts": ["tools/community-outreach/targets/problemsilike_02/research.md"],
  "first_experiments": [{"label": "x", "command": [], "expected_outputs": [], "success_predicate": "x"}],
  "fallback_contribution": "valuable obstruction only",
  "science_contract": {
    "contribution_type": "research_note",
    "target_lane": "math_lane",
    "terminal_artifact": "tools/community-outreach/targets/problemsilike_02/research.md",
    "verifier": "local check",
    "progress_metric": "proof gap count",
    "evidence_required": ["evidence"],
    "writeback_when": ["proof"],
    "close_when": ["already solved"],
    "no_progress_patience_turns": 2
  }
}
""",
                encoding="utf-8",
            )
            if loop._no_progress_patience(fresh_pil.slug()) < 20:
                raise AssertionError("Problems I Like targets must get at least 20 no-progress turns")
        finally:
            loop.TARGETS_DIR = old_targets
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
