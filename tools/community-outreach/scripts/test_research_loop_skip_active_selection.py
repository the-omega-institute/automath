#!/usr/bin/env python3
"""Regression test for skipping active targets during selection."""

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
    topic_score: int = 10
    fit_score: int = 10

    def slug(self) -> str:
        return f"problemsilike_{int(self.source.rsplit('/', 1)[-1]):02d}"


@dataclass
class Preflight:
    verdict: str = "RUN"
    missing: list[str] | None = None
    reasons: list[str] | None = None


@dataclass
class Gate:
    status: str = "NEEDS_EVIDENCE"
    next_action: str = "deep_reason"


def main() -> int:
    loop = _load_research_loop()
    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        state = Path(tmp)
        old_claims = loop.RESEARCH_CLAIMS_DIR
        loop.RESEARCH_CLAIMS_DIR = state / "claims"
        loop.RESEARCH_CLAIMS_DIR.mkdir(parents=True)
        old_parse = loop._parse_board_safe
        old_judge = loop.judge
        old_gate = loop.science_gate_evaluate
        old_live = loop._live_worker_for_target
        old_transport_backoff = loop._transport_backoff_applies
        old_local_backoff = loop._local_repair_backoff_applies
        old_cooldown = loop._cooldown_applies
        old_global_oracle_backoff = loop._global_oracle_bridge_backoff_applies
        try:
            active = Todo("T-44", "Problems I Like #4", "https://www.problemsilike.com/4")
            next_target = Todo("T-45", "Problems I Like #5", "https://www.problemsilike.com/5")
            loop._parse_board_safe = lambda: {"T-44": active, "T-45": next_target}
            loop.judge = lambda _todo: Preflight(missing=[], reasons=[])
            loop.science_gate_evaluate = lambda _todo: Gate()
            loop._live_worker_for_target = lambda tid, slug: slug == "problemsilike_04"
            loop._transport_backoff_applies = lambda _slug: False
            loop._local_repair_backoff_applies = lambda _slug: False
            loop._cooldown_applies = lambda _tid, _slug, _hours: False
            loop._global_oracle_bridge_backoff_applies = lambda: False

            picked = loop.select_next_target()
            if picked != ("T-45", "problemsilike_05"):
                raise AssertionError(f"selection should skip active target and choose T-45, got {picked}")
        finally:
            loop.RESEARCH_CLAIMS_DIR = old_claims
            loop._parse_board_safe = old_parse
            loop.judge = old_judge
            loop.science_gate_evaluate = old_gate
            loop._live_worker_for_target = old_live
            loop._transport_backoff_applies = old_transport_backoff
            loop._local_repair_backoff_applies = old_local_backoff
            loop._cooldown_applies = old_cooldown
            loop._global_oracle_bridge_backoff_applies = old_global_oracle_backoff
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
