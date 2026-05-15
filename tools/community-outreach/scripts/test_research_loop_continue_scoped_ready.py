#!/usr/bin/env python3
"""Regression: low-impact scoped ready packets must not stop research."""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import dataclass
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "outreach_research_loop.py"


def _load_loop():
    spec = importlib.util.spec_from_file_location("outreach_research_loop_under_test", MODULE_PATH)
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
class Preflight:
    verdict: str = "RUN"
    missing: list[str] | None = None


@dataclass
class Science:
    status: str = "WRITEBACK_READY"
    next_action: str = "operator_review"


@dataclass
class Impact:
    status: str = "NEEDS_PUBLICATION_VALUE"
    next_action: str = "continue_deep_reason"
    primary_channel: str = "none"
    channels: list[str] | None = None


def main() -> int:
    loop = _load_loop()
    todo = Todo()
    loop.ACTIONABLE_VERDICTS = {"RUN"}
    loop._parse_board_safe = lambda: {todo.todo_id: todo}
    loop.judge = lambda _todo: Preflight()
    loop.science_gate_evaluate = lambda _todo: Science()
    loop.impact_gate_evaluate = lambda _todo: Impact()
    loop.write_impact_ledger = lambda _impact: None
    loop._claim_marker = lambda _slug: Path("/definitely/missing/claim")
    loop._live_worker_for_target = lambda _tid, _slug: False
    loop._cooldown_applies = lambda _tid, _slug, _hours: False
    loop._transport_backoff_applies = lambda _slug: False
    loop._local_repair_backoff_applies = lambda _slug: False
    loop._global_oracle_bridge_backoff_applies = lambda: False
    picked = loop.select_next_target()
    if picked != (todo.todo_id, todo.slug()):
        raise AssertionError(f"expected scoped ready target to continue, got {picked}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
