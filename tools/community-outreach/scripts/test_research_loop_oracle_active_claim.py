#!/usr/bin/env python3
"""Regression test for not reclaiming targets active in Oracle."""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace

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
        return f"problemsilike_{int(self.source.rsplit('/', 1)[-1]):02d}"


def _patch_actionable_gates(loop, todos: dict[str, Todo]):
    loop._parse_board_safe = lambda: todos
    loop.judge = lambda todo: SimpleNamespace(
        verdict=next(iter(loop.ACTIONABLE_VERDICTS)),
        missing=[],
        reasons=[],
    )
    loop.science_gate_evaluate = lambda todo: SimpleNamespace(
        status="NEEDS_EVIDENCE",
        next_action="deep_reason",
    )
    loop._global_oracle_bridge_backoff_applies = lambda: False
    loop._cooldown_applies = lambda todo_id, slug, cooldown_hours: False
    loop._transport_backoff_applies = lambda slug: False
    loop._local_repair_backoff_applies = lambda slug: False


def main() -> int:
    loop = _load_research_loop()
    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        state_dir = Path(tmp)
        loop.STATE_DIR = state_dir
        loop.RESEARCH_CLAIMS_DIR = state_dir / "research_claims"
        loop.RESEARCH_CLAIMS_DIR.mkdir(parents=True)

        slug = "problemsilike_04"
        claim_dir = loop.RESEARCH_CLAIMS_DIR / slug
        claim_dir.mkdir()
        (claim_dir / ".in_progress").write_text("claimed_at=test\npid=1\n", encoding="utf-8")
        (claim_dir / ".pid").write_text("1", encoding="utf-8")

        status_path = state_dir / "oracle_status.json"
        status_path.write_text(json.dumps({
            "agents": {
                "tab": {
                    "task_id": "deep_problemsilike_04_t1778777969516",
                    "conversation_id": "conv_demo",
                }
            }
        }), encoding="utf-8")
        loop.ORACLE_SERVER_URL = status_path.as_uri()
        if not loop._oracle_task_active_for_target("T-44", slug):
            raise AssertionError("active Oracle task was not detected for target slug")
        if not loop._live_worker_for_target("T-44", slug):
            raise AssertionError("Oracle-active target should count as a live worker")
        released = loop.cleanup_stale_claims(stale_hours=0)
        if released:
            raise AssertionError(f"Oracle-active claim should not be released, got {released}")
        if not (claim_dir / ".in_progress").exists():
            raise AssertionError("Oracle-active claim marker was removed")

        target_root = state_dir / "targets"
        target_root.mkdir()
        loop.TARGETS_DIR = target_root
        todos = {
            "T-44": Todo(
                todo_id="T-44",
                title="Problems I Like #4 active in Oracle",
                source="https://www.problemsilike.com/4",
            ),
            "T-45": Todo(
                todo_id="T-45",
                title="Problems I Like #5 next open target",
                source="https://www.problemsilike.com/5",
            ),
        }
        _patch_actionable_gates(loop, todos)
        picked = loop.select_next_target()
        if picked != ("T-45", "problemsilike_05"):
            raise AssertionError(f"selector should skip Oracle-active #4 and pick #5, got {picked}")

        _patch_actionable_gates(loop, {"T-44": todos["T-44"]})
        picked = loop.select_next_target()
        if picked is not None:
            raise AssertionError(f"selector should not busy-loop on only Oracle-active target, got {picked}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
