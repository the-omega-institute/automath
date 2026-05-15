#!/usr/bin/env python3
"""Regression test that oracle-deep dispatch skips arXiv Stage 0 noise."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
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


def main() -> int:
    loop = _load_research_loop()
    captured: dict[str, list[str]] = {}

    class FakeProc:
        pid = 12345

        def wait(self, timeout=None):  # noqa: ANN001
            return 0

    def fake_popen(cmd, **kwargs):  # noqa: ANN001
        captured["cmd"] = list(cmd)
        return FakeProc()

    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        state = Path(tmp)
        old_log_dir = loop.RESEARCH_LOOP_LOG_DIR
        old_dispatch = loop.DISPATCH_WORKTREE
        old_popen = loop.subprocess.Popen
        old_turns = loop._oracle_batch_turns
        old_timeout = loop.DEFAULT_ORACLE_TURN_TIMEOUT_S
        try:
            loop.RESEARCH_LOOP_LOG_DIR = state / "logs"
            loop.DISPATCH_WORKTREE = MODULE_PATH
            loop.subprocess.Popen = fake_popen
            loop._oracle_batch_turns = lambda _todo_id: 1
            loop.DEFAULT_ORACLE_TURN_TIMEOUT_S = 600
            rc, log_path = loop._spawn_oracle_deep("T-44", 600)
            if rc != 0:
                raise AssertionError(f"fake oracle-deep dispatch returned rc={rc}")
            if not log_path:
                raise AssertionError("oracle-deep dispatch did not return a log path")
            cmd = captured.get("cmd") or []
            if "--oracle-deep" not in cmd:
                raise AssertionError(f"missing --oracle-deep in command: {cmd}")
            if "--no-arxiv-stage0" not in cmd:
                raise AssertionError(f"oracle-deep must skip arXiv Stage 0 noise: {cmd}")
        finally:
            loop.RESEARCH_LOOP_LOG_DIR = old_log_dir
            loop.DISPATCH_WORKTREE = old_dispatch
            loop.subprocess.Popen = old_popen
            loop._oracle_batch_turns = old_turns
            loop.DEFAULT_ORACLE_TURN_TIMEOUT_S = old_timeout
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
