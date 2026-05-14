#!/usr/bin/env python3
"""Regression test for Oracle lane reservation in the supervisor.

Generic board refill is useful when the research pool is thin.  It is harmful
when enough RUN targets already exist, because it consumes the same ChatGPT
browser capacity needed for deep target turns.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "outreach_supervisor.py"


def _load_supervisor():
    spec = importlib.util.spec_from_file_location("outreach_supervisor_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    supervisor = _load_supervisor()

    if supervisor._generic_board_refill_allowed(2, 2):
        raise AssertionError("board refill should be blocked when RUN pool meets low-water")
    if supervisor._generic_board_refill_allowed(12, 2):
        raise AssertionError("board refill should be blocked when RUN pool is well above low-water")
    if not supervisor._generic_board_refill_allowed(1, 2):
        raise AssertionError("board refill should be allowed below low-water")
    if not supervisor._generic_board_refill_allowed(0, 2):
        raise AssertionError("board refill should be allowed for an empty RUN pool")
    if supervisor._generic_board_refill_allowed(0, 0):
        raise AssertionError("low-water=0 means generic refill is operator/manual only")

    rows = [
        {"verdict": "RUN"},
        {"verdict": "RUN"},
        {"verdict": "NEEDS_PROFILE"},
        {"verdict": "DROP"},
    ]
    if supervisor._run_target_count(rows) != 2:
        raise AssertionError("RUN target counter ignored or over-counted board rows")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
