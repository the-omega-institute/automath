#!/usr/bin/env python3
"""Regression test for watchdog-spawned supervisor defaults."""

from __future__ import annotations

import importlib.util
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "outreach_watchdog.py"


def _load_watchdog():
    spec = importlib.util.spec_from_file_location("outreach_watchdog_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    watchdog = _load_watchdog()
    args = list(watchdog.DEFAULT_SUPERVISOR_ARGS)
    try:
        parallel = int(args[args.index("--parallel") + 1])
    except (ValueError, IndexError) as exc:
        raise AssertionError(f"DEFAULT_SUPERVISOR_ARGS must include --parallel N: {args}") from exc

    # Three Outreach Oracle tabs should map to three research workers. Board
    # refill reserve is disabled separately, so the watchdog must not expand
    # the active math pool beyond the browser bridge capacity.
    if parallel != 3:
        raise AssertionError(
            "watchdog-spawned supervisor must run exactly three research workers "
            f"for three browser tabs (expected --parallel 3, got {parallel})"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
