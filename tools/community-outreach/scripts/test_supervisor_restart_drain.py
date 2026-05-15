#!/usr/bin/env python3
"""Regression test for supervisor code-change drain detection."""

from __future__ import annotations

import importlib.util
import tempfile
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "outreach_supervisor.py"


def _load_supervisor():
    spec = importlib.util.spec_from_file_location("outreach_supervisor_drain_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    supervisor = _load_supervisor()
    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        drain = Path(tmp) / ".outreach_restart_drain"
        supervisor.RESTART_DRAIN_FILE = drain
        supervisor._git_head = lambda: "newhead"  # type: ignore[assignment]

        if supervisor._restart_drain_requested("oldhead"):
            raise AssertionError("missing drain marker should not request restart")

        drain.write_text("oldhead -> newhead\n", encoding="utf-8")
        if not supervisor._restart_drain_requested("oldhead"):
            raise AssertionError("head change plus drain marker should request restart")
        if supervisor._restart_drain_requested("newhead"):
            raise AssertionError("fresh supervisor at current head should not drain")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
