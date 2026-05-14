#!/usr/bin/env python3
"""Regression tests for watchdog safe-restart gating."""

from __future__ import annotations

import importlib.util
import json
import tempfile
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "outreach_watchdog.py"


def _load_watchdog():
    spec = importlib.util.spec_from_file_location("outreach_watchdog_restart_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    watchdog = _load_watchdog()
    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        tmp_path = Path(tmp)
        runtime = tmp_path / "supervisor.runtime.json"
        stop_file = tmp_path / ".outreach_stop"
        drain_file = tmp_path / ".outreach_restart_drain"
        runtime.write_text(
            json.dumps({"status": "running", "pid": 12345, "git_head": "oldhead"}, indent=2) + "\n",
            encoding="utf-8",
        )
        watchdog.SUPERVISOR_RUNTIME = runtime
        watchdog.STOP_FILE = stop_file
        watchdog.RESTART_DRAIN_FILE = drain_file
        watchdog._git_head = lambda: "newhead"  # type: ignore[assignment]
        watchdog._observer_unreliable = lambda server: False  # type: ignore[assignment]

        server_local_only = {"agents_busy": 0, "queue_length": 0, "port": 8766}
        action = watchdog._request_safe_supervisor_restart_if_code_changed(server_local_only)
        if not action.startswith("restart_supervisor_code_changed:"):
            raise AssertionError(f"local-only work must not block restart: {action}")
        if not stop_file.exists():
            raise AssertionError("safe restart should write STOP_FILE")
        if not drain_file.exists():
            raise AssertionError("stale supervisor should receive a drain marker")

        stop_file.unlink()
        action = watchdog._request_safe_supervisor_restart_if_code_changed({"agents_busy": 1, "queue_length": 0, "port": 8766})
        if not action.startswith("restart_deferred_oracle_active:"):
            raise AssertionError(f"active Oracle work should defer restart: {action}")
        if stop_file.exists():
            raise AssertionError("Oracle-active restart deferral must not write STOP_FILE")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
