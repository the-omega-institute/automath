#!/usr/bin/env python3
"""Regression tests for supervisor runtime bookkeeping."""

from __future__ import annotations

import importlib.util
import json
import os
import tempfile
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
    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        state_dir = Path(tmp)
        runtime = state_dir / "supervisor.runtime.json"
        runtime.write_text(
            json.dumps(
                {
                    "status": "running",
                    "pid": os.getpid() + 100000,
                    "git_head": "abc123",
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
        supervisor.STATE_DIR = state_dir
        supervisor.SUPERVISOR_RUNTIME = runtime

        supervisor.mark_runtime_stopped()
        payload = json.loads(runtime.read_text(encoding="utf-8"))
        if payload.get("status") != "running":
            raise AssertionError(
                "mark_runtime_stopped should not overwrite a runtime record owned by another supervisor pid: "
                f"{payload}"
            )

        payload["pid"] = os.getpid()
        runtime.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        supervisor.mark_runtime_stopped()
        payload = json.loads(runtime.read_text(encoding="utf-8"))
        if payload.get("status") != "stopped" or not payload.get("finished_at"):
            raise AssertionError(f"own runtime record should be marked stopped: {payload}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
