#!/usr/bin/env python3
"""Regression test for watchdog supervisor singleton-lock handling."""

from __future__ import annotations

import fcntl
import importlib.util
import os
import tempfile
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "outreach_watchdog.py"


def _load_watchdog():
    spec = importlib.util.spec_from_file_location("outreach_watchdog_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    watchdog = _load_watchdog()
    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        lock_path = Path(tmp) / "supervisor.lock"
        watchdog.SUPERVISOR_LOCK = lock_path

        if watchdog._supervisor_lock_held():
            raise AssertionError("new supervisor lock should not be reported as held")

        fd = os.open(str(lock_path), os.O_CREAT | os.O_RDWR, 0o644)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            if not watchdog._supervisor_lock_held():
                raise AssertionError("watchdog should see an externally held supervisor lock")
        finally:
            fcntl.flock(fd, fcntl.LOCK_UN)
            os.close(fd)

        if watchdog._supervisor_lock_held():
            raise AssertionError("released supervisor lock should not be reported as held")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
