#!/usr/bin/env python3
"""Regression test for global Codex local-repair transport backoff."""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import time
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
    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        state_dir = Path(tmp)
        loop.STATE_DIR = state_dir
        loop.CODEX_TRANSPORT_STATE = state_dir / "codex_transport.json"
        log_path = state_dir / "codex.stderr.txt"
        log_path.write_text(
            "Error: failed to initialize in-process app-server client: Operation not permitted\n",
            encoding="utf-8",
        )

        if not loop._path_contains_codex_transport_failure(str(log_path)):
            raise AssertionError("Codex app-server permission error was not classified as transport failure")

        loop._note_global_codex_transport_backoff(reason="test", log_path=str(log_path))
        if not loop._global_codex_transport_backoff_applies():
            raise AssertionError("global Codex transport backoff should apply immediately after marker write")

        state = json.loads(loop.CODEX_TRANSPORT_STATE.read_text(encoding="utf-8"))
        if state.get("transport_backoff") is not True:
            raise AssertionError("transport_backoff marker missing from global Codex state")

        state["backoff_until_epoch"] = time.time() - 1
        loop.CODEX_TRANSPORT_STATE.write_text(json.dumps(state), encoding="utf-8")
        if loop._global_codex_transport_backoff_applies():
            raise AssertionError("expired global Codex transport backoff should not apply")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
