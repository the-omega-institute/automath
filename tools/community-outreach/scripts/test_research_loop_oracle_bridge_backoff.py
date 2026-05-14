#!/usr/bin/env python3
"""Regression test for global Oracle bridge backoff in research_loop."""

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
        loop.ORACLE_BRIDGE_STATE = state_dir / "oracle_bridge.json"
        log_path = state_dir / "oracle_deep.log"
        log_path.write_text(
            "[oracle-deep] bridge not ready for T-36: "
            "no compatible Outreach Oracle tab; required=outreach-1.24 seen=outreach-1.23 active=2\n",
            encoding="utf-8",
        )

        if not loop._path_contains_oracle_bridge_not_ready(str(log_path)):
            raise AssertionError("bridge-not-ready oracle log was not classified")

        loop._note_global_oracle_bridge_backoff(reason="test", log_path=str(log_path))
        if not loop._global_oracle_bridge_backoff_applies():
            raise AssertionError("global Oracle bridge backoff should apply immediately")

        state = json.loads(loop.ORACLE_BRIDGE_STATE.read_text(encoding="utf-8"))
        if state.get("bridge_backoff") is not True:
            raise AssertionError("bridge_backoff marker missing from Oracle bridge state")

        if loop.select_next_target(skip_slugs=set()) is not None:
            raise AssertionError("target selection should pause while Oracle bridge backoff is active")

        state["backoff_until_epoch"] = time.time() - 1
        loop.ORACLE_BRIDGE_STATE.write_text(json.dumps(state), encoding="utf-8")
        if loop._global_oracle_bridge_backoff_applies():
            raise AssertionError("expired global Oracle bridge backoff should not apply")

        server_down_log = state_dir / "server_down.log"
        server_down_log.write_text("[oracle-deep] server down at http://127.0.0.1:8766\n", encoding="utf-8")
        if not loop._log_contains_transport_skip(str(server_down_log)):
            raise AssertionError("server-down oracle log should still count as transport skip")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
