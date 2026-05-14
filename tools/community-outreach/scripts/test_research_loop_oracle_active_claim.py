#!/usr/bin/env python3
"""Regression test for not reclaiming targets active in Oracle."""

from __future__ import annotations

import importlib.util
import json
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
