#!/usr/bin/env python3
"""Regression test: busy compatible Project tabs still make Oracle queue-ready."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[3]
MODULE_PATH = REPO / "tools/community-outreach/oracle_consultant.py"


def _load_oracle():
    spec = importlib.util.spec_from_file_location("oracle_consultant_readiness_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load oracle_consultant")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def main() -> int:
    oracle = _load_oracle()

    old_get = oracle.http_get
    old_curl = oracle._http_get_with_curl
    try:
        def fake_get(url: str, timeout: int = 5) -> dict:
            return {
                "queue_length": 0,
                "required_script_version": "outreach-1.24",
                "active_poll_agents": [],
                "compatible_active_poll_agents": [],
                "project_active_poll_agents": [],
                "recent_agents": {
                    "outreach_1_abc123": {
                        "event": "heartbeat",
                        "recent": True,
                        "metrics": {
                            "script_version": "outreach-1.24",
                            "page_url": (
                                "https://chatgpt.com/g/"
                                "g-p-69fdba181e648191a0eb330852658373-openproblem/"
                                "c/6a060548-18f4-83ec-b624-dd738f5013b9"
                            ),
                            "task_id": "deep_busy",
                            "generating": True,
                        },
                    }
                },
            }

        oracle.http_get = fake_get
        oracle._http_get_with_curl = fake_get
        ready, reason, status = oracle.oracle_bridge_readiness("http://127.0.0.1:8766")
    finally:
        oracle.http_get = old_get
        oracle._http_get_with_curl = old_curl

    if not ready:
        raise AssertionError(f"busy compatible Project tab should be queue-ready: {reason}; {status}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
