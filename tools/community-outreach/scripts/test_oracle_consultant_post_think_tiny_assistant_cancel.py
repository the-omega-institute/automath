#!/usr/bin/env python3
"""Regression test for post-think tiny-assistant extraction mismatch cancel."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[3]
MODULE_PATH = REPO / "tools/community-outreach/oracle_consultant.py"


def _load_oracle():
    spec = importlib.util.spec_from_file_location("oracle_consultant_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load oracle_consultant")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def main() -> int:
    oracle = _load_oracle()

    task_id = "deep_demo_tiny_assistant"
    calls: list[tuple[str, dict | None]] = []

    def fake_get(url: str, timeout: int = 10) -> dict:
        calls.append(("GET", {"url": url, "timeout": timeout}))
        if url.endswith(f"/result/{task_id}"):
            return {"status": "pending"}
        if url.endswith("/status"):
            return {
                "queue_length": 0,
                "recent_agents": {
                    "outreach_tab_1": {
                        "metrics": {
                            "task_id": task_id,
                            "elapsed_seconds": 1200,
                            "extracted_chars": 146,
                            "generating": False,
                            "generation": {"post_think": True},
                            "assistant": {
                                "assistant_only_chars": 0,
                                "last_assistant_clean_chars": 1,
                            },
                        }
                    }
                },
            }
        raise AssertionError(f"unexpected GET {url}")

    def fake_post(url: str, payload: dict, timeout: int = 10) -> dict:
        calls.append(("POST", {"url": url, "payload": payload, "timeout": timeout}))
        if url.endswith("/cancel") and payload.get("task_id") == task_id:
            return {"status": "cancelled", "tasks": [task_id]}
        raise AssertionError(f"unexpected POST {url} {payload}")

    old_get = oracle.http_get
    old_post = oracle.http_post
    old_threshold = oracle.POST_THINK_TINY_ASSISTANT_CANCEL_S
    try:
        oracle.http_get = fake_get
        oracle.http_post = fake_post
        oracle.POST_THINK_TINY_ASSISTANT_CANCEL_S = 900
        response = oracle.oracle_poll(task_id, timeout=1, poll_interval=0, progress=False)
    finally:
        oracle.http_get = old_get
        oracle.http_post = old_post
        oracle.POST_THINK_TINY_ASSISTANT_CANCEL_S = old_threshold

    if response != "":
        raise AssertionError(f"expected empty response after cancellation, got {response!r}")
    if not any(kind == "POST" and row["url"].endswith("/cancel") for kind, row in calls):
        raise AssertionError("oracle_poll did not cancel the tiny-assistant post-think task")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
