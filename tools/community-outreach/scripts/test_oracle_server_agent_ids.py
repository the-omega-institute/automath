#!/usr/bin/env python3
"""Regression test for Outreach Oracle browser agent id compatibility."""

from __future__ import annotations

import importlib.util
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "outreach_oracle_server.py"


def _load_server():
    spec = importlib.util.spec_from_file_location("outreach_oracle_server_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    server = _load_server()
    accepted = [
        "outreach_6187_euxi",
        "outreach_7409_rqxq",
        "outreach_1043_s7wu",
        "outreach_1_m3s9kabcd",
    ]
    rejected = [
        "",
        "default",
        "outreach",
        "outreach_2",
        "outreach_1",
        "outreach_agent_1",
        "outreach_abc",
        "other_6187_euxi",
    ]
    for agent_id in accepted:
        if not server._agent_id_ok(agent_id):
            raise AssertionError(f"valid Outreach Oracle agent id rejected: {agent_id}")
    for agent_id in rejected:
        if server._agent_id_ok(agent_id):
            raise AssertionError(f"invalid Outreach Oracle agent id accepted: {agent_id}")

    if not server._page_in_openproblem_project(server.OPENPROBLEM_PROJECT_URL):
        raise AssertionError("canonical OpenProblem project URL should be accepted")
    conversation_url = server.OPENPROBLEM_PROJECT_URL.replace("/project", "/c/6a04c06a-abd4-83ec-bbce-654c23b3d1e2")
    if not server._page_in_openproblem_project(conversation_url):
        raise AssertionError("OpenProblem conversation URL should be accepted")
    if server._page_in_openproblem_project("https://chatgpt.com/g/another-project/project"):
        raise AssertionError("other ChatGPT project URLs should not be accepted")

    agent_id = "outreach_1_m3s9kabcd"
    old_poll = {
        "script_version": "outreach-1.24",
        "page_url": server.OPENPROBLEM_PROJECT_URL,
        "chatgpt_url": "",
    }
    stale_poll = {
        "script_version": "outreach-1.22",
        "page_url": conversation_url,
        "chatgpt_url": conversation_url,
    }
    server.recent_agents.clear()
    server._record_agent_seen(agent_id, event="poll", metrics=old_poll)
    server._record_agent_seen(agent_id, event="poll", metrics=stale_poll)
    metrics = server.recent_agents[agent_id]["metrics"]
    if metrics["script_version"] != "outreach-1.24":
        raise AssertionError("stale/incompatible poll overwrote compatible active agent")

    # The compatibility predicate itself is the first line of defense used
    # before returning pending tasks or cancelling same-id pending tasks.
    if server._script_version_ok("outreach-1.23"):
        raise AssertionError("outreach-1.23 should not satisfy the 1.24 guard")
    if not server._script_version_ok("outreach-1.24"):
        raise AssertionError("outreach-1.24 should satisfy the 1.24 guard")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
