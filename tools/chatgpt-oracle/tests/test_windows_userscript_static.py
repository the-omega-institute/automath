"""Static checks for the Windows ChatGPT Oracle userscript.

These tests do not execute browser automation. They protect the visible
operator affordances that keep the five-tab Oracle pool observable.
"""

from __future__ import annotations

import re
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "chatgpt_oracle_windows.user.js"


def _source() -> str:
    return SCRIPT.read_text(encoding="utf-8")


def test_windows_userscript_version_literals_match() -> None:
    source = _source()
    metadata = re.search(r"// @version\s+([0-9.]+)", source)
    runtime = re.search(r'const SCRIPT_VERSION = "([0-9.]+)"', source)

    assert metadata is not None
    assert runtime is not None
    assert metadata.group(1) == runtime.group(1)


def test_windows_userscript_exposes_five_oracle_tab_labels() -> None:
    source = _source()

    for idx in range(1, 6):
        assert f"id=\"oracle-label-{idx}\"" in source
        assert f"title=\"Open Tab #{idx}\"" in source

    assert 'for (const tag of ["1", "2", "3", "4", "5"])' in source


def test_windows_userscript_panel_exposes_poll_state() -> None:
    source = _source()

    assert "last_poll_at" in source
    assert "last_poll_status" in source
    assert "function recordPollStatus(status)" in source
    assert "poll: ${lastPollStatus}" in source
