#!/usr/bin/env python3
"""Static regression checks for Outreach Oracle fresh-chat navigation guards."""

from __future__ import annotations

from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "outreach_oracle_macos.user.js"


def _require(text: str, needle: str) -> None:
    if needle not in text:
        raise AssertionError(f"missing userscript guard: {needle}")


def main() -> int:
    text = SCRIPT.read_text(encoding="utf-8")
    _require(text, "function isOnConversationPage()")
    _require(text, "if (isOnConversationPage()) return false;")
    _require(text, "if (!isOnConversationPage() && isOnNewChatPage()) return true;")
    _require(text, "const needNavToFresh = !targetUrl && !isOnNewChatPage();")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
