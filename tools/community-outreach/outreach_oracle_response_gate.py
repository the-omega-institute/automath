#!/usr/bin/env python3
"""Shared Outreach Oracle response classifiers.

The browser bridge can fail in several non-mathematical ways: explicit
transport errors, empty/tiny extraction stubs, or prompt echo where the saved
"response" is just the prompt we sent to ChatGPT.  All harness layers must
classify those consistently so they do not become Oracle claim packets or
science-gate evidence.
"""

from __future__ import annotations

import re


TRANSPORT_MARKERS = (
    "error: task cancelled by server",
    "error (re-extract):",
    "error: empty response",
    "error: no assistant output after",
    "empty response (timeout or extraction failure)",
    "no assistant output after",
    "re-extract: nothing meaningful",
    "re-extract: empty response",
    "server unreachable",
)

PROMPT_ECHO_MARKERS = (
    "you are the primary mathematical worker on this omega project outreach target.",
    "you are the oracle math worker for this omega project open-problem target.",
    "## current codex-selected task",
    "## selected task",
    "## codex local workup",
    "## local facts",
    "## compact science contract",
    "## deterministic gate blockers",
    "## target",
    "## math problem statement",
    "## problem statement",
    "## current deterministic science-gate blockers",
    "## your first turn",
    "## output",
    "do not summarize the problem back to me. start doing the mathematics.",
    "do not summarize or restart. start with the next mathematical move.",
)


def claim_packet_oracle_response(text: str) -> str:
    marker = "## Oracle Response"
    idx = (text or "").find(marker)
    if idx < 0:
        return text or ""
    return (text or "")[idx + len(marker) :].strip()


def is_transport_stub_response(text: str) -> bool:
    stripped = (text or "").strip()
    if not stripped:
        return True
    lowered = stripped.lower()
    if any(lowered.startswith(marker) for marker in TRANSPORT_MARKERS):
        return True
    return len(stripped) < 80 and "cancelled" in lowered and "server" in lowered


def is_prompt_echo_response(text: str) -> bool:
    """Return true when extraction captured our prompt instead of an answer.

    A valid Oracle answer may follow the requested "CONTRACT TARGET" format,
    but it should not begin by replaying the full worker prompt.  If the saved
    text starts with the worker-role sentence and contains several prompt
    section headings near the front, treat it as extraction failure.
    """
    stripped = (text or "").strip()
    if not stripped:
        return False
    lowered = stripped.lower()
    head = lowered[:12000]
    role_markers = (
        "you are the primary mathematical worker on this omega project outreach target.",
        "you are the oracle math worker for this omega project open-problem target.",
    )
    if not any(marker in head[:1000] for marker in role_markers):
        return False
    marker_count = sum(1 for marker in PROMPT_ECHO_MARKERS if marker in head)
    if marker_count >= 4:
        return True
    if (
        "## current codex-selected task" in head
        and "## your first turn" in head
        and re.search(r"\b1\.\s+contract target\b", head)
    ):
        return True
    return False


def is_non_substantive_oracle_response(text: str) -> bool:
    return is_transport_stub_response(text) or is_prompt_echo_response(text)


def has_deep_answer_anchor(text: str) -> bool:
    """Lightweight positive signal for a real deep-research answer."""
    lowered = (text or "").lower()
    anchors = (
        "contract target",
        "current score",
        "move:",
        "evidence:",
        "next stop test",
        "theorem",
        "proof",
        "lemma",
        "counterexample",
        "obstruction",
        "certificate",
    )
    return any(anchor in lowered for anchor in anchors)
