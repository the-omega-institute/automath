#!/usr/bin/env python3
"""Regression test for research-loop science+impact readiness gating."""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import dataclass
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


@dataclass
class Impact:
    status: str


def main() -> int:
    loop = _load_research_loop()

    if not loop._impact_allows_operator_review(Impact("IMPACT_PLAN_READY")):
        raise AssertionError("IMPACT_PLAN_READY should allow operator review")
    if not loop._impact_allows_operator_review(Impact("CLOSE_OR_ARCHIVE")):
        raise AssertionError("CLOSE_OR_ARCHIVE should allow operator archive review")
    for status in ("NEEDS_PUBLICATION_VALUE", "NEEDS_RESEARCH", "BOARD_SKIPPED", ""):
        if loop._impact_allows_operator_review(Impact(status)):
            raise AssertionError(f"{status!r} should not allow operator review")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
