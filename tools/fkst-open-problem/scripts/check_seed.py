#!/usr/bin/env python3
"""Static checks for the FKST open-problem pilot skeleton."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def require(path: str, needle: str) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    if needle not in text:
        raise SystemExit(f"{path}: missing {needle!r}")


def main() -> None:
    require("README.md", "Agent consensus alone is never an accepted mathematical fact.")
    require("pilot.md", "Start with T-43")
    require("packages/omega-open-problem/core.lua", "T-43")
    require("packages/omega-open-problem/departments/proposal_intake/main.lua", "consensus.proposal")
    require("packages/omega-open-problem/raisers/seed.lua", "Source-replay A5 same-W")


if __name__ == "__main__":
    main()
