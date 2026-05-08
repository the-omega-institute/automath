#!/usr/bin/env python3
"""Outreach board refill — STUB awaiting ChatGPT Project URL configuration.

Once the operator has built the `Omega Outreach` ChatGPT Project (with
attached: theory/.../main.pdf + lean4/README.md + papers/publication/PROGRAM_BOARD.md),
this script will:

  1. Build a refill prompt: "look at the attached Project files + the
     arxiv_watch / lit_staleness output deltas since last refill; propose
     5-10 NEW outreach targets — do not look at RESEARCH_BOARD.md, dedup
     happens downstream."
  2. Submit the prompt as a fresh task via outreach_oracle_server (port 8766);
     the userscript routes it to the configured ChatGPT Project tab.
  3. Poll for the JSON response.
  4. Run claude judge / dedup against current RESEARCH_BOARD.md entries.
  5. Atomically append the survivors to RESEARCH_BOARD.md as new T-NN
     Backlog entries.

Until the Project URL is wired into the userscript, this script is a no-op
that logs a notice and exits 0. The supervisor calls it on cooldown; that
empty call is harmless.

Configuration knobs to be added once ready:
  - REFILL_PROJECT_URL : str (the full chatgpt.com /g/g-p-...../project URL)
  - REFILL_PROMPT_PATH : Path (prompts/outreach_board_refill.txt — to be written)
  - REFILL_TIMEOUT_S   : int (poll budget, default 1800)
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
STATE_DIR = SCRIPT_DIR / "outreach_state"
STATUS_PATH = STATE_DIR / "board_refill.status.json"

# Operator fills this in once the Project is built.
REFILL_PROJECT_URL = ""
REFILL_PROMPT_PATH = SCRIPT_DIR / "prompts" / "outreach_board_refill.txt"


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _write_status(payload: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    try:
        STATUS_PATH.write_text(
            json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8"
        )
    except OSError:
        pass


def _stub_no_op(reason: str) -> int:
    payload = {
        "ran_at": _now_iso(),
        "verdict": "noop",
        "reason": reason,
    }
    _write_status(payload)
    print(json.dumps(payload, ensure_ascii=False, indent=2))
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--force", action="store_true",
                   help="bypass the configured-or-not check (for development)")
    p.add_argument("--dry-run", action="store_true",
                   help="reserved for future: print the prompt without dispatch")
    args = p.parse_args(argv)

    if not REFILL_PROJECT_URL and not args.force:
        return _stub_no_op(
            "REFILL_PROJECT_URL not configured — set it once the ChatGPT "
            "Omega Outreach project is built and attached files are uploaded."
        )

    if not REFILL_PROMPT_PATH.exists() and not args.force:
        return _stub_no_op(
            f"refill prompt missing at {REFILL_PROMPT_PATH.relative_to(SCRIPT_DIR.parent.parent)}"
        )

    return _stub_no_op("stub: implementation pending")


if __name__ == "__main__":
    raise SystemExit(main())
