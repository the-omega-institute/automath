#!/usr/bin/env python3
"""Approval ledger for human-gated outreach sends.

The pipeline may generate drafts automatically, but external actions require an
explicit approval record. This module records approvals locally; send/post
commands should require an approval id before performing external actions.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
STATE_DIR = SCRIPT_DIR / "outreach_state"
LEDGER = STATE_DIR / "approval_ledger.jsonl"


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _approval_id(payload: dict) -> str:
    raw = json.dumps(payload, ensure_ascii=False, sort_keys=True) + str(time.time())
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:12]


def record_approval(*, target_id: str, action: str, artifact: str, note: str = "") -> dict:
    if action not in {"send_email", "post_issue", "post_pr_comment", "post_forum", "post_x", "publish_paper"}:
        raise ValueError(f"unsupported action: {action}")
    payload = {
        "target_id": target_id,
        "action": action,
        "artifact": artifact,
        "note": note,
        "approved_at": _now_iso(),
    }
    payload["approval_id"] = _approval_id(payload)
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    with open(LEDGER, "a", encoding="utf-8") as f:
        f.write(json.dumps(payload, ensure_ascii=False) + "\n")
    return payload


def list_approvals() -> list[dict]:
    if not LEDGER.exists():
        return []
    rows: list[dict] = []
    for line in LEDGER.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError:
            continue
    return rows


def find_approval(approval_id: str) -> dict | None:
    for row in list_approvals():
        if row.get("approval_id") == approval_id:
            return row
    return None


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="cmd", required=True)
    approve = sub.add_parser("approve", help="record explicit operator approval")
    approve.add_argument("--target-id", required=True)
    approve.add_argument("--action", required=True)
    approve.add_argument("--artifact", required=True)
    approve.add_argument("--note", default="")
    sub.add_parser("list", help="list approvals")
    args = p.parse_args(argv)
    if args.cmd == "approve":
        print(json.dumps(record_approval(
            target_id=args.target_id,
            action=args.action,
            artifact=args.artifact,
            note=args.note,
        ), ensure_ascii=False, indent=2))
        return 0
    if args.cmd == "list":
        print(json.dumps(list_approvals(), ensure_ascii=False, indent=2))
        return 0
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
