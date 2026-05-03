#!/usr/bin/env python3
"""Outreach inbox watcher — Apple Mail Inbox → OUTREACH_LOG correlation.

Scans Apple Mail Inbox for new messages since the last cursor; matches each
against the "Active Targets" rows in OUTREACH_LOG.md by recipient address and
sender heuristics; for matches it:

  1. Auto-updates the matched OUTREACH_LOG row status from
     "sent YYYY-MM-DD ... reply pending" → "replied YYYY-MM-DD <subject snip>"
     (board mutation only — never modifies Mail content).
  2. Appends a short "REPLY from <sender>" entry to .outreach_human_inbox.md
     so the operator sees it on next supervisor cycle.

Matching is conservative: we only flag a reply when the sender address appears
in some "sent ... <addr>" status text or the subject begins with "Re: " of a
sent subject substring. Spam / unrelated messages get reported in the inbox
file but never modify the LOG.

Cursor: outreach_state/inbox_cursor.json — tracks last seen Mail.app message
date so re-runs don't double-process.

Usage:
  python3 outreach_inbox_watcher.py            # default: last 14 days, write changes
  python3 outreach_inbox_watcher.py --dry-run  # report what would change
  python3 outreach_inbox_watcher.py --days 30  # broader window on first run
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
STATE_DIR = SCRIPT_DIR / "outreach_state"
CURSOR_FILE = STATE_DIR / "inbox_cursor.json"
OUTREACH_LOG = SCRIPT_DIR / "OUTREACH_LOG.md"
HUMAN_INBOX = SCRIPT_DIR / ".outreach_human_inbox.md"

EMAIL_RE = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")
ROW_RE = re.compile(r"^\|([^|]+)\|([^|]+)\|([^|]+)\|([^|]+)\|([^|]+)\|([^|]+)\|\s*$")

DEFAULT_DAYS = 14


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _today() -> str:
    return datetime.now().strftime("%Y-%m-%d")


def _load_cursor() -> dict:
    if not CURSOR_FILE.exists():
        return {}
    try:
        return json.loads(CURSOR_FILE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def _save_cursor(cursor: dict) -> None:
    CURSOR_FILE.parent.mkdir(parents=True, exist_ok=True)
    CURSOR_FILE.write_text(json.dumps(cursor, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def fetch_inbox(days: int) -> list[dict]:
    """Return last N days of Apple Mail Inbox messages.

    Each item: {sender, subject, date_str, message_id}. Failures return []
    silently — caller decides how to surface."""
    if sys.platform != "darwin":
        return []
    script = f'''
on dateAfter(d, n)
    return d - (n * 24 * 60 * 60)
end dateAfter

tell application "Mail"
    set cutoff to my dateAfter(current date, {days})
    set matches to (messages of inbox whose date received > cutoff)
    set out to {{}}
    repeat with m in matches
        try
            set s to subject of m
            set fr to sender of m
            set d to date received of m
            set mid to id of m
            set end of out to (mid as string) & "<<TAB>>" & fr & "<<TAB>>" & s & "<<TAB>>" & (d as string)
        end try
    end repeat
    return out
end tell
'''
    try:
        proc = subprocess.run(
            ["osascript", "-e", script],
            capture_output=True,
            text=True,
            timeout=60,
        )
    except Exception as exc:
        print(f"[inbox_watcher] osascript failed: {exc}", file=sys.stderr)
        return []
    if proc.returncode != 0:
        print(f"[inbox_watcher] osascript rc={proc.returncode}: {(proc.stderr or '')[:200]}", file=sys.stderr)
        return []
    rows: list[dict] = []
    for chunk in (proc.stdout or "").split(", "):
        chunk = chunk.strip()
        if "<<TAB>>" not in chunk:
            continue
        parts = chunk.split("<<TAB>>")
        if len(parts) < 4:
            continue
        rows.append({
            "message_id": parts[0],
            "sender": parts[1],
            "subject": parts[2],
            "date_str": parts[3],
        })
    return rows


def parse_outreach_log_active() -> list[dict]:
    """Pull Active Targets rows with full status text + extracted recipient address."""
    if not OUTREACH_LOG.exists():
        return []
    text = OUTREACH_LOG.read_text(encoding="utf-8")
    in_active = False
    out: list[dict] = []
    for line in text.splitlines():
        if line.startswith("## Active Targets"):
            in_active = True
            continue
        if in_active and line.startswith("## "):
            break
        if not in_active:
            continue
        m = ROW_RE.match(line)
        if not m:
            continue
        cells = [c.strip() for c in m.groups()]
        if cells[0].lower() == "target" or set(cells[0]) <= {"-", " "}:
            continue
        emails_in_row = EMAIL_RE.findall(" ".join(cells))
        out.append({
            "raw": line,
            "target": cells[0],
            "channel": cells[1],
            "status": cells[2],
            "emails": emails_in_row,
            "last_update": cells[5],
            "cells": cells,
        })
    return out


def correlate(messages: list[dict], rows: list[dict], cursor_seen_ids: set[str]) -> list[dict]:
    """For each Inbox message, find matching OUTREACH_LOG row.

    Match rules (any one suffices):
      - sender's email appears in row's email cells
      - subject contains row's target identifier substrings (target/title fragments)
        AND row status contains "sent" or "pending"
      - subject starts with "Re: " followed by a string that matches a known
        sent subject (we don't have a sent-subject cache yet → drop this rule
        until we extend OUTREACH_LOG with a 'sent_subject' field)

    Conservative: false negative is OK; false positive is bad (would corrupt
    OUTREACH_LOG). Only first match wins."""
    out: list[dict] = []
    for msg in messages:
        if msg["message_id"] in cursor_seen_ids:
            continue
        sender_emails = EMAIL_RE.findall(msg["sender"])
        match_row: dict | None = None
        match_reason = ""
        for row in rows:
            row_emails = {e.lower() for e in row["emails"]}
            if not row_emails:
                continue
            for s_email in sender_emails:
                if s_email.lower() in row_emails:
                    match_row = row
                    match_reason = f"sender {s_email} in row emails"
                    break
            if match_row:
                break
        out.append({
            "message": msg,
            "matched_row": match_row,
            "match_reason": match_reason,
        })
    return out


def update_outreach_log(matches: list[dict], dry_run: bool) -> list[str]:
    """For each match where row.status contains 'reply pending' or 'pending',
    rewrite the status to 'replied <date> — Re: <subject snip>'.

    Returns list of human-readable change descriptions."""
    if not matches:
        return []
    text = OUTREACH_LOG.read_text(encoding="utf-8")
    new_lines: list[str] = []
    changes: list[str] = []
    today = _today()
    rows_to_update_by_raw: dict[str, dict] = {}
    for entry in matches:
        row = entry.get("matched_row")
        if not row:
            continue
        status = row["status"].lower()
        if "reply pending" not in status and "pending" not in status:
            continue
        rows_to_update_by_raw[row["raw"]] = entry

    if not rows_to_update_by_raw:
        return []

    for line in text.splitlines():
        m = ROW_RE.match(line)
        if not m or line not in rows_to_update_by_raw:
            new_lines.append(line)
            continue
        entry = rows_to_update_by_raw[line]
        cells = [c.strip() for c in m.groups()]
        msg = entry["message"]
        subj_snip = msg["subject"][:70].replace("|", "/")
        sender_snip = msg["sender"][:60].replace("|", "/")
        # Use ` :: ` not ` | ` — pipe breaks markdown table column count.
        new_status = f"replied {today} — {sender_snip} :: {subj_snip}"
        cells[2] = new_status
        cells[5] = today
        new_line = "| " + " | ".join(cells) + " |"
        new_lines.append(new_line)
        changes.append(f"{cells[0][:60]}: {row['status'][:80]} → {new_status[:90]}")

    if changes and not dry_run:
        OUTREACH_LOG.write_text("\n".join(new_lines) + ("\n" if text.endswith("\n") else ""), encoding="utf-8")
    return changes


def append_inbox_summary(matches: list[dict], log_changes: list[str]) -> None:
    """Always append a summary block to .outreach_human_inbox.md so the
    operator sees what was matched (and what wasn't)."""
    if not matches:
        return
    HUMAN_INBOX.parent.mkdir(parents=True, exist_ok=True)
    lines = [f"\n## inbox_watcher {_now_iso()}"]
    matched = [e for e in matches if e["matched_row"]]
    unmatched = [e for e in matches if not e["matched_row"]]
    if matched:
        lines.append(f"\n### {len(matched)} replies matched to active targets\n")
        for entry in matched:
            msg = entry["message"]
            row = entry["matched_row"]
            target_snip = row["target"][:60]
            lines.append(f"- **{target_snip}** ← {msg['sender'][:80]}: {msg['subject'][:120]} ({entry['match_reason']})")
    if log_changes:
        lines.append(f"\n### {len(log_changes)} OUTREACH_LOG status updates applied\n")
        for ch in log_changes:
            lines.append(f"- {ch}")
    if unmatched:
        lines.append(f"\n### {len(unmatched)} new Inbox messages with no OUTREACH_LOG match\n")
        for entry in unmatched[:20]:
            msg = entry["message"]
            lines.append(f"- {msg['sender'][:80]}: {msg['subject'][:120]}")
        if len(unmatched) > 20:
            lines.append(f"- ... ({len(unmatched) - 20} more)")
    with open(HUMAN_INBOX, "a", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--days", type=int, default=DEFAULT_DAYS,
                    help=f"window of Inbox messages to scan (default {DEFAULT_DAYS})")
    ap.add_argument("--dry-run", action="store_true",
                    help="report changes but do not modify OUTREACH_LOG / inbox file")
    args = ap.parse_args()

    cursor = _load_cursor()
    seen_ids = set(cursor.get("seen_message_ids") or [])

    messages = fetch_inbox(args.days)
    if not messages and sys.platform == "darwin":
        print("[inbox_watcher] no Inbox messages returned (Mail.app may not be running or have no recent mail)")
        return 0

    rows = parse_outreach_log_active()
    matches = correlate(messages, rows, seen_ids)

    if not matches:
        print(f"[inbox_watcher] {len(messages)} Inbox messages scanned, all already seen in cursor")
        return 0

    changes = update_outreach_log(matches, dry_run=args.dry_run)
    if not args.dry_run:
        append_inbox_summary(matches, changes)
        new_seen = sorted({e["message"]["message_id"] for e in matches} | seen_ids)
        cursor["seen_message_ids"] = new_seen[-2000:]
        cursor["last_run_iso"] = _now_iso()
        cursor["last_run_messages_scanned"] = len(messages)
        cursor["last_run_matched"] = len([e for e in matches if e["matched_row"]])
        _save_cursor(cursor)

    matched_n = len([e for e in matches if e["matched_row"]])
    print(f"[inbox_watcher] {len(messages)} scanned, {len(matches)} new, {matched_n} matched, {len(changes)} log updates"
          + (" (dry-run)" if args.dry_run else ""))
    for ch in changes:
        print(f"  {ch}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
