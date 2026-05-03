#!/usr/bin/env python3
"""Outreach drafts review TUI — batch-review drafts/ and Apple Mail Drafts.

Lists every draft from two sources side by side:
  1. tools/community-outreach/drafts/*.md      (markdown drafts, human-edited)
  2. Apple Mail Drafts mailbox                 (rendered drafts ready to send)

For each item the operator chooses one of:
  v  view    — print body to stdout (md content + Mail body if both exist)
  o  open    — bring Mail.app foreground at this draft (no auto-send)
  e  edit    — open .md in $EDITOR; manual re-render via the matching .sh
  s  send    — osascript: send the Mail Draft (final external action — final
               approval is THIS keystroke)
  d  discard — delete from Mail Drafts; archive .md to drafts/discarded/<date>/
  n  next    — skip this item (also: just press Enter)
  q  quit    — exit batch

After [s]end:
  - .md (if matched) is moved to drafts/sent/<date>/ for archival
  - if recipient + subject substring appears in OUTREACH_LOG sent-row context,
    no row mutation is performed here — that's outreach_inbox_watcher.py's job
    after the actual reply arrives.

Hard rule: this script never auto-decides to send. Every send requires the
operator to type 's' against the specific draft after viewing.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import textwrap
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional

SCRIPT_DIR = Path(__file__).resolve().parent
DRAFTS_DIR = SCRIPT_DIR / "drafts"
DRAFTS_SENT = DRAFTS_DIR / "sent"
DRAFTS_DISCARDED = DRAFTS_DIR / "discarded"

EMAIL_RE = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")


def _today_dir() -> str:
    return datetime.now().strftime("%Y-%m-%d")


def _short(s: str, n: int) -> str:
    s = (s or "").strip()
    return s if len(s) <= n else s[: n - 1] + "…"


# ---------------------------------------------------------------------------
# Apple Mail bridge
# ---------------------------------------------------------------------------


def _osa(script: str, timeout: int = 30) -> tuple[bool, str, str]:
    if sys.platform != "darwin":
        return (False, "", "not darwin")
    try:
        proc = subprocess.run(
            ["osascript", "-e", script],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except Exception as exc:
        return (False, "", str(exc))
    return (proc.returncode == 0, proc.stdout or "", proc.stderr or "")


def list_mail_drafts() -> list[dict]:
    """Return [{message_id, subject, recipient, date_str}] for Apple Mail Drafts."""
    if sys.platform != "darwin":
        return []
    script = '''
tell application "Mail"
    set msgs to messages of drafts mailbox
    set out to {}
    repeat with m in msgs
        try
            set mid to id of m
            set s to subject of m
            set toAddrs to address of (to recipients of m)
            set d to date sent of m
            if d is missing value then set d to (current date)
            set end of out to (mid as string) & "<<TAB>>" & (toAddrs as string) & "<<TAB>>" & s & "<<TAB>>" & (d as string)
        end try
    end repeat
    return out
end tell
'''
    ok, out, err = _osa(script)
    if not ok:
        return []
    rows: list[dict] = []
    for chunk in out.split(", "):
        chunk = chunk.strip()
        if "<<TAB>>" not in chunk:
            continue
        parts = chunk.split("<<TAB>>")
        if len(parts) < 4:
            continue
        rows.append({
            "message_id": parts[0],
            "recipient": parts[1],
            "subject": parts[2],
            "date_str": parts[3],
        })
    return rows


def get_mail_body(message_id: str) -> str:
    script = f'''
tell application "Mail"
    set m to message id {message_id} of drafts mailbox
    set bodyTxt to content of m as text
    return bodyTxt
end tell
'''
    ok, out, _ = _osa(script, timeout=20)
    return out if ok else ""


def open_mail_draft(message_id: str) -> bool:
    script = f'''
tell application "Mail"
    set m to message id {message_id} of drafts mailbox
    open m
    activate
end tell
'''
    ok, _, err = _osa(script, timeout=10)
    if not ok:
        print(f"  [mail open failed] {err[:200]}", file=sys.stderr)
    return ok


def send_mail_draft(message_id: str) -> bool:
    script = f'''
tell application "Mail"
    set m to message id {message_id} of drafts mailbox
    send m
end tell
'''
    ok, _, err = _osa(script, timeout=30)
    if not ok:
        print(f"  [mail send failed] {err[:200]}", file=sys.stderr)
    return ok


def discard_mail_draft(message_id: str) -> bool:
    script = f'''
tell application "Mail"
    delete (message id {message_id} of drafts mailbox)
end tell
'''
    ok, _, err = _osa(script, timeout=10)
    if not ok:
        print(f"  [mail discard failed] {err[:200]}", file=sys.stderr)
    return ok


# ---------------------------------------------------------------------------
# pairing drafts/ md files with Apple Mail Drafts
# ---------------------------------------------------------------------------


@dataclass
class DraftItem:
    md_path: Optional[Path] = None
    mail_id: Optional[str] = None
    mail_subject: str = ""
    mail_recipient: str = ""
    mail_date: str = ""

    @property
    def label(self) -> str:
        if self.md_path and self.mail_id:
            return f"{self.md_path.name} ↔ Mail#{self.mail_id}"
        if self.md_path:
            return f"{self.md_path.name} (md only)"
        return f"Mail#{self.mail_id} (Mail-only)"

    @property
    def kind(self) -> str:
        if self.md_path and self.mail_id:
            return "paired"
        if self.md_path:
            return "md-only"
        return "mail-only"


def _md_subject_hint(md: Path) -> str:
    try:
        text = md.read_text(encoding="utf-8")
    except OSError:
        return ""
    m = re.search(r"\*\*Subject\*\*\s*[:：]\s*(.+)", text, flags=re.IGNORECASE)
    if m:
        return m.group(1).strip().split("\n", 1)[0].rstrip("*").strip()
    return ""


def _md_recipient_hint(md: Path) -> str:
    try:
        text = md.read_text(encoding="utf-8")
    except OSError:
        return ""
    em = EMAIL_RE.findall(text)
    return em[0] if em else ""


def _normalize_subj(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "").lower()).strip()


def gather_drafts() -> list[DraftItem]:
    md_files: list[Path] = []
    if DRAFTS_DIR.exists():
        for p in sorted(DRAFTS_DIR.iterdir()):
            if p.is_file() and p.suffix == ".md":
                md_files.append(p)
    mail_drafts = list_mail_drafts()

    md_used: set[Path] = set()
    paired: list[DraftItem] = []
    for md in md_files:
        subj_hint = _normalize_subj(_md_subject_hint(md))
        recip_hint = _md_recipient_hint(md).lower()
        match: Optional[dict] = None
        for d in mail_drafts:
            if subj_hint and subj_hint in _normalize_subj(d["subject"]):
                match = d
                break
            if recip_hint and recip_hint in d["recipient"].lower():
                match = d
                break
        if match is not None:
            paired.append(DraftItem(
                md_path=md,
                mail_id=match["message_id"],
                mail_subject=match["subject"],
                mail_recipient=match["recipient"],
                mail_date=match["date_str"],
            ))
            md_used.add(md)
            mail_drafts = [x for x in mail_drafts if x["message_id"] != match["message_id"]]
        else:
            paired.append(DraftItem(md_path=md))
    for d in mail_drafts:
        paired.append(DraftItem(
            mail_id=d["message_id"],
            mail_subject=d["subject"],
            mail_recipient=d["recipient"],
            mail_date=d["date_str"],
        ))
    return paired


# ---------------------------------------------------------------------------
# action handlers
# ---------------------------------------------------------------------------


def action_view(item: DraftItem) -> None:
    print()
    print("=" * 72)
    if item.md_path:
        print(f"--- {item.md_path.name} ---")
        try:
            print(item.md_path.read_text(encoding="utf-8"))
        except OSError as exc:
            print(f"(could not read: {exc})")
    if item.mail_id:
        print()
        print(f"--- Mail Draft #{item.mail_id} (TO: {item.mail_recipient} | SUBJ: {item.mail_subject}) ---")
        body = get_mail_body(item.mail_id)
        if body:
            print(body[:8000])
            if len(body) > 8000:
                print(f"\n... ({len(body) - 8000} more chars truncated)")
        else:
            print("(could not fetch Mail body)")
    print("=" * 72)
    print()


def action_open(item: DraftItem) -> bool:
    if not item.mail_id:
        print("  no Mail Draft to open (md-only); use [e]dit instead")
        return False
    return open_mail_draft(item.mail_id)


def action_edit(item: DraftItem) -> None:
    if not item.md_path:
        print("  no .md file (Mail-only draft); open in Mail.app to edit")
        return
    editor = os.environ.get("EDITOR") or shutil.which("vim") or shutil.which("nano") or "vi"
    try:
        subprocess.run([editor, str(item.md_path)], check=False)
    except Exception as exc:
        print(f"  editor failed: {exc}")
        return
    print(f"  edited {item.md_path.name}")
    if item.mail_id:
        print(f"  NOTE: Mail Draft #{item.mail_id} is now stale relative to .md.")
        print(f"  re-render via the matching save_*.sh script if needed before sending.")


def action_send(item: DraftItem) -> bool:
    if not item.mail_id:
        print("  no Mail Draft to send; render via save_*.sh first")
        return False
    confirm = input(f"  CONFIRM SEND to {item.mail_recipient[:80]} | {item.mail_subject[:80]} ? [y/N] ").strip().lower()
    if confirm != "y":
        print("  send cancelled")
        return False
    ok = send_mail_draft(item.mail_id)
    if not ok:
        return False
    print(f"  ✓ sent")
    if item.md_path:
        DRAFTS_SENT.mkdir(parents=True, exist_ok=True)
        target_dir = DRAFTS_SENT / _today_dir()
        target_dir.mkdir(parents=True, exist_ok=True)
        new_path = target_dir / item.md_path.name
        try:
            item.md_path.rename(new_path)
            print(f"  archived md → {new_path.relative_to(SCRIPT_DIR)}")
        except OSError as exc:
            print(f"  md archive failed: {exc}")
    return True


def action_discard(item: DraftItem) -> bool:
    if not item.mail_id and not item.md_path:
        return False
    confirm = input(f"  CONFIRM DISCARD {_short(item.label, 60)} ? [y/N] ").strip().lower()
    if confirm != "y":
        print("  discard cancelled")
        return False
    if item.mail_id:
        if not discard_mail_draft(item.mail_id):
            print("  Mail discard failed; aborting")
            return False
        print(f"  ✓ Mail Draft #{item.mail_id} deleted")
    if item.md_path:
        DRAFTS_DISCARDED.mkdir(parents=True, exist_ok=True)
        target_dir = DRAFTS_DISCARDED / _today_dir()
        target_dir.mkdir(parents=True, exist_ok=True)
        new_path = target_dir / item.md_path.name
        try:
            item.md_path.rename(new_path)
            print(f"  archived md → {new_path.relative_to(SCRIPT_DIR)}")
        except OSError as exc:
            print(f"  md archive failed: {exc}")
    return True


# ---------------------------------------------------------------------------
# main TUI
# ---------------------------------------------------------------------------


def _print_header(idx: int, total: int, item: DraftItem) -> None:
    print()
    print(f"━━ [{idx}/{total}] {item.kind} ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    if item.md_path:
        try:
            mtime = item.md_path.stat().st_mtime
            age_days = (datetime.now().timestamp() - mtime) / 86400.0
            print(f"  md:        {item.md_path.name}  (age {age_days:.1f}d)")
        except OSError:
            print(f"  md:        {item.md_path.name}")
        subj_hint = _md_subject_hint(item.md_path)
        recip_hint = _md_recipient_hint(item.md_path)
        if subj_hint:
            print(f"  subject:   {_short(subj_hint, 90)}")
        if recip_hint:
            print(f"  recipient: {recip_hint}")
    if item.mail_id:
        print(f"  Mail#{item.mail_id}: TO {_short(item.mail_recipient, 60)}")
        print(f"  subject:   {_short(item.mail_subject, 90)}")
        print(f"  date:      {_short(item.mail_date, 60)}")


def _prompt() -> str:
    return input("  [v]iew [o]pen [e]dit [s]end [d]iscard [n]ext [q]uit > ").strip().lower()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--md-only", action="store_true", help="only review .md files (skip Mail-only)")
    ap.add_argument("--mail-only", action="store_true", help="only review Mail Drafts (skip md-only)")
    ap.add_argument("--paired-only", action="store_true", help="only review items where both .md and Mail exist")
    args = ap.parse_args()

    items = gather_drafts()
    if args.md_only:
        items = [i for i in items if i.md_path]
    if args.mail_only:
        items = [i for i in items if i.mail_id]
    if args.paired_only:
        items = [i for i in items if i.md_path and i.mail_id]

    if not items:
        print("(no drafts to review)")
        return 0

    print(f"\n{len(items)} drafts to review.\n")
    counts = {"sent": 0, "discarded": 0, "skipped": 0, "edited": 0, "viewed": 0}
    for idx, item in enumerate(items, 1):
        _print_header(idx, len(items), item)
        while True:
            choice = _prompt()
            if choice in ("", "n", "next"):
                counts["skipped"] += 1
                break
            if choice == "q" or choice == "quit":
                print("\nsummary:", counts)
                return 0
            if choice == "v" or choice == "view":
                action_view(item)
                counts["viewed"] += 1
                continue
            if choice == "o" or choice == "open":
                action_open(item)
                continue
            if choice == "e" or choice == "edit":
                action_edit(item)
                counts["edited"] += 1
                continue
            if choice == "s" or choice == "send":
                if action_send(item):
                    counts["sent"] += 1
                    break
                continue
            if choice == "d" or choice == "discard":
                if action_discard(item):
                    counts["discarded"] += 1
                    break
                continue
            print("  unknown command")
    print("\nsummary:", counts)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
