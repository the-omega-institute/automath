#!/usr/bin/env python3
"""Targeted context refresh before starting the outreach pipeline.

This tool refreshes only threads explicitly registered in local outreach state:

  - GitHub issue / PR URLs in RESEARCH_BOARD, OUTREACH_LOG, or task_queue JSON
  - Apple Mail threads identified by explicit subject/email fields in task JSON
    or OUTREACH_LOG rows

It is intentionally not a broad inbox or internet scanner. The output is a
local snapshot for progress tracking and duplicate avoidance. Registered
emails / GitHub threads are NOT board-refill sources; they should be advanced
under their existing task/target until they are explicitly closed.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_DIR = SCRIPT_DIR / "outreach_state"
TASK_QUEUE_DIR = STATE_DIR / "task_queue"
SNAPSHOT_PATH = STATE_DIR / "context_refresh.json"
BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"
OUTREACH_LOG = SCRIPT_DIR / "OUTREACH_LOG.md"

EMAIL_RE = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")
GH_ISSUE_RE = re.compile(
    r"https://github\.com/([^/\s)]+)/([^/\s)]+)/(issues|pull)/(\d+)",
    re.IGNORECASE,
)
BACKTICK_SUBJECT_RE = re.compile(r"subject\s+`([^`]+)`", re.IGNORECASE)
MAIL_SCAN_LIMIT_PER_BOX = 250
MAIL_QUERY_TIMEOUT_S = 25


@dataclass
class GitHubThreadRef:
    repo: str
    kind: str
    number: int
    url: str
    sources: list[str] = field(default_factory=list)


@dataclass
class MailThreadRef:
    subject: str = ""
    email: str = ""
    person: str = ""
    sources: list[str] = field(default_factory=list)


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def _load_task_jsons() -> list[tuple[Path, dict]]:
    out: list[tuple[Path, dict]] = []
    if not TASK_QUEUE_DIR.exists():
        return out
    for p in sorted(TASK_QUEUE_DIR.glob("*.json")):
        try:
            out.append((p, json.loads(p.read_text(encoding="utf-8"))))
        except (OSError, json.JSONDecodeError):
            continue
    return out


def _add_gh(refs: dict[tuple[str, str, int], GitHubThreadRef], url: str, source: str) -> None:
    m = GH_ISSUE_RE.search(url)
    if not m:
        return
    owner, name, kind, num = m.groups()
    repo = f"{owner}/{name}"
    n = int(num)
    key = (repo, kind, n)
    ref = refs.get(key)
    if ref is None:
        ref = GitHubThreadRef(repo=repo, kind=kind, number=n, url=f"https://github.com/{repo}/{kind}/{n}")
        refs[key] = ref
    if source not in ref.sources:
        ref.sources.append(source)


def _add_mail(
    refs: dict[tuple[str, str], MailThreadRef],
    *,
    subject: str = "",
    email: str = "",
    person: str = "",
    source: str,
) -> None:
    subject = subject.strip()
    email = email.strip()
    person = person.strip()
    if not subject and not email:
        return
    key = (subject.lower(), email.lower())
    ref = refs.get(key)
    if ref is None:
        ref = MailThreadRef(subject=subject, email=email, person=person)
        refs[key] = ref
    if person and not ref.person:
        ref.person = person
    if source not in ref.sources:
        ref.sources.append(source)


def collect_registered_refs() -> tuple[list[GitHubThreadRef], list[MailThreadRef]]:
    gh_refs: dict[tuple[str, str, int], GitHubThreadRef] = {}
    mail_refs: dict[tuple[str, str], MailThreadRef] = {}

    for label, path in (("board", BOARD_PATH), ("outreach_log", OUTREACH_LOG)):
        text = _read_text(path)
        for m in GH_ISSUE_RE.finditer(text):
            _add_gh(gh_refs, m.group(0), label)
        for line in text.splitlines():
            emails = EMAIL_RE.findall(line)
            if not emails:
                continue
            # OUTREACH_LOG rows are concise enough that using the row prefix as
            # person/context is more useful than trying to parse all columns.
            person = line.strip().strip("|").split("|", 1)[0].strip()[:120]
            for email in emails:
                _add_mail(mail_refs, email=email, person=person, source=label)

    for path, task in _load_task_jsons():
        source = f"task:{task.get('id') or path.stem}"
        ctx = task.get("context") or {}
        thread = str(ctx.get("thread") or "")
        for m in GH_ISSUE_RE.finditer(thread):
            _add_gh(gh_refs, m.group(0), source)
        subj = ""
        sm = BACKTICK_SUBJECT_RE.search(thread)
        if sm:
            subj = sm.group(1)
        external = str(ctx.get("external_party") or "")
        emails = EMAIL_RE.findall(external + " " + thread)
        person = external.split("<", 1)[0].strip()
        for email in emails:
            _add_mail(mail_refs, subject=subj, email=email, person=person, source=source)
        if subj and not emails:
            _add_mail(mail_refs, subject=subj, source=source)

    return list(gh_refs.values()), list(mail_refs.values())


def refresh_github(ref: GitHubThreadRef, *, dry_run: bool = False) -> dict:
    out = {
        "repo": ref.repo,
        "kind": ref.kind,
        "number": ref.number,
        "url": ref.url,
        "sources": ref.sources,
        "status": "dry_run" if dry_run else "unknown",
    }
    if dry_run:
        return out
    endpoint = f"repos/{ref.repo}/{ref.kind}/{ref.number}"
    comments_endpoint = f"repos/{ref.repo}/{ref.kind}/{ref.number}/comments?per_page=5"
    if ref.kind == "pull":
        endpoint = f"repos/{ref.repo}/pulls/{ref.number}"
        comments_endpoint = f"repos/{ref.repo}/issues/{ref.number}/comments?per_page=5"
    try:
        meta = subprocess.run(
            ["gh", "api", endpoint],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=30,
        )
        if meta.returncode != 0:
            out["status"] = "error"
            out["error"] = (meta.stderr or meta.stdout)[:500]
            return out
        payload = json.loads(meta.stdout)
        out.update({
            "status": "ok",
            "state": payload.get("state"),
            "title": payload.get("title"),
            "updated_at": payload.get("updated_at"),
            "comments": payload.get("comments"),
            "author": (payload.get("user") or {}).get("login"),
        })
        comments = subprocess.run(
            ["gh", "api", comments_endpoint],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=30,
        )
        if comments.returncode == 0:
            rows = json.loads(comments.stdout)
            if isinstance(rows, list):
                out["recent_comments"] = [
                    {
                        "user": (c.get("user") or {}).get("login"),
                        "created_at": c.get("created_at"),
                        "updated_at": c.get("updated_at"),
                        "body_head": (c.get("body") or "")[:500],
                    }
                    for c in rows[-5:]
                    if isinstance(c, dict)
                ]
    except Exception as exc:  # noqa: BLE001
        out["status"] = "error"
        out["error"] = str(exc)
    return out


def _mail_osascript(ref: MailThreadRef, idx: int, days: int) -> str:
    subj = ref.subject.replace('"', '\\"')
    email = ref.email.replace('"', '\\"')
    inbox_filters: list[str] = []
    sent_filters: list[str] = []
    if email:
        inbox_filters.append(f'sender contains "{email}"')
        sent_filters.append(f'(sender contains "{email}" or subject contains "{subj}")' if subj else f'sender contains "{email}"')
    if subj:
        inbox_filters.append(f'subject contains "{subj}"')
        sent_filters.append(f'subject contains "{subj}"')
    inbox_filter = " or ".join(inbox_filters) or "false"
    sent_filter = " or ".join(sent_filters) or "false"
    return f'''
on scrubText(t)
    try
        set s to t as text
    on error
        set s to ""
    end try
    set oldDelims to AppleScript's text item delimiters
    set AppleScript's text item delimiters to return
    set parts to text items of s
    set AppleScript's text item delimiters to " "
    set s to parts as text
    set AppleScript's text item delimiters to linefeed
    set parts to text items of s
    set AppleScript's text item delimiters to " "
    set s to parts as text
    set AppleScript's text item delimiters to tab
    set parts to text items of s
    set AppleScript's text item delimiters to " "
    set s to parts as text
    set AppleScript's text item delimiters to "<<ROW>>"
    set parts to text items of s
    set AppleScript's text item delimiters to " "
    set s to parts as text
    set AppleScript's text item delimiters to "<<TAB>>"
    set parts to text items of s
    set AppleScript's text item delimiters to " "
    set s to parts as text
    set AppleScript's text item delimiters to oldDelims
    if (length of s) > 4000 then set s to text 1 thru 4000 of s
    return s
end scrubText

on dateAfter(d, n)
    return d - (n * 24 * 60 * 60)
end dateAfter

tell application "Mail"
    set cutoff to my dateAfter(current date, {days})
    set out to {{}}

    repeat with acct in accounts
        try
            set box to mailbox "Inbox" of acct
            set matches to messages of box whose ({inbox_filter})
            set ctr to 0
            repeat with m in matches
                if ctr ≥ {MAIL_SCAN_LIMIT_PER_BOX} then exit repeat
                set ctr to ctr + 1
                try
                    set msgDate to date received of m
                    if msgDate is not less than cutoff then
                        set mid to id of m
                        set fr to sender of m
                        set s to subject of m
                        set bodyHead to my scrubText(content of m)
                        set end of out to "{idx}" & "<<TAB>>inbox<<TAB>>" & (mid as string) & "<<TAB>>" & fr & "<<TAB>>" & s & "<<TAB>>" & (msgDate as string) & "<<TAB>>" & bodyHead
                    end if
                end try
            end repeat
        end try

        try
            set box to mailbox "Sent Items" of acct
            set matches to messages of box whose ({sent_filter})
            set ctr to 0
            repeat with m in matches
                if ctr ≥ {MAIL_SCAN_LIMIT_PER_BOX} then exit repeat
                set ctr to ctr + 1
                try
                    set msgDate to date sent of m
                    if msgDate is not less than cutoff then
                        set toAddrs to ""
                        try
                            set toAddrs to address of (to recipients of m) as string
                        end try
                        if "{email}" is "" or toAddrs contains "{email}" or sender of m contains "{email}" then
                            set mid to id of m
                            set fr to sender of m
                            set s to subject of m
                            set bodyHead to my scrubText(content of m)
                            set end of out to "{idx}" & "<<TAB>>sent<<TAB>>" & (mid as string) & "<<TAB>>" & fr & " -> " & toAddrs & "<<TAB>>" & s & "<<TAB>>" & (msgDate as string) & "<<TAB>>" & bodyHead
                        end if
                    end if
                end try
            end repeat
        end try
    end repeat
    set oldDelims to AppleScript's text item delimiters
    set AppleScript's text item delimiters to "<<ROW>>"
    set joinedOut to out as text
    set AppleScript's text item delimiters to oldDelims
    return joinedOut
end tell
'''


def _parse_mail_stdout(stdout: str, rows: list[dict]) -> None:
    for chunk in (stdout or "").split("<<ROW>>"):
        if "<<TAB>>" not in chunk:
            continue
        parts = chunk.strip().split("<<TAB>>")
        if len(parts) < 6:
            continue
        try:
            idx = int(parts[0])
        except ValueError:
            continue
        if 0 <= idx < len(rows):
            rows[idx]["messages"].append({
                "mailbox": parts[1],
                "message_id": parts[2],
                "sender": parts[3],
                "subject": parts[4],
                "date_str": parts[5],
                "body_head": parts[6] if len(parts) > 6 else "",
            })


def refresh_mail(refs: list[MailThreadRef], *, days: int, dry_run: bool = False) -> list[dict]:
    rows = [
        {
            "subject": r.subject,
            "email": r.email,
            "person": r.person,
            "sources": r.sources,
            "status": "dry_run" if dry_run else "unknown",
            "messages": [],
        }
        for r in refs
    ]
    if dry_run or not refs:
        return rows
    if sys.platform != "darwin":
        for row in rows:
            row["status"] = "skipped"
            row["error"] = "Apple Mail refresh only available on macOS"
        return rows
    for row in rows:
        row["status"] = "ok"
    for idx, ref in enumerate(refs):
        script = _mail_osascript(ref, idx, days)
        try:
            proc = subprocess.run(
                ["osascript", "-e", script],
                capture_output=True,
                text=True,
                timeout=MAIL_QUERY_TIMEOUT_S,
            )
        except Exception as exc:  # noqa: BLE001
            rows[idx]["status"] = "error"
            rows[idx]["error"] = str(exc)
            continue
        if proc.returncode != 0:
            rows[idx]["status"] = "error"
            rows[idx]["error"] = (proc.stderr or proc.stdout)[:500]
            continue
        _parse_mail_stdout(proc.stdout, rows)
    return rows


def build_snapshot(*, days: int, dry_run: bool = False, github: bool = True, mail: bool = True) -> dict:
    gh_refs, mail_refs = collect_registered_refs()
    return {
        "generated_at": _now_iso(),
        "dry_run": dry_run,
        "scope": "registered_threads_only",
        "registered": {
            "github_threads": [asdict(r) for r in gh_refs],
            "mail_threads": [asdict(r) for r in mail_refs],
        },
        "github": [refresh_github(r, dry_run=dry_run) for r in gh_refs] if github else [],
        "mail": refresh_mail(mail_refs, days=days, dry_run=dry_run) if mail else [],
    }


def write_snapshot(snapshot: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    SNAPSHOT_PATH.write_text(json.dumps(snapshot, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--days", type=int, default=30, help="mail lookback window for registered threads")
    p.add_argument("--dry-run", action="store_true", help="discover refs only; do not call gh or Mail")
    p.add_argument("--no-github", action="store_true", help="skip GitHub refresh")
    p.add_argument("--no-mail", action="store_true", help="skip Mail refresh")
    p.add_argument("--write", action="store_true", help="write outreach_state/context_refresh.json")
    p.add_argument("--json", action="store_true", help="print full JSON")
    args = p.parse_args(argv)

    snapshot = build_snapshot(
        days=args.days,
        dry_run=args.dry_run,
        github=not args.no_github,
        mail=not args.no_mail,
    )
    if args.write and not args.dry_run:
        write_snapshot(snapshot)
    if args.json:
        print(json.dumps(snapshot, ensure_ascii=False, indent=2))
    else:
        reg = snapshot["registered"]
        print(
            f"registered refs: github={len(reg['github_threads'])} "
            f"mail={len(reg['mail_threads'])} dry_run={args.dry_run}"
        )
        for row in snapshot["github"][:12]:
            print(f"  gh {row['repo']} {row['kind']}#{row['number']} status={row['status']} sources={','.join(row['sources'])}")
        for row in snapshot["mail"][:12]:
            label = row.get("subject") or row.get("email")
            print(f"  mail {label!r} status={row['status']} messages={len(row.get('messages') or [])} sources={','.join(row['sources'])}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
