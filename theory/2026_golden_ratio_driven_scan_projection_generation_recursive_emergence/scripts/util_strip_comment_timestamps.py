#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Strip auto-inserted timestamp comments from paper sources.

This repository occasionally accumulates comment lines that only record "added/modified"
timestamps (e.g. "日期与时间：YYYY-MM-DD HH:MM:SS" or "Time (local timezone): ...").
These lines are metadata and should not appear in the manuscript sources.

Policy implemented here:
  - Remove full-line comments (LaTeX: '% ...', Python: '# ...') that look like
    timestamp records.
  - Additionally, for LaTeX sources, remove standalone provenance lines that
    are clearly timestamps even when they were inserted as non-comment text
    (e.g. "当前时间：YYYY-MM-DD HH:MM:SS（Asia/Singapore）").
  - A line is treated as a timestamp record if (and only if) it satisfies one
    of the following:
      * starts with "日期与时间" or "当前时间" (with a ':' or '：'), OR
      * starts with "Time (local timezone):", OR
      * contains an ISO date pattern (YYYY-MM-DD), with or without a time-of-day.
  - Additionally, for LaTeX sources, remove editorial timestamp notes inside
    `\\footnote{...}` when they are clearly provenance metadata, e.g.:
      * contains "版本记录"  -> drop the whole footnote
      * contains "归档时间戳" -> drop the timestamp clause (or the whole footnote if empty)

The script edits files in place and writes a small JSON report under:
  artifacts/export/strip_comment_timestamps_report.json
"""

from __future__ import annotations

import argparse
import json
import re
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple


@dataclass(frozen=True)
class Change:
    path: str
    removed_lines: int


_ISO_DATE_RE = re.compile(r"\b\d{4}-\d{2}-\d{2}\b")
_CN_TIME_LABEL_RE = re.compile(r"(日期与时间|当前时间)")
_CN_TIME_STANDALONE_LINE_RE = re.compile(
    r"^\s*(?:日期与时间|当前时间(?:日期)?)\s*[:：]"
)
_EN_TIME_STANDALONE_LINE_RE = re.compile(r"^\s*Time\s*\(local timezone\)\s*:")


def _iter_files(root: Path, include_dirs: Sequence[str], exts: Sequence[str]) -> Iterable[Path]:
    for rel in include_dirs:
        base = (root / rel).resolve()
        if not base.exists():
            continue
        if base.is_file():
            if base.suffix in exts:
                yield base
            continue
        for p in base.rglob("*"):
            if not p.is_file():
                continue
            if p.suffix not in exts:
                continue
            yield p


def _comment_prefix_for_suffix(suffix: str) -> str | None:
    if suffix == ".tex":
        return "%"
    if suffix == ".py":
        return "#"
    return None


def _should_strip_comment_line(line: str) -> bool:
    if _CN_TIME_LABEL_RE.search(line):
        return True
    if _ISO_DATE_RE.search(line):
        return True
    return False


def _strip_latex_editorial_timestamp_footnotes(text: str) -> Tuple[str, int]:
    """Strip timestamp provenance footnotes from LaTeX text.

    We only target editorial metadata markers that should not appear in the manuscript
    (e.g. internal version-record timestamps). We do NOT remove general footnotes.
    """

    def parse_bracket_group(s: str, start: int) -> int:
        # start points at '['; return index just after matching ']'
        i = start + 1
        while i < len(s):
            if s[i] == "]" and s[i - 1] != "\\":
                return i + 1
            i += 1
        return start  # malformed; signal failure

    def parse_brace_group(s: str, start: int) -> int:
        # start points at '{'; return index of matching '}' (position), or -1
        depth = 1
        i = start + 1
        while i < len(s):
            ch = s[i]
            if ch == "{" and s[i - 1] != "\\":
                depth += 1
            elif ch == "}" and s[i - 1] != "\\":
                depth -= 1
                if depth == 0:
                    return i
            i += 1
        return -1

    def strip_one(content: str) -> str | None:
        frag = content.strip()
        if frag in {"本段条目链的", "本段条目链的。", "本段条目链的．", "本段条目链的."}:
            return None
        if "版本记录" in content:
            return None
        if "归档时间戳" in content:
            before = content.split("归档时间戳", 1)[0].rstrip()
            before_clean = before.strip()
            if before_clean in {"本段条目链的", "本段条目链"}:
                return None
            # Heuristic: if we would leave a dangling possessive like "...的", drop the note.
            if before_clean.endswith("的") and len(before_clean) <= 12:
                return None
            if before == "":
                return None
            return before
        return content

    edits = 0
    i = 0
    out: List[str] = []
    while True:
        idx = text.find("\\footnote", i)
        if idx < 0:
            out.append(text[i:])
            break

        out.append(text[i:idx])
        j = idx + len("\\footnote")

        # Optional star
        if j < len(text) and text[j] == "*":
            j += 1

        # Skip whitespace
        while j < len(text) and text[j].isspace():
            j += 1

        # Optional [..] groups
        while j < len(text) and text[j] == "[":
            j2 = parse_bracket_group(text, j)
            if j2 == j:
                break
            j = j2
            while j < len(text) and text[j].isspace():
                j += 1

        if j >= len(text) or text[j] != "{":
            # Not a standard \footnote{...}; keep verbatim and continue.
            out.append(text[idx : idx + len("\\footnote")])
            i = idx + len("\\footnote")
            continue

        brace_open = j
        brace_close = parse_brace_group(text, brace_open)
        if brace_close < 0:
            # Malformed; keep verbatim.
            out.append(text[idx:])
            break

        content = text[brace_open + 1 : brace_close]
        new_content = strip_one(content)

        if new_content is None:
            edits += 1
            i = brace_close + 1
            continue

        if new_content != content:
            edits += 1
        out.append(text[idx : brace_open + 1])
        out.append(new_content)
        out.append("}")
        i = brace_close + 1

    return ("".join(out), edits)


def _process_file(path: Path) -> Tuple[bool, int]:
    prefix = _comment_prefix_for_suffix(path.suffix)
    if prefix is None:
        return (False, 0)

    original = path.read_text(encoding="utf-8")
    lines = original.splitlines(keepends=True)

    removed = 0
    out_lines: List[str] = []
    for ln in lines:
        # For LaTeX sources, drop standalone timestamp provenance lines even if
        # they were inserted as non-comment text.
        if path.suffix == ".tex":
            s0 = ln.strip()
            if s0 and (_CN_TIME_STANDALONE_LINE_RE.match(s0) or _EN_TIME_STANDALONE_LINE_RE.match(s0)):
                removed += 1
                continue

        s = ln.lstrip()
        if s.startswith(prefix) and _should_strip_comment_line(s):
            removed += 1
            continue
        out_lines.append(ln)

    new_text = "".join(out_lines)

    # Strip timestamp provenance inside LaTeX footnotes (editorial only).
    if path.suffix == ".tex":
        new_text2, footnote_edits = _strip_latex_editorial_timestamp_footnotes(new_text)
        new_text = new_text2
        removed += footnote_edits  # count as "removed items" for reporting

    if removed == 0 and new_text == original:
        return (False, 0)

    path.write_text(new_text, encoding="utf-8")
    return (True, removed)


def main() -> None:
    parser = argparse.ArgumentParser(description="Strip timestamp-only comment lines.")
    parser.add_argument(
        "--root",
        type=str,
        default=str(Path(__file__).resolve().parent.parent),
        help="Paper root directory (defaults to scripts/..).",
    )
    parser.add_argument(
        "--include",
        type=str,
        nargs="*",
        default=["sections", "scripts"],
        help="Subdirectories under --root to scan.",
    )
    parser.add_argument(
        "--ext",
        type=str,
        nargs="*",
        default=[".tex", ".py"],
        help="File extensions to process.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Do not write files; only report what would change.",
    )
    args = parser.parse_args()

    root = Path(args.root).resolve()
    include_dirs = list(args.include)
    exts = list(args.ext)

    print(f"[strip_timestamps] root={root}", flush=True)
    print(f"[strip_timestamps] include={include_dirs} ext={exts} dry_run={args.dry_run}", flush=True)

    t0 = time.time()
    last_progress = t0

    changed: List[Change] = []
    scanned = 0
    removed_total = 0

    paths = sorted(_iter_files(root, include_dirs=include_dirs, exts=exts))
    for p in paths:
        scanned += 1
        if (time.time() - last_progress) >= 20.0:
            print(
                f"[strip_timestamps] progress scanned={scanned}/{len(paths)} changed={len(changed)} removed_total={removed_total}",
                flush=True,
            )
            last_progress = time.time()

        if args.dry_run:
            prefix = _comment_prefix_for_suffix(p.suffix)
            if prefix is None:
                continue
            text = p.read_text(encoding="utf-8")
            lines = text.splitlines(keepends=True)

            removed = 0
            out_lines: List[str] = []
            for ln in lines:
                s = ln.lstrip()
                if s.startswith(prefix) and _should_strip_comment_line(s):
                    removed += 1
                    continue
                out_lines.append(ln)

            new_text = "".join(out_lines)
            if p.suffix == ".tex":
                new_text2, footnote_edits = _strip_latex_editorial_timestamp_footnotes(new_text)
                new_text = new_text2
                removed += footnote_edits

            if removed > 0 or new_text != text:
                changed.append(Change(path=str(p.relative_to(root)), removed_lines=removed))
                removed_total += removed
            continue

        did_change, removed = _process_file(p)
        if did_change:
            changed.append(Change(path=str(p.relative_to(root)), removed_lines=removed))
            removed_total += removed

    dt = time.time() - t0
    print(
        f"[strip_timestamps] done scanned={scanned} changed={len(changed)} removed_total={removed_total} elapsed_s={dt:.3f}",
        flush=True,
    )

    report_path = root / "artifacts" / "export" / "strip_comment_timestamps_report.json"
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_payload: Dict[str, object] = {
        "root": str(root),
        "include": include_dirs,
        "ext": exts,
        "dry_run": bool(args.dry_run),
        "scanned_files": int(scanned),
        "changed_files": int(len(changed)),
        "removed_lines_total": int(removed_total),
        "changes": [c.__dict__ for c in changed],
        "elapsed_s": float(dt),
        "generated_at_unix_s": float(time.time()),
    }
    report_path.write_text(json.dumps(report_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[strip_timestamps] report={report_path}", flush=True)


if __name__ == "__main__":
    main()

