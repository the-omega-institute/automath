#!/usr/bin/env python3
"""Regenerate MAIN_PAPER_INDEX.md from theory/.../main.tex.

Walks `\subfile`/`\input`/`\include` recursively, extracts top-level
\section / \subsection headers only (skips theorem-like envs and
subsubsections by design — keep the index small enough for ChatGPT
Project context), groups by top-level subdirectory, and emits a
~50-100 KB markdown TOC suitable for the Omega Outreach ChatGPT Project.

Output: tools/community-outreach/chatgpt_project_upload/MAIN_PAPER_INDEX.md

Usage:
  python3 tools/community-outreach/scripts/build_main_paper_index.py
"""

from __future__ import annotations

import re
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
PAPER_ROOT = REPO_ROOT / "theory" / "2026_golden_ratio_driven_scan_projection_generation_recursive_emergence"
MAIN_TEX = PAPER_ROOT / "main.tex"
OUT_PATH = REPO_ROOT / "tools" / "community-outreach" / "chatgpt_project_upload" / "MAIN_PAPER_INDEX.md"

INCLUDE_RE = re.compile(r"\\(?:input|include|subfile)\{([^}]+)\}")
SECTION_RE = re.compile(r"\\(section|subsection)\*?\{([^}]+)\}")
COMMENT_RE = re.compile(r"(?<!\\)%[^\n]*")


def _resolve(p: Path) -> Path:
    return p if p.suffix else p.with_suffix(".tex")


def walk(path: Path, depth: int = 0, seen: set | None = None,
         out: list | None = None) -> list[tuple[str, str, str]]:
    if seen is None:
        seen, out = set(), []
    if depth > 12:
        return out
    p = _resolve(path)
    if not p.exists():
        return out
    rel = str(p.relative_to(PAPER_ROOT))
    if rel in seen:
        return out
    seen.add(rel)
    text = COMMENT_RE.sub("", p.read_text(encoding="utf-8", errors="ignore"))
    for m in SECTION_RE.finditer(text):
        out.append((rel, m.group(1), m.group(2).strip()))
    for m in INCLUDE_RE.finditer(text):
        sub = m.group(1).strip()
        cand = (p.parent / sub) if not sub.startswith("/") else Path(sub)
        if not _resolve(cand).exists():
            cand = PAPER_ROOT / sub
        walk(cand, depth + 1, seen, out)
    return out


def main() -> int:
    entries = walk(MAIN_TEX)
    groups: dict[str, list[tuple[str, str, str]]] = defaultdict(list)
    for rel, kind, title in entries:
        parts = rel.split("/")
        top = "/".join(parts[:3]) if len(parts) >= 3 else parts[0]
        groups[top].append((rel, kind, title))

    lines = [
        "# Main paper TOC — golden-ratio driven scan-projection",
        "",
        "**Source**: `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/main.tex` (11,260 pages)",
        "**Scope**: top-level section + subsection structure only.",
        "For specific theorems / lemmas / definitions: read the attached `main.pdf` directly.",
        "",
        f"**Total sections+subsections**: {len(entries)}",
        "",
    ]
    for top in sorted(groups):
        items = groups[top]
        lines.append(f"## `{top}/` ({len(items)})")
        for rel, kind, title in items:
            mark = "§" if kind == "section" else "    §§"
            lines.append(f"- {mark} {title}")
        lines.append("")

    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"wrote {OUT_PATH.relative_to(REPO_ROOT)} "
          f"({OUT_PATH.stat().st_size / 1024:.1f} KB, "
          f"{len(entries)} sections)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
