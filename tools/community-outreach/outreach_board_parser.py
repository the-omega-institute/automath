#!/usr/bin/env python3
"""outreach_board_parser — zero-dependency parser for RESEARCH_BOARD.md.

Extracted from dispatch_worktree.py to break the cross-import chain that
made arxiv_watch / lit_staleness / oracle_consultant / resume_deep /
outreach_research_loop fail to start whenever dispatch_worktree.py had any
import-time bug. This module imports only stdlib.

Public API:
    BOARD_PATH_DEFAULT        : Path to RESEARCH_BOARD.md (resolved at import)
    TARGET_SLUG_OVERRIDES     : compatibility map for pre-existing target dirs
    TodoSpec                  : dataclass for one ### T-NN block
    parse_board(path)         : -> dict[str, TodoSpec]

Slug rules and TodoSpec field semantics MUST stay byte-equivalent to the
dispatch_worktree definitions they replaced — every consumer was written
against the older definitions.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT_DEFAULT = Path(__file__).resolve().parents[2]
BOARD_PATH_DEFAULT = REPO_ROOT_DEFAULT / "tools/community-outreach/RESEARCH_BOARD.md"

# Compatibility aliases for targets that were already researched before the
# generic board slugger existed. Keep these stable so reruns reuse the existing
# ignored target directories rather than silently forking evidence.
TARGET_SLUG_OVERRIDES = {
    "T-08": "opg_lucas_mod_m",
}


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------


@dataclass
class TodoSpec:
    todo_id: str
    title: str
    status: str
    source: str
    type_: str
    untouched: str
    fit_score: int | None
    topic_score: int | None
    effort: str
    risk: str
    final_display: str
    success_gate: str
    statement: str
    prior: str
    omega_fit_detail: str
    attack_plan: list[str]
    worktree_inputs: list[str]
    deliverables: list[str]
    raw_block: str

    def slug(self) -> str:
        # 0. TARGET_SLUG_OVERRIDES wins (compatibility with pre-existing target dirs)
        if self.todo_id in TARGET_SLUG_OVERRIDES:
            return TARGET_SLUG_OVERRIDES[self.todo_id]
        # 1. Explicit override in table
        # 2. targets/<slug>/ in deliverables
        for d in self.deliverables:
            m = re.search(r"targets/([a-z0-9_]+)/", d.lower())
            if m:
                return m.group(1)
        # 3. Erdős #N pattern in title → erdos_N
        m = re.search(r"Erd[őo]?s\s*#?(\d+)", self.title)
        if m:
            return f"erdos_{m.group(1)}"
        # 4. arxiv ID in source or title (strip vN suffix). Try URL then inline.
        haystack = self.source + " " + self.title
        m = re.search(r"arxiv\.org/abs/(\d{4}\.\d{4,6})", haystack, re.IGNORECASE)
        if not m:
            m = re.search(r"arxiv:(\d{4}\.\d{4,6})", haystack, re.IGNORECASE)
        if m:
            return "arxiv_" + m.group(1).replace(".", "_")
        # 5. AimPL workshop → aimpl_<name>
        m = re.search(r"aimpl\.org/([a-z0-9]+)/(\d+)", self.source)
        if m:
            return f"aimpl_{m.group(1)}_{m.group(2)}"
        m = re.search(r"aimpl\.org/([a-z0-9]+)", self.source)
        if m:
            return f"aimpl_{m.group(1)}"
        # 6. OPG → opg_<name>
        m = re.search(r"openproblemgarden\.org/op/([a-z0-9_]+)", self.source)
        if m:
            return f"opg_{m.group(1)[:24]}"
        # 7. Tao blog → tao_<first-2-words>
        m = re.search(r"terrytao\.wordpress\.com/[\d/]+/([a-z0-9-]+)", self.source)
        if m:
            parts = [p for p in m.group(1).split("-") if p][:2]
            return "tao_" + "_".join(parts) if parts else "tao_post"
        # 8. erdosproblems.com/N → erdos_N
        m = re.search(r"erdosproblems\.com/(\d+)", self.source)
        if m:
            return f"erdos_{m.group(1)}"
        # 9. Fallback: title first 2-3 alphabetic words, max 32
        words = [w.lower() for w in re.findall(r"[A-Za-z]{3,}", self.title)][:3]
        base = "_".join(words)[:32]
        return base or self.todo_id.replace("-", "_").lower()

    def expanded_deliverables(self) -> list[str]:
        """Resolve '同模板' shorthand into concrete paths based on slug."""
        if not self.deliverables or any("同模板" in d for d in self.deliverables):
            slug = self.slug()
            area = slug.split("_", 1)[0]  # erdos, arxiv, tao, aimpl, opg
            return [
                f"tools/community-outreach/targets/{slug}/research.md",
                f"tools/community-outreach/{area}/{slug}_*.py",
                f"tools/community-outreach/targets/{slug}/submission_draft.md",
                f"theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/appendix/{slug}/main.tex",
            ]
        return list(self.deliverables)

    def submission_target(self) -> dict[str, str]:
        s = self.source
        if "erdosproblems.com/forum" in s:
            return {"type": "forum_post", "venue": "erdosproblems.com forum", "format": "markdown"}
        if "erdosproblems.com/" in s:
            return {"type": "forum_comment", "venue": "erdosproblems.com problem page", "format": "markdown"}
        if "github.com/teorth/erdosproblems" in s:
            return {"type": "github_pr", "venue": "teorth/erdosproblems data/problems.yaml", "format": "yaml_diff"}
        if "arxiv.org" in s:
            return {"type": "arxiv_followup", "venue": "arXiv preprint or author email", "format": "tex_or_email"}
        if "terrytao.wordpress.com" in s:
            return {"type": "blog_comment", "venue": "Tao blog comment", "format": "markdown"}
        if "aimpl.org" in s:
            return {"type": "email_authors", "venue": "AimPL workshop email", "format": "markdown_or_pdf"}
        if "openproblemgarden.org" in s:
            return {"type": "comment_or_email", "venue": "OPG comment + author email", "format": "markdown"}
        return {"type": "unknown", "venue": s, "format": "markdown"}


# ---------------------------------------------------------------------------
# Regex constants and helpers (private)
# ---------------------------------------------------------------------------


_TODO_HEADER = re.compile(r"^### (T-\d+)\s*[··]\s*(.+)$", re.MULTILINE)
_TABLE_ROW = re.compile(r"^\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*$", re.MULTILINE)
_SCORE = re.compile(r"(\d+)\s*/\s*10")


def _split_blocks(text: str) -> list[tuple[str, str, str]]:
    """Split board text into (todo_id, title, body) per TODO."""
    matches = list(_TODO_HEADER.finditer(text))
    blocks = []
    for i, m in enumerate(matches):
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        body = text[start:end]
        blocks.append((m.group(1), m.group(2).strip(), body))
    return blocks


def _extract_table(body: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for m in _TABLE_ROW.finditer(body):
        k = m.group(1).strip().lower()
        v = m.group(2).strip()
        if k in {"field", "---"} or v in {"value", "---"}:
            continue
        fields[k] = v
    return fields


def _extract_section(body: str, label: str) -> str:
    """Extract a labelled paragraph or list. label is e.g. 'Statement', 'Prior'."""
    pattern = re.compile(
        r"\*\*" + re.escape(label) + r"\.?\*\*\s*\n?(.*?)(?=\n\*\*[A-Z]|\n---|\Z)",
        re.DOTALL,
    )
    m = pattern.search(body)
    return m.group(1).strip() if m else ""


def _extract_numbered_steps(body: str, label: str) -> list[str]:
    sect = _extract_section(body, label)
    steps: list[str] = []
    for line in sect.splitlines():
        line = line.strip()
        m = re.match(r"^\d+\.\s*(.+)$", line)
        if m:
            steps.append(m.group(1).strip())
    return steps


def _extract_bullets(body: str, label: str) -> list[str]:
    sect = _extract_section(body, label)
    bullets: list[str] = []
    for line in sect.splitlines():
        line = line.strip()
        m = re.match(r"^[-*]\s*(.+)$", line)
        if m:
            bullets.append(m.group(1).strip())
    if not bullets and sect:
        # Fallback: comma / period split for inline lists
        for chunk in re.split(r"[,;]\s*", sect):
            chunk = chunk.strip().strip("`").strip()
            if chunk:
                bullets.append(chunk)
    return bullets


def _score_from_field(text: str) -> int | None:
    m = _SCORE.search(text or "")
    return int(m.group(1)) if m else None


# ---------------------------------------------------------------------------
# Public parser
# ---------------------------------------------------------------------------


def parse_board(path: Path) -> dict[str, TodoSpec]:
    text = Path(path).read_text(encoding="utf-8")
    todos: dict[str, TodoSpec] = {}
    for todo_id, title, body in _split_blocks(text):
        table = _extract_table(body)
        spec = TodoSpec(
            todo_id=todo_id,
            title=title,
            status=table.get("status", ""),
            source=table.get("source", ""),
            type_=table.get("type", ""),
            untouched=table.get("untouched", ""),
            fit_score=_score_from_field(table.get("omega fit", "")),
            topic_score=_score_from_field(table.get("topic value", "")),
            effort=table.get("effort est", ""),
            risk=table.get("risk", ""),
            final_display=table.get("final display", ""),
            success_gate=table.get("success gate", ""),
            statement=_extract_section(body, "Statement"),
            prior=_extract_section(body, "Prior"),
            omega_fit_detail=_extract_section(body, "Omega fit detail"),
            attack_plan=_extract_numbered_steps(body, "Attack plan"),
            worktree_inputs=_extract_bullets(body, "Worktree-ready inputs"),
            deliverables=_extract_bullets(body, "Deliverables"),
            raw_block=body.strip(),
        )
        todos[todo_id] = spec
    return todos
