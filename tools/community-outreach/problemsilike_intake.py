#!/usr/bin/env python3
"""Problems I Like source snapshot and board synchronizer.

Problems I Like is treated as a curated high-impact source. OPEN problems enter
the exploratory math lane without generic fit/topic/publishable-value filtering.
The downstream science and impact gates still decide proof closure,
verification strength, and writeback readiness.
"""

from __future__ import annotations

import argparse
import html
from html.parser import HTMLParser
import json
import re
import sys
import urllib.request
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"
TARGETS_DIR = SCRIPT_DIR / "targets"
STATE_DIR = SCRIPT_DIR / "outreach_state"
SNAPSHOT_DIR = STATE_DIR / "source_snapshots"
SOURCE_URL = "https://www.problemsilike.com/range/1-end"
BASE_URL = "https://www.problemsilike.com"

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_board_parser import parse_board  # noqa: E402
from outreach_profile import SCHEMA_VERSION, validate_profile_dict  # noqa: E402


@dataclass
class ProblemsILikeProblem:
    problem_id: int
    canonical_url: str
    title: str
    short_statement: str
    status: str
    last_edited_date: str = ""
    comments_count: int = 0
    comments_claim: str = "none"
    comments_claim_partial: bool = False
    comments_claim_complete: bool = False
    reactions: dict[str, str] = field(default_factory=dict)
    tags: list[str] = field(default_factory=list)
    resolution_text: str = ""
    source_excerpt: str = ""


class _ProblemHTMLParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.problems: list[dict] = []
        self._current: dict | None = None
        self._stack: list[dict] = []
        self._pending_reaction: str = ""
        self._capture_reaction_users = False
        self._capture_comment_count = False
        self._link_href: str = ""
        self._link_text: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        attr = {k: v or "" for k, v in attrs}
        cls = attr.get("class", "")
        ident = attr.get("id", "")
        if tag == "div" and cls == "problem-box":
            self._current = {
                "boxes": [],
                "tags": [],
                "reactions": {},
                "links": [],
                "comment_count_text": "",
            }
        if self._current is None:
            return
        if tag == "a":
            self._link_href = attr.get("href", "")
            self._link_text = []
        if tag == "br":
            self._append_text("\n")
        if tag == "div" and cls == "problem-text":
            self._stack.append({"kind": "problem_text", "id": ident, "parts": []})
        elif tag == "div" and cls == "problem-additional-text":
            self._stack.append({"kind": "additional", "id": ident, "parts": []})
        elif tag == "div" and cls == "citationbox":
            self._stack.append({"kind": "citation", "id": ident, "parts": []})
        elif tag == "span" and "problem-reaction-users" in cls:
            self._capture_reaction_users = True
            self._stack.append({"kind": "reaction_users", "label": self._pending_reaction, "parts": []})
        elif tag == "div" and "comment-count" in cls:
            self._capture_comment_count = True
            self._stack.append({"kind": "comment_count", "parts": []})

    def handle_endtag(self, tag: str) -> None:
        if self._current is None:
            return
        if tag == "a" and self._link_href:
            label = _clean(" ".join(self._link_text))
            self._current["links"].append((self._link_href, label))
            if self._stack:
                self._stack[-1]["parts"].append(label)
            self._link_href = ""
            self._link_text = []
            return
        if tag == "span" and self._capture_reaction_users:
            box = self._pop_kind("reaction_users")
            if box:
                label = str(box.get("label") or "").strip()
                if label:
                    self._current["reactions"][label] = _clean(" ".join(box["parts"])) or "None"
            self._capture_reaction_users = False
            return
        if tag == "div" and self._capture_comment_count:
            box = self._pop_kind("comment_count")
            if box:
                self._current["comment_count_text"] = _clean(" ".join(box["parts"]))
            self._capture_comment_count = False
            return
        if tag == "div" and self._stack and self._stack[-1]["kind"] in {"problem_text", "additional", "citation"}:
            box = self._stack.pop()
            self._current["boxes"].append(box)
            return
        if tag == "div" and self._current is not None:
            # HTMLParser does not expose nesting depth for arbitrary divs here;
            # problem-boxes in this site are flat enough that seeing a citation
            # box followed by closing problem-box is handled by problem id checks
            # during extraction.
            pass

    def handle_data(self, data: str) -> None:
        if self._current is None:
            return
        text = html.unescape(data)
        if self._link_href:
            self._link_text.append(text)
        self._append_text(text)
        stripped = _clean(text)
        if stripped in _REACTION_LABELS:
            self._pending_reaction = stripped

    def close_problem(self) -> None:
        if self._current is not None:
            self.problems.append(self._current)
            self._current = None
            self._stack = []
            self._pending_reaction = ""
            self._capture_reaction_users = False
            self._capture_comment_count = False

    def _append_text(self, text: str) -> None:
        if self._stack:
            self._stack[-1]["parts"].append(text)

    def _pop_kind(self, kind: str) -> dict | None:
        for i in range(len(self._stack) - 1, -1, -1):
            if self._stack[i].get("kind") == kind:
                return self._stack.pop(i)
        return None


_REACTION_LABELS = {
    "Likes this problem",
    "Interested in collaborating",
    "Currently working on this problem",
    "This problem looks difficult",
    "This problem looks tractable",
    "The results on this problem could be formalisable",
    "I am working on formalising the results on this problem",
}


def _clean(text: str) -> str:
    return " ".join(html.unescape(text or "").split())


def _html_to_text(raw: str) -> str:
    text = re.sub(r"(?i)<br\s*/?>", "\n", raw or "")
    text = re.sub(r"(?is)<script.*?</script>", " ", text)
    text = re.sub(r"(?is)<style.*?</style>", " ", text)
    text = re.sub(r"(?is)<[^>]+>", " ", text)
    return _clean(text)


def canonical_problemsilike_url(url: str) -> str:
    m = re.search(r"https?://(?:www\.)?problemsilike\.com/(?:go_to/)?(\d+)(?:[/?#].*)?$", str(url or ""), re.I)
    if not m:
        m = re.search(r"^/(\d+)(?:[/?#].*)?$", str(url or ""))
    if not m:
        return ""
    return f"{BASE_URL}/{int(m.group(1))}"


def _fetch(url: str) -> str:
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": "OmegaOutreach/0.1 ProblemsILike intake",
            "Accept": "text/html,text/plain;q=0.9,*/*;q=0.5",
        },
    )
    with urllib.request.urlopen(req, timeout=30) as resp:
        return resp.read().decode("utf-8", errors="replace")


def _problem_boxes(raw_html: str) -> list[dict]:
    chunks = re.split(r'(?=<div class="problem-box">)', raw_html)
    out: list[dict] = []
    for chunk in chunks:
        if 'class="problem-box"' not in chunk:
            continue
        out.append({"raw": chunk})
    return out


def _box_text(box: dict, kind: str = "", ident: str = "") -> str:
    parts: list[str] = []
    for rec in box.get("boxes") or []:
        if kind and rec.get("kind") != kind:
            continue
        if ident and rec.get("id") != ident:
            continue
        parts.append(_clean(" ".join(rec.get("parts") or [])))
    return "\n".join(p for p in parts if p)


def _tags(box: dict, problem_id: int) -> list[str]:
    tags: list[str] = []
    for href, label in box.get("links") or []:
        if str(href).startswith("/tags/") and label and label not in tags:
            tags.append(label)
    return tags


def _extract_problem(box: dict) -> ProblemsILikeProblem | None:
    if "raw" in box:
        return _extract_problem_from_raw(str(box.get("raw") or ""))
    main = _box_text(box, "problem_text", "open") or _box_text(box, "problem_text", "solved")
    if not main:
        return None
    m = re.search(r"\b(OPEN|SOLVED)\b\s+(.*?)\s+#(\d+)\b", main, re.I | re.DOTALL)
    if not m:
        return None
    status = m.group(1).upper()
    statement = _clean(m.group(2))
    problem_id = int(m.group(3))
    title = _title_from_statement(statement)

    all_text = "\n".join(
        _clean(" ".join(rec.get("parts") or []))
        for rec in box.get("boxes") or []
        if rec.get("kind") in {"additional", "problem_text", "citation"}
    )


def _extract_problem_from_raw(raw: str) -> ProblemsILikeProblem | None:
    main = re.search(
        r'<div class="problem-text" id="(open|solved)">\s*'
        r'.*?<div id="prize">\s*(OPEN|SOLVED)\s*</div>\s*'
        r'.*?<div id="content">(.*?)</div>\s*'
        r'<div id="problem_id">\s*<a href="/(\d+)">#\d+</a>(.*?)</div>',
        raw,
        re.I | re.S,
    )
    if not main:
        return None
    status = main.group(2).upper()
    statement = _html_to_text(main.group(3))
    problem_id = int(main.group(4))
    title = _title_from_statement(statement)

    tag_block = re.search(r'<div id="tags">(.*?)</div>', raw, re.I | re.S)
    tags: list[str] = []
    if tag_block:
        for label in re.findall(r'<a[^>]+href="/tags/[^"]+"[^>]*>(.*?)</a>', tag_block.group(1), re.I | re.S):
            clean = _html_to_text(label)
            if clean and clean not in tags:
                tags.append(clean)

    current_status = ""
    m_status = re.search(r'data-current-status="([^"]+)"', raw, re.I)
    if m_status:
        current_status = m_status.group(1).lower()
    comments_claim = {
        "open": "none",
        "partial": "partial_claimed",
        "claimed": "solution_claimed",
    }.get(current_status, "none")

    comments_count = 0
    m_comments = re.search(r'(\d+)\s+comments?\s+on\s+this\s+problem', raw, re.I)
    if m_comments:
        comments_count = int(m_comments.group(1))

    edited = ""
    m_edited = re.search(r'This page was last edited\s+([^.<]+?\d{4})\.', raw, re.I | re.S)
    if m_edited:
        edited = _clean(m_edited.group(1))

    reactions: dict[str, str] = {}
    for row in re.findall(r'<tr class="problem-reaction-row".*?</tr>', raw, re.I | re.S):
        m_label = re.search(r'<strong>(.*?)</strong>', row, re.I | re.S)
        m_users = re.search(r'<span class="problem-reaction-users">\s*(.*?)\s*</span>', row, re.I | re.S)
        if m_label:
            reactions[_html_to_text(m_label.group(1))] = _html_to_text(m_users.group(1) if m_users else "") or "None"

    additional = "\n".join(_html_to_text(m.group(1)) for m in re.finditer(r'<div class="problem-additional-text"[^>]*>(.*?)</div>', raw, re.I | re.S))
    disclaimer = _html_to_text(
        re.search(r'<div class="problem-text" id="disclaimer">(.*?)</div>', raw, re.I | re.S).group(1)
        if re.search(r'<div class="problem-text" id="disclaimer">(.*?)</div>', raw, re.I | re.S)
        else ""
    )
    source_excerpt = "\n".join(part for part in (statement, disclaimer, additional) if part)[:5000]
    resolution = _resolution_excerpt(additional) if status == "SOLVED" else ""
    return ProblemsILikeProblem(
        problem_id=problem_id,
        canonical_url=f"{BASE_URL}/{problem_id}",
        title=title,
        short_statement=statement,
        status=status,
        last_edited_date=edited,
        comments_count=comments_count,
        comments_claim=comments_claim,
        comments_claim_partial=comments_claim == "partial_claimed",
        comments_claim_complete=comments_claim == "solution_claimed",
        reactions=reactions,
        tags=tags,
        resolution_text=resolution,
        source_excerpt=source_excerpt,
    )
    edited = ""
    edit_m = re.search(r"This page was last edited\s+([^\.]+)\.", all_text)
    if edit_m:
        edited = _clean(edit_m.group(1))

    comment_text = str(box.get("comment_count_text") or "")
    c_m = re.search(r"(\d+)\s+comments?", comment_text)
    comments_count = int(c_m.group(1)) if c_m else 0

    status_widget_text = _box_text(box, "problem_text", "disclaimer")
    comments_claim = "none"
    if re.search(r"claimed solution", status_widget_text, re.I):
        comments_claim = "solution_claimed"
    elif re.search(r"claims of partial results|path to a solution", status_widget_text, re.I):
        comments_claim = "partial_claimed"
    if "There are no solutions, partial or complete, claimed in the comments." in status_widget_text:
        comments_claim = "none"

    resolution = ""
    if status == "SOLVED":
        add_text = "\n".join(
            _clean(" ".join(rec.get("parts") or []))
            for rec in box.get("boxes") or []
            if rec.get("kind") == "additional"
        )
        resolution = _resolution_excerpt(add_text)

    return ProblemsILikeProblem(
        problem_id=problem_id,
        canonical_url=f"{BASE_URL}/{problem_id}",
        title=title,
        short_statement=statement,
        status=status,
        last_edited_date=edited,
        comments_count=comments_count,
        comments_claim=comments_claim,
        comments_claim_partial=comments_claim == "partial_claimed",
        comments_claim_complete=comments_claim == "solution_claimed",
        reactions=dict(box.get("reactions") or {}),
        tags=_tags(box, problem_id),
        resolution_text=resolution,
        source_excerpt=all_text[:5000],
    )


def _title_from_statement(statement: str) -> str:
    text = _clean(re.sub(r"\$+", "", statement))
    if len(text) <= 86:
        return text
    cut = text[:86].rsplit(" ", 1)[0].rstrip(" ,;:")
    return cut + "..."


def _resolution_excerpt(text: str) -> str:
    if not text:
        return ""
    markers = ("Solution", "Resolved", "Counterexample", "General remarks")
    for marker in markers:
        i = text.lower().find(marker.lower())
        if i >= 0:
            return text[i:i + 900].strip()
    return text[:900].strip()


def build_snapshot() -> dict:
    index_html = _fetch(SOURCE_URL)
    index_items = []
    for box in _problem_boxes(index_html):
        problem = _extract_problem(box)
        if problem:
            index_items.append(problem)
    ids = sorted({p.problem_id for p in index_items})

    by_id: dict[int, ProblemsILikeProblem] = {}
    fetch_errors: dict[str, str] = {}
    for pid in ids:
        url = f"{BASE_URL}/{pid}"
        try:
            raw = _fetch(url)
            boxes = _problem_boxes(raw)
            parsed = [_extract_problem(box) for box in boxes]
            parsed = [p for p in parsed if p and p.problem_id == pid]
            by_id[pid] = parsed[0] if parsed else next(p for p in index_items if p.problem_id == pid)
        except Exception as exc:  # noqa: BLE001
            fetch_errors[str(pid)] = str(exc)
            by_id[pid] = next(p for p in index_items if p.problem_id == pid)

    problems = [by_id[pid] for pid in ids]
    return {
        "source": SOURCE_URL,
        "fetched_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "problem_count": len(problems),
        "open_count": sum(1 for p in problems if p.status == "OPEN"),
        "solved_count": sum(1 for p in problems if p.status == "SOLVED"),
        "fetch_errors": fetch_errors,
        "problems": [asdict(p) for p in problems],
    }


def write_snapshot(snapshot: dict) -> Path:
    SNAPSHOT_DIR.mkdir(parents=True, exist_ok=True)
    latest = SNAPSHOT_DIR / "problemsilike_latest.json"
    latest.write_text(json.dumps(snapshot, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    tag = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    dated = SNAPSHOT_DIR / f"problemsilike_{tag}.json"
    dated.write_text(json.dumps(snapshot, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return latest


def _existing_by_canonical() -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for todo in parse_board(BOARD_PATH).values():
        canon = canonical_problemsilike_url(todo.source)
        if canon:
            out.setdefault(canon, []).append(todo.todo_id)
    return out


def _next_todo_id() -> str:
    nums: list[int] = []
    for tid in parse_board(BOARD_PATH):
        m = re.match(r"^T-(\d+)$", tid)
        if m:
            nums.append(int(m.group(1)))
    return f"T-{(max(nums) + 1) if nums else 1:02d}"


def _slug(problem: dict) -> str:
    return f"problemsilike_{int(problem['problem_id']):02d}"


def _problem_title(problem: dict) -> str:
    return f"Problems I Like #{problem['problem_id']} · {problem['title']}"


def _candidate_block(todo_id: str, problem: dict) -> str:
    slug = _slug(problem)
    status = "Backlog (Problems I Like curated OPEN intake)"
    if int(problem["problem_id"]) == 6:
        status = "SOLVED_EXTERNAL (Problems I Like original statement solved; derivative-only)"
    source_status = problem.get("status") or "OPEN"
    title = _problem_title(problem)
    final_display = (
        "Internal math-lane research memo first; after progress, decide among Problems I Like comment, "
        "author email, Automath writeback, paper/short note, X thread, or internal close."
    )
    success_gate = (
        "No outreach/writeback unless Codex local replay verifies a proof, counterexample, reproducible "
        "computation, or valuable obstruction memo. Operator approval is required before any external action."
    )
    if int(problem["problem_id"]) == 6:
        final_display = (
            "Derivative verification/formalization target only: verify the published counterexample or "
            "study the stronger remaining variant p > rk(E), never the solved original statement."
        )
        success_gate = (
            "Before any writeback, verify actual source bytes for the published counterexample or produce "
            "a complete proof/obstruction for the stronger p > rk(E) variant; do not claim the original "
            "Problems I Like #6 statement as new work."
        )
    tags = ", ".join(problem.get("tags") or []) or "(none visible)"
    untouched = (
        f"Problems I Like source status={source_status}; last edited {problem.get('last_edited_date') or 'not visible'}; "
        f"{problem.get('comments_count', 0)} comments; comment claim status={problem.get('comments_claim') or 'none'}; "
        f"tags={tags}. Impact assumed high enough for exploratory math-lane entry by operator policy."
    )
    return "\n".join([
        f"### {todo_id} · {title}",
        "",
        "| field | value |",
        "|---|---|",
        f"| Status | {status} |",
        f"| Source | {problem['canonical_url']} |",
        "| Type | open problem |" if source_status == "OPEN" else "| Type | solved_external |",
        f"| Untouched | {untouched} |",
        "| Omega fit | 0/10 (curated-source entry; generic fit score is not a blocker) |",
        "| Topic value | 10/10 (Problems I Like curated source; generic topic score is not a blocker) |",
        "| Effort est | 7-21 天 for first harness cycle; longer only if progress justifies it |",
        "| Risk | high |",
        f"| Final display | {final_display} |",
        f"| Success gate | {success_gate} |",
        "",
        f"**Statement.** {problem['short_statement']}",
        "",
        f"**Prior.** Local source snapshot records canonical URL {problem['canonical_url']}, status {source_status}, last edited {problem.get('last_edited_date') or 'not visible'}, comments={problem.get('comments_count', 0)}, comments_claim={problem.get('comments_claim') or 'none'}, and visible reaction metadata {json.dumps(problem.get('reactions') or {}, ensure_ascii=False)}. This is source metadata, not mathematical progress; each run must still do local literature/source verification before any writeback.",
        "",
        "**Omega fit detail.** Generic Automath/Omega fit does not gate this source. The first harness cycle should convert the curated open problem into an auditable local proof/counterexample/search profile, separating source facts from mathematical evidence and keeping all outreach blocked until science_gate=WRITEBACK_READY.",
        "",
        "**Attack plan.**",
        "1. Re-read the canonical problem page and freeze the exact statement, status metadata, tags, comments-claim status, visible interest/working metadata, and cited context.",
        "2. Perform Codex local source/profile workup: identify the first concrete theorem, counterexample, computation, or obstruction route and write a grounded next_oracle_question.",
        "3. Send Oracle a continuation/deep-reasoning prompt only after local workup; after Oracle returns, replay/check locally and update research.md, results.json, and next_oracle_question without public outreach.",
        "",
        "**Deliverables.**",
        f"- tools/community-outreach/targets/{slug}/research.md",
        f"- tools/community-outreach/targets/{slug}/results.json",
        f"- tools/community-outreach/targets/{slug}/next_oracle_question.md",
        f"- tools/community-outreach/targets/{slug}/submission_draft.md",
        "",
        "_Problems I Like intake rationale_: Curated-source policy admits OPEN entries into exploratory math lane without generic fit/topic/publishable-value filtering. Science and impact gates remain strict; source metadata is not a result.",
        "",
        "---",
        "",
    ])


def _profile(problem: dict, todo_id: str) -> dict:
    slug = _slug(problem)
    title = _problem_title(problem)
    solved = problem.get("status") == "SOLVED" or int(problem["problem_id"]) == 6
    contribution = "source_audit_note" if solved else "research_note"
    close_when = [
        "Focused local/Oracle cycle finds the problem is already solved or substantially subsumed in the literature.",
        "After no-progress patience, only source summary/speculation exists and no valuable obstruction memo has emerged.",
    ]
    if solved:
        close_when.insert(0, "The derivative verification/formalization lane cannot be separated from re-solving the solved original statement.")
    profile = {
        "schema_version": SCHEMA_VERSION,
        "todo_id": todo_id,
        "slug": slug,
        "title": title,
        "source_url": problem["canonical_url"],
        "profile_status": "ready",
        "final_display_form": "After verified progress only: Problems I Like comment, author email, Automath writeback, paper/short note, X thread, or internal close.",
        "success_gate": "No external action unless a proof, counterexample, verified computation, or valuable obstruction memo is complete and operator-approved.",
        "no_external_send_without_operator_approval": True,
        "canonical_draft_paths": [
            f"tools/community-outreach/targets/{slug}/research.md",
            f"tools/community-outreach/targets/{slug}/submission_draft.md",
        ],
        "expected_artifacts": [
            f"tools/community-outreach/targets/{slug}/research.md",
            f"tools/community-outreach/targets/{slug}/results.json",
            f"tools/community-outreach/targets/{slug}/next_oracle_question.md",
        ],
        "first_experiments": [
            {
                "label": "curated_source_local_workup",
                "command": [],
                "expected_outputs": [
                    f"tools/community-outreach/targets/{slug}/research.md",
                    f"tools/community-outreach/targets/{slug}/results.json",
                    f"tools/community-outreach/targets/{slug}/next_oracle_question.md",
                ],
                "success_predicate": "research.md distinguishes source metadata from mathematical evidence; results.json records status/progress fields; next_oracle_question.md asks a grounded mathematical question based on local source/profile workup.",
                "timeout_s": 1800,
            }
        ],
        "fallback_contribution": "A fallback is acceptable only if it is a valuable obstruction or source/literature audit memo with reusable mathematical content; otherwise keep internal and close.",
        "science_contract": {
            "contribution_type": contribution,
            "target_lane": "math_lane",
            "contract_quality_floor": 8,
            "origin": "operator",
            "closure_status": "seed",
            "verification_status": "unverified",
            "outreach_status": "not_drafted",
            "terminal_artifact": f"tools/community-outreach/targets/{slug}/research.md",
            "verifier": "A writeback-ready result requires a complete proof, explicit counterexample, independently reproducible computation, or valuable obstruction memo. Source metadata, comments, and Oracle prose are not accepted as mathematical evidence until Codex locally replays/checks them and records actual artifacts.",
            "progress_metric": "Completion of source-status verification, number of concrete proof/counterexample/computation routes locally tested, number of Oracle claims locally replayed, and whether a verified proof/counterexample/computation/obstruction memo exists.",
            "taste_obligations": {
                "novelty_witness": f"Use the local Problems I Like snapshot for #{problem['problem_id']} plus a dated literature/source check; do not treat the curated source as proof that no later solution exists.",
                "no_hidden_assumption_witness": "Every run must separate the source statement, visible comments/reactions metadata, cited literature, Oracle suggestions, and locally checked mathematical claims.",
                "reproducibility_witness": "research.md and results.json must record exact local files, commands or proof obligations, and actual bytes checked before trusting claims of artifacts or solutions.",
                "layer_separation_witness": "Problems I Like intake grants exploratory entry only; science_gate controls result readiness and impact_gate controls final channel after progress with operator approval.",
            },
            "evidence_required": [
                "Dated source snapshot metadata for the problem page and local re-read of the canonical URL.",
                "Codex local replay/check of any Oracle proof, counterexample, computation, or obstruction claim before writeback.",
            ],
            "writeback_when": [
                "A proof, counterexample, verified computation, or valuable obstruction memo is complete and locally checked.",
                "The impact gate has selected the final channel and the operator has approved exact text.",
            ],
            "close_when": close_when,
            "no_progress_patience_turns": 2,
        },
        "main_paper_bridge": {
            "required_before_run": False,
            "section_hint": "",
            "omega_modules": [],
            "backflow_surface": "decide after verified progress",
        },
        "oracle_judge_required": True,
        "freshness_required": True,
        "notes": "Problems I Like curated-source target. Generic fit/topic scores must not block OPEN exploratory entry; no external outreach before science/impact/operator gates.",
    }
    if solved:
        profile["profile_status"] = "ready"
        profile["notes"] += " Original statement is solved_external; only derivative verification/formalization or stronger variant work is allowed."
    errors = validate_profile_dict(profile)
    if errors:
        raise ValueError(f"profile for problem #{problem['problem_id']} failed validation: {errors}")
    return profile


def _replace_status(text: str, todo_id: str, new_status: str) -> tuple[str, bool]:
    header = re.search(rf"^### {re.escape(todo_id)}\s*[··]\s*.*$", text, re.MULTILINE)
    if not header:
        return text, False
    next_header = re.search(r"^### T-\d+\s*[··]\s*.*$", text[header.end():], re.MULTILINE)
    end = header.end() + next_header.start() if next_header else len(text)
    block = text[header.start():end]
    new_block, n = re.subn(
        r"^\|\s*Status\s*\|\s*.*?\s*\|$",
        f"| Status | {new_status} |",
        block,
        count=1,
        flags=re.MULTILINE,
    )
    if n != 1:
        return text, False
    return text[:header.start()] + new_block + text[end:], True


def sync_board(snapshot: dict, *, dry_run: bool = False) -> dict:
    text = BOARD_PATH.read_text(encoding="utf-8")
    existing = _existing_by_canonical()
    actions: list[dict] = []

    # Deduplicate by canonical Problems I Like problem URL.
    for canonical, todo_ids in sorted(existing.items()):
        if len(todo_ids) <= 1:
            continue
        keep = todo_ids[0]
        for tid in todo_ids[1:]:
            new_status = f"OPERATOR_DEPRIORITIZED · duplicate of {keep} by canonical Problems I Like URL {canonical}"
            text, changed = _replace_status(text, tid, new_status)
            actions.append({"action": "dedup_mark", "todo_id": tid, "kept": keep, "canonical_url": canonical, "changed": changed})

    next_id = _next_todo_id()
    next_num = int(next_id.split("-")[1])
    active_problem_ids: list[int] = []
    for problem in snapshot.get("problems") or []:
        pid = int(problem.get("problem_id") or 0)
        canonical = problem["canonical_url"]
        source_status = problem.get("status")
        if pid == 6:
            # Mark existing original as solved_external if present. A derivative
            # target can be added separately only if explicitly scoped.
            existing_ids = existing.get(canonical, [])
            for tid in existing_ids:
                text, changed = _replace_status(
                    text,
                    tid,
                    "SOLVED_EXTERNAL · original Problems I Like #6 is solved; derivative verification/stronger-variant only",
                )
                actions.append({"action": "mark_solved_external", "todo_id": tid, "canonical_url": canonical, "changed": changed})
            if not existing_ids:
                todo_id = f"T-{next_num:02d}"
                next_num += 1
                block = _candidate_block(todo_id, problem)
                text = text.rstrip() + "\n\n" + block
                actions.append({
                    "action": "append_solved_external_marker",
                    "problem_id": pid,
                    "todo_id": todo_id,
                    "canonical_url": canonical,
                })
            continue
        if source_status != "OPEN":
            continue
        active_problem_ids.append(pid)
        if existing.get(canonical):
            actions.append({"action": "exists", "problem_id": pid, "canonical_url": canonical, "todo_ids": existing[canonical]})
            for tid in existing[canonical][:1]:
                todo = parse_board(BOARD_PATH).get(tid)
                if not todo:
                    continue
                profile_path = TARGETS_DIR / todo.slug() / "profile.json"
                profile = _profile(problem, tid)
                profile["slug"] = todo.slug()
                profile["title"] = todo.title
                profile["canonical_draft_paths"] = [
                    f"tools/community-outreach/targets/{todo.slug()}/research.md",
                    f"tools/community-outreach/targets/{todo.slug()}/submission_draft.md",
                ]
                profile["expected_artifacts"] = [
                    f"tools/community-outreach/targets/{todo.slug()}/research.md",
                    f"tools/community-outreach/targets/{todo.slug()}/results.json",
                    f"tools/community-outreach/targets/{todo.slug()}/next_oracle_question.md",
                ]
                for exp in profile.get("first_experiments") or []:
                    if isinstance(exp, dict):
                        exp["expected_outputs"] = [
                            f"tools/community-outreach/targets/{todo.slug()}/research.md",
                            f"tools/community-outreach/targets/{todo.slug()}/results.json",
                            f"tools/community-outreach/targets/{todo.slug()}/next_oracle_question.md",
                        ]
                if isinstance(profile.get("science_contract"), dict):
                    profile["science_contract"]["terminal_artifact"] = f"tools/community-outreach/targets/{todo.slug()}/research.md"
                errors = validate_profile_dict(profile)
                if errors:
                    raise ValueError(f"refreshed profile for {tid} failed validation: {errors}")
                actions.append({"action": "refresh_existing_profile", "todo_id": tid, "path": str(profile_path.relative_to(SCRIPT_DIR))})
                if not dry_run:
                    profile_path.parent.mkdir(parents=True, exist_ok=True)
                    profile_path.write_text(json.dumps(profile, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
            continue
        todo_id = f"T-{next_num:02d}"
        next_num += 1
        block = _candidate_block(todo_id, problem)
        text = text.rstrip() + "\n\n" + block
        profile = _profile(problem, todo_id)
        profile_path = TARGETS_DIR / profile["slug"] / "profile.json"
        actions.append({
            "action": "append_open_problem",
            "problem_id": pid,
            "todo_id": todo_id,
            "slug": profile["slug"],
            "canonical_url": canonical,
            "profile_path": str(profile_path.relative_to(SCRIPT_DIR)),
        })
        if not dry_run:
            profile_path.parent.mkdir(parents=True, exist_ok=True)
            profile_path.write_text(json.dumps(profile, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    if not dry_run:
        tmp = BOARD_PATH.with_suffix(".md.tmp")
        tmp.write_text(text.rstrip() + "\n", encoding="utf-8")
        tmp.replace(BOARD_PATH)
    return {
        "active_open_problem_ids": active_problem_ids,
        "actions": actions,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--snapshot-only", action="store_true", help="fetch and write snapshot, do not sync board")
    parser.add_argument("--sync-board", action="store_true", help="append missing OPEN targets and mark duplicates")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args(argv)

    snapshot = build_snapshot()
    path = write_snapshot(snapshot)
    result = {
        "snapshot_path": str(path.relative_to(SCRIPT_DIR)),
        "problem_count": snapshot["problem_count"],
        "open_count": snapshot["open_count"],
        "solved_count": snapshot["solved_count"],
    }
    if args.sync_board and not args.snapshot_only:
        result["sync"] = sync_board(snapshot, dry_run=args.dry_run)
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
