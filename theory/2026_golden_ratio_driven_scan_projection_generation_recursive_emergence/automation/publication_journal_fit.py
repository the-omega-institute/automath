#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Journal-fit automation for external publication workspaces."""

from __future__ import annotations

import argparse
import json
import os
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from automation_paths import export_dir
import journal_recon
import publication_sync


WORD_RE = re.compile(r"[A-Za-z][A-Za-z0-9'-]*")
TITLE_RE = re.compile(r"\\title(?:\[[^\]]*\])?\{(.*?)\}", re.DOTALL)
ABSTRACT_RE = re.compile(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", re.DOTALL)
SECTION_RE = re.compile(r"(?m)^\\section(?:\[[^\]]*\])?\{")
SUBSECTION_RE = re.compile(r"(?m)^\\subsection(?:\[[^\]]*\])?\{")
THEOREM_ENV_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition|conjecture|remark)\}(?:\[[^\]]*\])?",
    re.DOTALL,
)
CITE_RE = re.compile(r"\\cite[a-zA-Z*]*\s*(?:\[[^\]]*\]){0,2}\{([^}]+)\}")
INPUT_RE = re.compile(r"\\(?:input|include)\{([^}]+)\}")
BIBLIOGRAPHY_RE = re.compile(r"\\bibliography\{([^}]+)\}")
BIBSTYLE_RE = re.compile(r"\\bibliographystyle\{([^}]+)\}")
ENTRY_START_RE = re.compile(r"@([A-Za-z]+)\s*\{\s*([^,]+),", re.MULTILINE)
FIELD_VALUE_RE = r'(?is)\b{field}\s*=\s*(".*?"|\{{.*?\}}|[^,\n]+)'
NORMALIZE_RE = re.compile(r"[^A-Za-z0-9]+")

REQUIRED_ROOT_FILES = (
    "journal_fit_manifest.json",
    "journal_fit_records.json",
    "journal_fit_report.md",
)
REQUIRED_TRACK_FILES = (
    "journal_fit_profile.json",
    "journal_fit_report.md",
    "revision_prompt.md",
    "JOURNAL_FIT.template.md",
    "BIB_SCOPE.template.md",
    "SOURCE_MAP.template.md",
    "THEOREM_LIST.template.md",
    "WORKBOARD.md",
    "01_research_extension.md",
    "02_journal_style_rewrite.md",
    "03_editorial_review.md",
    "04_full_improvement.md",
    "JOURNAL_PROFILE.md",
)
ACTIVE_STATUSES = {"submitted", "planned_batch_1", "planned_batch_2", "planned_batch_3"}
JOURNAL_HINTS: tuple[dict[str, Any], ...] = (
    {
        "aliases": ("ergodic theory and dynamical systems", "etds"),
        "canonical": "Ergodic Theory and Dynamical Systems",
        "short": "ETDS",
        "publisher": "Cambridge University Press",
        "homepage": "https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/information/about-this-journal",
        "guidance": [
            "Keep the introduction mathematically direct and problem-led.",
            "Reserve appendices for genuinely peripheral technical material.",
            "Frame results as self-contained dynamical statements, not as manifesto language.",
        ],
    },
    {
        "aliases": ("annals of pure and applied logic", "apal"),
        "canonical": "Annals of Pure and Applied Logic",
        "short": "APAL",
        "publisher": "Elsevier",
        "homepage": "https://www.sciencedirect.com/journal/annals-of-pure-and-applied-logic",
        "guide": "https://www.sciencedirect.com/journal/annals-of-pure-and-applied-logic/publish/guide-for-authors",
        "guidance": [
            "State the semantic question early and keep the theorem chain tightly focused on that question.",
            "Use precise logical vocabulary and avoid rhetoric without theorem-level payoff.",
            "Move lengthy side constructions out of the main line unless they are needed for the principal result.",
        ],
    },
    {
        "aliases": ("journal of functional analysis", "jfa"),
        "canonical": "Journal of Functional Analysis",
        "short": "JFA",
        "publisher": "Elsevier",
        "homepage": "https://www.sciencedirect.com/journal/journal-of-functional-analysis",
        "guide": "https://www.sciencedirect.com/journal/journal-of-functional-analysis/publish/guide-for-authors",
        "guidance": [
            "Lead with the functional-analytic object and the core structural theorem.",
            "Keep examples subordinate to the main analytic argument.",
            "Prefer compact exposition in the main body over appendix-heavy packaging.",
        ],
    },
    {
        "aliases": ("transactions of the american mathematical society", "trans. amer. math. soc.", "tams"),
        "canonical": "Transactions of the American Mathematical Society",
        "short": "TAMS",
        "publisher": "American Mathematical Society",
        "homepage": "https://www.ams.org/publications/journals/journalsframework/abouttran",
        "guide": "https://www.ams.org/publications/journals/journalsframework/transubmit",
        "guidance": [
            "Sustain a long-form theorem-development arc with minimal exposition waste.",
            "Justify why the central theorem package is of independent mathematical interest.",
            "Appendices should remain auxiliary; core arguments belong in the main text.",
        ],
    },
    {
        "aliases": ("journal of algebra",),
        "canonical": "Journal of Algebra",
        "short": "JAlgebra",
        "publisher": "Elsevier",
        "homepage": "https://www.sciencedirect.com/journal/journal-of-algebra",
        "guide": "https://www.sciencedirect.com/journal/journal-of-algebra/publish/guide-for-authors",
        "guidance": [
            "State algebraic objects and structural consequences with minimal surrounding narrative.",
            "Prefer theorem-proof cadence over broad motivational exposition.",
            "Retain only examples that clarify structure theorems or obstructions.",
        ],
    },
    {
        "aliases": ("journal of philosophical logic", "j. philos. logic"),
        "canonical": "Journal of Philosophical Logic",
        "short": "JPL",
        "publisher": "Springer",
        "homepage": "https://link.springer.com/journal/10992",
        "guidance": [
            "Keep philosophical motivation subordinate to formal distinctions and exact results.",
            "Define the semantic framework crisply before discussing interpretive consequences.",
            "Use examples selectively and only when they sharpen the formal claim.",
        ],
    },
)


@dataclass
class BibEntry:
    key: str
    entry_type: str
    title: str
    journal: str
    doi: str
    year: str


@dataclass
class JournalFitRecord:
    directory: str
    status: str
    target_journal: str | None
    canonical_journal: str | None
    journal_short: str | None
    publisher: str | None
    homepage: str | None
    guide: str | None
    source_sections: list[str]
    has_main_tex: bool
    has_references_bib: bool
    bibliography_style: str | None
    section_total: int
    subsection_total: int
    theorem_env_total: int
    abstract_word_count: int
    main_body_word_count: int
    appendix_word_count: int
    appendix_ratio: float | None
    citation_keys_total: int
    bibliography_entries_total: int
    missing_bib_keys_total: int
    unused_bib_entries_total: int
    target_journal_bib_entries_total: int
    recent_target_journal_overlap_total: int
    recent_target_journal_overlap_sample: list[str]
    recent_recon_record_total: int
    recent_recon_abstract_total: int
    recent_recon_abstract_word_median: float | None
    recon_output_dir: str | None
    recon_error: str | None
    contract_templates_generated: list[str]
    issues: list[str]
    recommendations: list[str]


def slugify(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "_", text).strip("_").lower() or "journal_fit"


def write_json(path: Path, payload: Any) -> None:
    ensure_dir(path.parent)
    with open(io_path(path), "w", encoding="utf-8") as handle:
        handle.write(json.dumps(payload, ensure_ascii=False, indent=2) + "\n")


def write_markdown(path: Path, content: str) -> None:
    ensure_dir(path.parent)
    with open(io_path(path), "w", encoding="utf-8") as handle:
        handle.write(content.rstrip() + "\n")


def io_path(path: Path) -> str:
    text = os.path.abspath(str(path))
    if os.name != "nt":
        return text
    normalized = text.replace("/", "\\")
    if normalized.startswith("\\\\?\\"):
        return normalized
    if normalized.startswith("\\\\"):
        return "\\\\?\\UNC\\" + normalized[2:]
    return "\\\\?\\" + normalized


def ensure_dir(path: Path) -> None:
    os.makedirs(io_path(path), exist_ok=True)


def assets_root() -> Path:
    return Path(__file__).resolve().parent / "assets"


def load_asset(relative_path: str) -> str:
    target = assets_root() / relative_path
    return target.read_text(encoding="utf-8")


def count_words(text: str) -> int:
    return len(WORD_RE.findall(text))


def clean_tex_text(text: str) -> str:
    cleaned = re.sub(r"(?m)^\s*%.*$", " ", text)
    cleaned = re.sub(r"\\begin\{[^}]+\}|\\end\{[^}]+\}", " ", cleaned)
    cleaned = re.sub(r"\\[A-Za-z@]+(?:\*?)\s*(?:\[[^\]]*\])?(?:\{[^{}]*\})?", " ", cleaned)
    cleaned = re.sub(r"[{}$&_^~]", " ", cleaned)
    return re.sub(r"\s+", " ", cleaned).strip()


def normalize_title(text: str) -> str:
    return NORMALIZE_RE.sub("", text).lower()


def journal_hint(journal_name: str | None) -> dict[str, Any]:
    if not journal_name:
        return {}
    normalized = journal_name.casefold()
    for hint in JOURNAL_HINTS:
        if any(alias in normalized for alias in hint["aliases"]):
            return dict(hint)
    return {
        "canonical": journal_name.strip(),
        "short": journal_name.strip(),
        "publisher": None,
        "homepage": None,
        "guide": None,
        "guidance": [],
    }


def journal_profile_key(hint: dict[str, Any]) -> str:
    short = str(hint.get("short") or "").strip().lower()
    if short == "etds":
        return "etds"
    if short == "apal":
        return "apal"
    return "default"


def journal_profile_text(hint: dict[str, Any]) -> str:
    key = journal_profile_key(hint)
    return load_asset(f"journal_profiles/{key}.md")


def primary_target_journal(text: str | None) -> str | None:
    if not text:
        return None
    token = text.strip().strip("`")
    token = re.split(r"\s*\|\s*|;\s*|,\s+(?=[A-Z])", token, maxsplit=1)[0]
    token = token.strip()
    return token or None


def extract_abstract(text: str) -> str:
    match = ABSTRACT_RE.search(text)
    return clean_tex_text(match.group(1)) if match else ""


def bibliography_paths(publication_dir: Path, tex_text: str) -> list[Path]:
    match = BIBLIOGRAPHY_RE.search(tex_text)
    if not match:
        candidate = publication_dir / "references.bib"
        return [candidate] if candidate.is_file() else []
    names = [token.strip() for token in match.group(1).split(",") if token.strip()]
    candidates: list[Path] = []
    for name in names:
        candidate = publication_dir / f"{name}.bib"
        if candidate.is_file():
            candidates.append(candidate)
    return candidates


def extract_citation_keys(tex_text: str) -> list[str]:
    keys: list[str] = []
    for group in CITE_RE.findall(tex_text):
        for token in group.split(","):
            key = token.strip()
            if key:
                keys.append(key)
    return sorted(dict.fromkeys(keys))


def split_bib_entries(text: str) -> list[tuple[str, str, str]]:
    entries: list[tuple[str, str, str]] = []
    idx = 0
    while True:
        match = ENTRY_START_RE.search(text, idx)
        if not match:
            break
        entry_type = match.group(1).strip()
        key = match.group(2).strip()
        brace_start = text.find("{", match.start())
        if brace_start < 0:
            break
        depth = 0
        end = len(text)
        for cursor in range(brace_start, len(text)):
            char = text[cursor]
            if char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
                if depth == 0:
                    end = cursor
                    break
        body = text[match.end() : end]
        entries.append((entry_type, key, body))
        idx = end + 1
    return entries


def extract_bib_field(body: str, field: str) -> str:
    pattern = re.compile(FIELD_VALUE_RE.format(field=re.escape(field)))
    match = pattern.search(body)
    if not match:
        return ""
    value = match.group(1).strip().rstrip(",")
    if len(value) >= 2 and value[0] == value[-1] and value[0] in {'"', "'"}:
        value = value[1:-1]
    elif len(value) >= 2 and value[0] == "{" and value[-1] == "}":
        value = value[1:-1]
    return re.sub(r"\s+", " ", value.replace("\n", " ")).strip()


def load_bib_entries(paths: list[Path]) -> list[BibEntry]:
    entries: list[BibEntry] = []
    for path in paths:
        text = path.read_text(encoding="utf-8")
        for entry_type, key, body in split_bib_entries(text):
            entries.append(
                BibEntry(
                    key=key,
                    entry_type=entry_type,
                    title=extract_bib_field(body, "title"),
                    journal=extract_bib_field(body, "journal"),
                    doi=extract_bib_field(body, "doi"),
                    year=extract_bib_field(body, "year"),
                )
            )
    return entries


def match_recent_overlap(
    bib_entries: list[BibEntry],
    recent_papers: list[dict[str, Any]],
) -> tuple[int, list[str]]:
    by_doi = {entry.doi.lower().strip(): entry for entry in bib_entries if entry.doi}
    by_title = {normalize_title(entry.title): entry for entry in bib_entries if entry.title}
    matched_titles: list[str] = []
    for paper in recent_papers:
        doi = str(paper.get("doi") or "").lower().strip()
        title = str(paper.get("title") or "")
        if doi and doi in by_doi:
            matched_titles.append(title)
            continue
        normalized_title = normalize_title(title)
        if normalized_title and normalized_title in by_title:
            matched_titles.append(title)
    deduped = list(dict.fromkeys(title for title in matched_titles if title))
    return len(deduped), deduped[:10]


def analyze_manuscript(entry: publication_sync.PublicationEntry) -> dict[str, Any]:
    publication_dir = Path(entry.path)
    main_tex = publication_dir / "main.tex"
    if not main_tex.is_file():
        return {
            "has_references_bib": False,
            "bibliography_style": None,
            "section_total": 0,
            "subsection_total": 0,
            "theorem_env_total": 0,
            "abstract_word_count": 0,
            "main_body_word_count": 0,
            "appendix_word_count": 0,
            "appendix_ratio": None,
            "citation_keys": [],
            "bib_entries": [],
        }

    main_text = main_tex.read_text(encoding="utf-8")
    tex_text = expand_tex_inputs(publication_dir, main_text)
    appendix_idx = tex_text.find("\\appendix")
    if appendix_idx >= 0:
        body_text = tex_text[:appendix_idx]
        appendix_text = tex_text[appendix_idx:]
    else:
        body_text = tex_text
        appendix_text = ""

    citation_keys = extract_citation_keys(tex_text)
    bib_paths = bibliography_paths(publication_dir, main_text)
    bib_entries = load_bib_entries(bib_paths)
    main_body_words = count_words(clean_tex_text(body_text))
    appendix_words = count_words(clean_tex_text(appendix_text))
    bibliography_style = None
    style_match = BIBSTYLE_RE.search(main_text)
    if style_match:
        bibliography_style = style_match.group(1).strip()

    appendix_ratio = None
    total_words = main_body_words + appendix_words
    if total_words > 0:
        appendix_ratio = appendix_words / total_words

    return {
        "has_references_bib": any(path.is_file() for path in bib_paths),
        "bibliography_style": bibliography_style,
        "section_total": len(SECTION_RE.findall(tex_text)),
        "subsection_total": len(SUBSECTION_RE.findall(tex_text)),
        "theorem_env_total": len(THEOREM_ENV_RE.findall(tex_text)),
        "abstract_word_count": count_words(extract_abstract(tex_text)),
        "main_body_word_count": main_body_words,
        "appendix_word_count": appendix_words,
        "appendix_ratio": appendix_ratio,
        "citation_keys": citation_keys,
        "bib_entries": bib_entries,
    }


def resolve_input_path(publication_dir: Path, token: str) -> Path | None:
    candidate = publication_dir / token
    if candidate.is_file():
        return candidate
    if candidate.suffix != ".tex":
        tex_candidate = candidate.with_suffix(".tex")
        if tex_candidate.is_file():
            return tex_candidate
    return None


def expand_tex_inputs(publication_dir: Path, root_text: str) -> str:
    seen: set[Path] = set()

    def expand(text: str) -> str:
        def replace(match: re.Match[str]) -> str:
            token = match.group(1).strip()
            target = resolve_input_path(publication_dir, token)
            if target is None or target in seen:
                return ""
            seen.add(target)
            return expand(target.read_text(encoding="utf-8"))

        return INPUT_RE.sub(replace, text)

    return expand(root_text)


def build_recommendations(
    *,
    entry: publication_sync.PublicationEntry,
    hint: dict[str, Any],
    metrics: dict[str, Any],
    recent_summary: dict[str, Any],
    recent_overlap_total: int,
    target_journal_bib_entries_total: int,
    missing_bib_keys_total: int,
) -> tuple[list[str], list[str]]:
    issues: list[str] = []
    recommendations: list[str] = []

    if not entry.has_main_tex:
        issues.append("missing main.tex")
    if not metrics["has_references_bib"]:
        issues.append("missing references.bib or bibliography source")
    if missing_bib_keys_total > 0:
        issues.append(f"{missing_bib_keys_total} citation keys missing from bibliography")
    if recent_overlap_total == 0:
        issues.append("no recent target-journal papers matched in local bibliography")
    if entry.status in ACTIVE_STATUSES and not entry.has_source_map:
        issues.append("missing SOURCE_MAP.md")
    if entry.status in ACTIVE_STATUSES and not entry.has_theorem_list:
        issues.append("missing THEOREM_LIST.md")
    if metrics["appendix_ratio"] is not None and metrics["appendix_ratio"] > 0.35:
        issues.append("appendix share appears high for a main submission draft")

    if recent_summary:
        median = recent_summary.get("abstract_word_median")
        if isinstance(median, (int, float)) and median > 0:
            abstract_words = metrics["abstract_word_count"]
            if abstract_words == 0:
                recommendations.append("add or restore a concrete abstract before journal-fit review")
            elif abstract_words > 1.8 * median:
                recommendations.append("compress the abstract toward the target journal median cadence")
            elif abstract_words < 0.5 * median:
                recommendations.append("strengthen the abstract so it states theorem-level payoff more explicitly")

    if metrics["appendix_ratio"] is not None:
        if metrics["appendix_ratio"] > 0.35:
            recommendations.append("move nonessential detours out of the appendix or fold key arguments into the main text")
        else:
            recommendations.append("keep the appendix subordinate; retain only technical overflow there")

    if target_journal_bib_entries_total == 0:
        recommendations.append("add target-journal citations only where they materially sharpen related work or positioning")
    else:
        recommendations.append("retain target-journal citations only where they are mathematically relevant, not decorative")

    recommendations.extend(hint.get("guidance", []))
    recommendations.append("rewrite the introduction and theorem roadmap in the target journal's technical register, not manifesto language")
    recommendations.append("prefer short theorem-linked paragraphs and explicit statement of mathematical payoff")
    return issues, list(dict.fromkeys(recommendations))


def bullet_block(items: list[str], fallback: str) -> str:
    if not items:
        return f"- {fallback}"
    return "\n".join(f"- {item}" for item in items)


def render_template(template_name: str, mapping: dict[str, str]) -> str:
    template = load_asset(f"prompt_templates/{template_name}")
    rendered = template
    for key, value in mapping.items():
        rendered = rendered.replace(f"{{{{{key}}}}}", value)
    return rendered


def build_contract_templates(
    *,
    entry: publication_sync.PublicationEntry,
    linkage: publication_sync.LeanLinkageRecord | None,
    record: JournalFitRecord,
    recent_papers: list[dict[str, Any]],
) -> dict[str, str]:
    matched_labels = linkage.matched_labels_sample if linkage else []
    missing_labels = linkage.missing_labels_sample if linkage else []
    matched_decls = linkage.matched_declarations if linkage else []
    recent_titles = [str(paper.get("title") or "") for paper in recent_papers[:5] if paper.get("title")]

    journal_fit_template = "\n".join(
        [
            f"# Journal Fit: {record.directory}",
            "",
            f"- Target journal: `{record.canonical_journal or record.target_journal or 'unknown'}`",
            f"- Status: `{record.status}`",
            f"- Publisher: `{record.publisher or 'unknown'}`",
            f"- Homepage: `{record.homepage or 'n/a'}`",
            f"- Guide: `{record.guide or 'n/a'}`",
            f"- Recon sample size: `{record.recent_recon_record_total}`",
            f"- Median recent abstract length: `{record.recent_recon_abstract_word_median or 0:.1f}`",
            f"- Local appendix ratio: `{record.appendix_ratio:.1%}`" if record.appendix_ratio is not None else "- Local appendix ratio: `n/a`",
            "",
            "## Actions",
            "",
        ]
        + [f"- {item}" for item in record.recommendations[:10]]
    )

    bib_scope_template = "\n".join(
        [
            f"# Bibliography Scope: {record.directory}",
            "",
            f"- Target journal: `{record.canonical_journal or record.target_journal or 'unknown'}`",
            f"- Citation keys used in draft: `{record.citation_keys_total}`",
            f"- Bibliography entries available: `{record.bibliography_entries_total}`",
            f"- Target-journal references already present: `{record.target_journal_bib_entries_total}`",
            f"- Recent target-journal overlap: `{record.recent_target_journal_overlap_total}`",
            "",
            "## Required bibliography buckets",
            "",
            "- Foundational references directly used in statements or proofs.",
            "- Closest target-journal papers that define the local editorial conversation.",
            "- Immediate technical predecessors for the main theorem package.",
            "- References cited only when they are used for a concrete comparison or imported result.",
            "",
            "## Recent target-journal papers to review",
            "",
        ]
        + [f"- {title}" for title in recent_titles]
    )

    source_map_template = "\n".join(
        [
            f"# SOURCE_MAP: {record.directory}",
            "",
            "## Source sections",
            "",
        ]
        + [f"- `sections/body/{section}/`" for section in entry.source_sections]
        + [
            "",
            "## Lean linkage anchors",
            "",
        ]
        + ([f"- `{label}`" for label in matched_labels] or ["- Add exact paper-label anchors here."])
        + [
            "",
            "## Draft-to-source trace",
            "",
            "- State which theorem in the publication draft comes from which source section or Lean label.",
            "- Separate results kept in the paper from results deliberately cut for journal fit.",
        ]
    )

    theorem_list_template = "\n".join(
        [
            f"# THEOREM_LIST: {record.directory}",
            "",
            "## Matched Lean declarations",
            "",
        ]
        + (
            [
                f"- `{item['name']}` from `{item['module']}` at `{item['file']}:{item['line']}`"
                for item in matched_decls[:12]
            ]
            or ["- Add theorem statements and Lean anchors here."]
        )
        + [
            "",
            "## Missing or still-unmapped labels",
            "",
        ]
        + ([f"- `{label}`" for label in missing_labels] or ["- None recorded in the current fallback sample."])
    )

    return {
        "JOURNAL_FIT.template.md": journal_fit_template,
        "BIB_SCOPE.template.md": bib_scope_template,
        "SOURCE_MAP.template.md": source_map_template,
        "THEOREM_LIST.template.md": theorem_list_template,
    }


def build_workboard_files(
    *,
    entry: publication_sync.PublicationEntry,
    record: JournalFitRecord,
    hint: dict[str, Any],
    recent_papers: list[dict[str, Any]],
) -> dict[str, str]:
    profile_text = journal_profile_text(hint)
    mapping = {
        "DIRECTORY": record.directory,
        "JOURNAL": record.canonical_journal or record.target_journal or "unknown",
        "STATUS": record.status,
        "SOURCE_SECTIONS": ", ".join(f"`{section}`" for section in record.source_sections) or "`n/a`",
        "RECON_TOTAL": str(record.recent_recon_record_total),
        "APPENDIX_RATIO": f"{record.appendix_ratio:.1%}" if record.appendix_ratio is not None else "n/a",
        "ISSUES": bullet_block(record.issues, "No blocking issues recorded by the current audit."),
        "RECOMMENDATIONS": bullet_block(record.recommendations, "No extra recommendations recorded."),
        "JOURNAL_PROFILE": profile_text.strip(),
        "RECENT_PAPERS": bullet_block(
            [str(paper.get("title") or "") for paper in recent_papers if paper.get("title")],
            "No recent-paper titles were captured in the current reconnaissance sample.",
        ),
    }
    return {
        "JOURNAL_PROFILE.md": profile_text,
        "WORKBOARD.md": render_template("workboard.md", mapping),
        "01_research_extension.md": render_template("research_extension.md", mapping),
        "02_journal_style_rewrite.md": render_template("journal_style_rewrite.md", mapping),
        "03_editorial_review.md": render_template("editorial_review.md", mapping),
        "04_full_improvement.md": render_template("full_improvement.md", mapping),
    }


def render_revision_prompt(record: JournalFitRecord, recent_papers: list[dict[str, Any]]) -> str:
    recent_titles = [str(paper.get("title") or "") for paper in recent_papers[:5] if paper.get("title")]
    lines = [
        f"# Revision Prompt: {record.directory}",
        "",
        f"Target journal: `{record.canonical_journal or record.target_journal or 'unknown'}`",
        "",
        "Revise the manuscript to a submission-ready mathematical standard under the following constraints.",
        "",
        "- Learn the tone, title cadence, abstract compression, and theorem-roadmap style from recent papers in the target journal.",
        "- Remove AI-sounding exposition: avoid manifesto claims, padded motivation, and repetitive summary sentences.",
        "- Rebuild the introduction so that the mathematical problem, the main theorem package, and the paper's local novelty are explicit within the first pages.",
        "- Keep only citations that serve a concrete mathematical purpose. Add target-journal citations only when they are directly relevant to the theorem chain or positioning.",
        "- Do not repeat arguments already standard in the literature; cite them and move on.",
        "- Prefer a compact appendix footprint. If a proof is central to the paper's claim, it belongs in the main body.",
        "- Rewrite section transitions and theorem commentary in formal academic prose, with short paragraphs and explicit logical progression.",
        "",
        "Local audit signals:",
        f"- Appendix ratio: `{record.appendix_ratio:.1%}`" if record.appendix_ratio is not None else "- Appendix ratio: `n/a`",
        f"- Abstract word count: `{record.abstract_word_count}`",
        f"- Citation keys in draft: `{record.citation_keys_total}`",
        f"- Recent target-journal overlap in bibliography: `{record.recent_target_journal_overlap_total}`",
        "",
        "Recent target-journal papers to read before revision:",
    ]
    lines.extend(f"- {title}" for title in recent_titles or ["- None captured in the current reconnaissance sample."])
    lines.extend(
        [
            "",
            "Required outcome:",
            "- Deliver a full-article rewrite that reads like a human mathematical paper written for the target journal, with consistent notation, controlled claims, and a referee-facing logical arc.",
        ]
    )
    return "\n".join(lines)


def render_track_report(record: JournalFitRecord) -> str:
    lines = [
        f"# Journal Fit Report: {record.directory}",
        "",
        f"- Status: `{record.status}`",
        f"- Target journal: `{record.canonical_journal or record.target_journal or 'unknown'}`",
        f"- Publisher: `{record.publisher or 'unknown'}`",
        f"- Homepage: `{record.homepage or 'n/a'}`",
        f"- Guide: `{record.guide or 'n/a'}`",
        f"- Recon output: `{record.recon_output_dir or 'n/a'}`",
        f"- Recon records: `{record.recent_recon_record_total}`",
        f"- Recon abstracts: `{record.recent_recon_abstract_total}`",
        f"- Median recent abstract length: `{record.recent_recon_abstract_word_median or 0:.1f}`",
        "",
        "## Local Manuscript Metrics",
        "",
        f"- `main.tex` present: `{record.has_main_tex}`",
        f"- `references.bib` present: `{record.has_references_bib}`",
        f"- Bibliography style: `{record.bibliography_style or 'n/a'}`",
        f"- Sections: `{record.section_total}`",
        f"- Subsections: `{record.subsection_total}`",
        f"- Theorem-like environments: `{record.theorem_env_total}`",
        f"- Abstract words: `{record.abstract_word_count}`",
        f"- Main-body words: `{record.main_body_word_count}`",
        f"- Appendix words: `{record.appendix_word_count}`",
        f"- Appendix ratio: `{record.appendix_ratio:.1%}`" if record.appendix_ratio is not None else "- Appendix ratio: `n/a`",
        "",
        "## Citation Audit",
        "",
        f"- Citation keys used: `{record.citation_keys_total}`",
        f"- Bibliography entries: `{record.bibliography_entries_total}`",
        f"- Missing bibliography keys: `{record.missing_bib_keys_total}`",
        f"- Unused bibliography entries: `{record.unused_bib_entries_total}`",
        f"- Target-journal bibliography entries: `{record.target_journal_bib_entries_total}`",
        f"- Recent target-journal overlaps: `{record.recent_target_journal_overlap_total}`",
    ]
    if record.recent_target_journal_overlap_sample:
        lines.append(
            "- Overlap sample: "
            + "; ".join(f"`{title}`" for title in record.recent_target_journal_overlap_sample[:5])
        )
    if record.issues:
        lines.extend(["", "## Issues", ""])
        lines.extend(f"- {item}" for item in record.issues)
    if record.recommendations:
        lines.extend(["", "## Recommendations", ""])
        lines.extend(f"- {item}" for item in record.recommendations)
    if record.contract_templates_generated:
        lines.extend(["", "## Generated Templates", ""])
        lines.extend(f"- `{name}`" for name in record.contract_templates_generated)
    if record.recon_error:
        lines.extend(["", "## Recon Error", "", f"- {record.recon_error}"])
    return "\n".join(lines)


def render_root_report(manifest: dict[str, Any], records: list[JournalFitRecord]) -> str:
    lines = [
        "# Publication Journal Fit Report",
        "",
        f"- Publication root: `{manifest['publication_root']}`",
        f"- Tracks processed: `{manifest['record_total']}`",
        f"- Tracks with recon data: `{manifest['tracks_with_recon']}`",
        f"- Tracks with citation issues: `{manifest['tracks_with_citation_issues']}`",
        f"- Tracks with appendix-heavy drafts: `{manifest['tracks_with_appendix_pressure']}`",
        "",
        "| Directory | Status | Journal | Recon | Recent overlap | Issues |",
        "|---|---|---|---:|---:|---:|",
    ]
    for record in records:
        lines.append(
            f"| `{record.directory}` | `{record.status}` | `{record.journal_short or record.canonical_journal or 'n/a'}` | "
            f"{record.recent_recon_record_total} | {record.recent_target_journal_overlap_total} | {len(record.issues)} |"
        )
    return "\n".join(lines)


def output_root(slug: str) -> Path:
    return export_dir() / "publication_journal_fit" / slug


def track_output_name(index: int, directory: str) -> str:
    return f"{index:02d}_{slugify(directory)[:48]}"


def run_fit(
    *,
    publication_root: Path,
    slug: str,
    only_directories: set[str],
    max_papers: int,
    years_back: int,
    skip_auto_recon: bool,
) -> tuple[Path, dict[str, Any], list[JournalFitRecord]]:
    dir_meta, _ = publication_sync.parse_workspace_readme(publication_root / "README.md")
    entries = publication_sync.collect_publication_entries(publication_root, dir_meta)
    entries = [entry for entry in entries if entry.status in ACTIVE_STATUSES and entry.target_journal]
    if only_directories:
        entries = [entry for entry in entries if entry.directory in only_directories]
    linkages = publication_sync.build_lean_linkages(entries)
    linkage_by_dir = {linkage.directory: linkage for linkage in linkages}

    root = output_root(slug)
    ensure_dir(root)
    tracks_root = root / "tracks"
    ensure_dir(tracks_root)

    records: list[JournalFitRecord] = []
    for index, entry in enumerate(entries, start=1):
        target = primary_target_journal(entry.target_journal)
        hint = journal_hint(target)
        canonical = hint.get("canonical") or target
        short = hint.get("short") or canonical
        recon_dir: Path | None = None
        recon_error: str | None = None
        recent_summary: dict[str, Any] = {}
        recent_papers: list[dict[str, Any]] = []

        if canonical and not skip_auto_recon:
            recon_slug = f"publication_{slugify(entry.directory)}_{slugify(short or canonical)}"
            try:
                recon_result = journal_recon.run_recon(
                    journal=canonical,
                    journal_short=short or canonical,
                    max_papers=max_papers,
                    years_back=years_back,
                    output_dir=None,
                    slug=recon_slug,
                    skip_landing_fetch=False,
                )
                recon_dir = Path(recon_result["output_dir"])
            except Exception as exc:  # pragma: no cover - network/runtime dependent
                recon_error = str(exc)

        if recon_dir and (recon_dir / "recent_papers.json").is_file():
            payload = json.loads((recon_dir / "recent_papers.json").read_text(encoding="utf-8"))
            recent_summary = payload.get("style_summary") or {}
            recent_papers = list(payload.get("papers") or [])

        metrics = analyze_manuscript(entry)
        bib_entries: list[BibEntry] = metrics["bib_entries"]
        citation_keys: list[str] = metrics["citation_keys"]
        cited_key_set = set(citation_keys)
        bib_key_set = {bib_entry.key for bib_entry in bib_entries}
        missing_bib_keys_total = len([key for key in citation_keys if key not in bib_key_set])
        unused_bib_entries_total = len([bib_entry for bib_entry in bib_entries if bib_entry.key not in cited_key_set])
        target_journal_bib_entries_total = len(
            [
                bib_entry
                for bib_entry in bib_entries
                if bib_entry.journal and canonical and journal_recon.journal_match(canonical, bib_entry.journal)
            ]
        )
        recent_overlap_total, recent_overlap_sample = match_recent_overlap(bib_entries, recent_papers)
        issues, recommendations = build_recommendations(
            entry=entry,
            hint=hint,
            metrics=metrics,
            recent_summary=recent_summary,
            recent_overlap_total=recent_overlap_total,
            target_journal_bib_entries_total=target_journal_bib_entries_total,
            missing_bib_keys_total=missing_bib_keys_total,
        )

        record = JournalFitRecord(
            directory=entry.directory,
            status=entry.status,
            target_journal=entry.target_journal,
            canonical_journal=canonical,
            journal_short=short,
            publisher=hint.get("publisher"),
            homepage=hint.get("homepage"),
            guide=hint.get("guide"),
            source_sections=entry.source_sections,
            has_main_tex=entry.has_main_tex,
            has_references_bib=bool(metrics["has_references_bib"]),
            bibliography_style=metrics["bibliography_style"],
            section_total=metrics["section_total"],
            subsection_total=metrics["subsection_total"],
            theorem_env_total=metrics["theorem_env_total"],
            abstract_word_count=metrics["abstract_word_count"],
            main_body_word_count=metrics["main_body_word_count"],
            appendix_word_count=metrics["appendix_word_count"],
            appendix_ratio=metrics["appendix_ratio"],
            citation_keys_total=len(citation_keys),
            bibliography_entries_total=len(bib_entries),
            missing_bib_keys_total=missing_bib_keys_total,
            unused_bib_entries_total=unused_bib_entries_total,
            target_journal_bib_entries_total=target_journal_bib_entries_total,
            recent_target_journal_overlap_total=recent_overlap_total,
            recent_target_journal_overlap_sample=recent_overlap_sample,
            recent_recon_record_total=len(recent_papers),
            recent_recon_abstract_total=sum(1 for paper in recent_papers if paper.get("abstract")),
            recent_recon_abstract_word_median=float(recent_summary.get("abstract_word_median") or 0.0)
            if recent_summary
            else None,
            recon_output_dir=str(recon_dir) if recon_dir else None,
            recon_error=recon_error,
            contract_templates_generated=[],
            issues=issues,
            recommendations=recommendations,
        )

        track_dir = tracks_root / track_output_name(index, entry.directory)
        ensure_dir(track_dir)
        templates = build_contract_templates(
            entry=entry,
            linkage=linkage_by_dir.get(entry.directory),
            record=record,
            recent_papers=recent_papers,
        )
        workboard_files = build_workboard_files(
            entry=entry,
            record=record,
            hint=hint,
            recent_papers=recent_papers,
        )
        for name, content in templates.items():
            write_markdown(track_dir / name, content)
        for name, content in workboard_files.items():
            write_markdown(track_dir / name, content)
        record.contract_templates_generated = sorted(templates)
        write_json(track_dir / "journal_fit_profile.json", asdict(record))
        write_markdown(track_dir / "journal_fit_report.md", render_track_report(record))
        write_markdown(track_dir / "revision_prompt.md", render_revision_prompt(record, recent_papers))
        records.append(record)

    manifest = {
        "publication_root": str(publication_root),
        "record_total": len(records),
        "tracks_with_recon": sum(1 for record in records if record.recent_recon_record_total > 0),
        "tracks_with_citation_issues": sum(
            1
            for record in records
            if record.missing_bib_keys_total > 0 or record.recent_target_journal_overlap_total == 0
        ),
        "tracks_with_appendix_pressure": sum(
            1
            for record in records
            if record.appendix_ratio is not None and record.appendix_ratio > 0.35
        ),
        "directories": [record.directory for record in records],
    }
    write_json(root / "journal_fit_manifest.json", manifest)
    write_json(root / "journal_fit_records.json", [asdict(record) for record in records])
    write_markdown(root / "journal_fit_report.md", render_root_report(manifest, records))
    return root, manifest, records


def validate_fit_directory(path: Path) -> tuple[bool, list[str]]:
    errors: list[str] = []
    if not os.path.isdir(io_path(path)):
        return False, [f"Missing journal-fit directory: {path}"]
    for filename in REQUIRED_ROOT_FILES:
        if not os.path.isfile(io_path(path / filename)):
            errors.append(f"Missing required file: {path / filename}")
    tracks_root = path / "tracks"
    if not os.path.isdir(io_path(tracks_root)):
        errors.append(f"Missing tracks directory: {tracks_root}")
        return False, errors
    for track_dir in sorted(child for child in tracks_root.iterdir() if os.path.isdir(io_path(child))):
        for filename in REQUIRED_TRACK_FILES:
            if not os.path.isfile(io_path(track_dir / filename)):
                errors.append(f"Missing required file: {track_dir / filename}")
    return len(errors) == 0, errors


def cmd_run(args: argparse.Namespace) -> int:
    publication_root = Path(args.publication_root).resolve()
    output_dir, manifest, _ = run_fit(
        publication_root=publication_root,
        slug=args.slug,
        only_directories=set(args.only_directory or []),
        max_papers=args.max_papers,
        years_back=args.years_back,
        skip_auto_recon=args.skip_auto_recon,
    )
    print(
        "[publication-journal-fit] run: "
        f"publication_root={publication_root} slug={args.slug} output={output_dir} "
        f"records={manifest['record_total']} recon={manifest['tracks_with_recon']}",
        flush=True,
    )
    return 0


def cmd_validate(args: argparse.Namespace) -> int:
    target = Path(args.path).resolve()
    ok, errors = validate_fit_directory(target)
    print(
        "[publication-journal-fit] validate: "
        f"path={target} ok={ok} errors={len(errors)}",
        flush=True,
    )
    for error in errors:
        print(f"  - {error}", flush=True)
    return 0 if ok else 1


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Generate journal-fit reports and contract templates for publication tracks"
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    run_parser = subparsers.add_parser("run", help="Build journal-fit artifacts for active publication tracks")
    run_parser.add_argument("--publication-root", required=True, help="Path to the external publication workspace")
    run_parser.add_argument("--slug", required=True, help="Output slug under artifacts/export/publication_journal_fit/")
    run_parser.add_argument("--only-directory", action="append", help="Restrict processing to one publication directory")
    run_parser.add_argument("--max-papers", type=int, default=5, help="Recent-paper sample size per journal")
    run_parser.add_argument("--years-back", type=int, default=3, help="Publication window for journal reconnaissance")
    run_parser.add_argument("--skip-auto-recon", action="store_true", help="Skip network journal reconnaissance")
    run_parser.set_defaults(func=cmd_run)

    validate_parser = subparsers.add_parser("validate", help="Validate one generated journal-fit directory")
    validate_parser.add_argument("path", help="Path to artifacts/export/publication_journal_fit/<slug>")
    validate_parser.set_defaults(func=cmd_validate)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
