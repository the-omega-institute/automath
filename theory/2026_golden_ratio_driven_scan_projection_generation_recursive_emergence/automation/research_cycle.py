#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Automate one research-extension cycle from a paper slice."""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable

from automation_paths import automation_dir, export_dir, paper_root


INCLUDE_RE = re.compile(r"\\(?:input|subfile)\{([^}]+)\}")
CITE_RE = re.compile(r"\\cite[a-zA-Z*]*\{([^}]+)\}")
HEADING_RE = re.compile(
    r"\\(section|subsection|subsubsection|paragraph)\{([^}]*)\}"
)
CLAIM_ENV_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition|conjecture|remark)\}"
    r"(?:\[([^\]]*)\])?",
    re.DOTALL,
)
CLAIM_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
LABEL_WORD_RE = re.compile(r"[A-Za-z0-9]+")
NON_ASCII_RE = re.compile(r"[^\x20-\x7E]+")
REQUIRED_CYCLE_FILES = (
    "slice_manifest.json",
    "paper_slice.md",
    "formalization_backlog.json",
    "literature_survey_seed.md",
    "workflow_next_steps.md",
    "cycle_report.json",
)
REQUIRED_JOURNAL_PACK_FILES = (
    "journal_profile.json",
    "journal_brief.md",
    "deep_revision_prompt.md",
    "research_extension_prompt.md",
    "editorial_review_prompt.md",
    "boundary_profile.json",
    "boundary_report.md",
    "keep_drop_matrix.json",
    "split_strategy.md",
    "boundary_gate_prompt.md",
    "workflow.md",
    "submission_checklist.md",
    "journal_pack_manifest.json",
    "recent_paper_notes_template.md",
    "editorial_notes_template.md",
)
DEFAULT_BATCH_DASHBOARD = export_dir() / "research_cycles" / "_batch" / "body_batch_all" / "dashboard.json"
SECTION_SUPPORT_KEYWORDS = {
    "introduction",
    "preliminaries",
    "principles",
    "discussion",
    "conclusion",
    "experiments",
}
THEME_KEYWORDS = {
    "core_algebra": (
        "fold",
        "folding",
        "stable",
        "syntax",
        "arithmetic",
        "group",
        "algebra",
        "ring",
        "module",
        "field",
        "fiber",
        "fibonacci",
        "zeckendorf",
        "recursive",
        "address",
    ),
    "projection_dynamics": (
        "spg",
        "projection",
        "scan",
        "shift",
        "symbolic",
        "sofic",
        "dynamics",
        "entropy",
        "cut",
        "project",
        "parry",
        "adjacency",
        "pom",
    ),
    "zeta_number": (
        "zeta",
        "riemann",
        "euler",
        "prime",
        "dirichlet",
        "number",
        "finite part",
    ),
    "physics_speculative": (
        "phase",
        "gate",
        "physical",
        "spacetime",
        "observer",
        "quantum",
        "anomaly",
        "skeleton",
        "time",
        "protocol",
    ),
}
CLAIM_PRIORITY = {
    "theorem": 0,
    "proposition": 1,
    "corollary": 2,
    "lemma": 3,
    "definition": 4,
    "conjecture": 5,
    "remark": 6,
}


@dataclass(frozen=True)
class HeadingRecord:
    file: str
    line: int
    level: str
    title: str


@dataclass(frozen=True)
class ClaimRecord:
    file: str
    line: int
    environment: str
    label: str
    title: str
    summary: str


def repo_root() -> Path:
    return paper_root().parents[1]


def lean_root() -> Path:
    return repo_root() / "lean4"


def omega_ci_path() -> Path:
    return lean_root() / "scripts" / "omega_ci.py"


def journal_recon_path() -> Path:
    return automation_dir() / "journal_recon.py"


def load_omega_ci() -> Any:
    path = omega_ci_path()
    spec = importlib.util.spec_from_file_location("omega_ci_runtime", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Unable to load omega_ci from {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def load_journal_recon() -> Any:
    path = journal_recon_path()
    spec = importlib.util.spec_from_file_location("journal_recon_runtime", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Unable to load journal_recon from {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def slugify(text: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9]+", "_", text).strip("_").lower()
    return slug or "research_cycle"


def section_entry(raw: str) -> Path:
    value = raw.strip()
    candidates: list[Path] = []
    input_path = Path(value)

    def add(path: Path) -> None:
        candidates.append(path)
        if path.suffix == "":
            candidates.append(path.with_suffix(".tex"))
        if path.is_dir() or path.suffix == "":
            candidates.append(path / "main.tex")

    if input_path.is_absolute():
        add(input_path)
    else:
        add(paper_root() / value)
        add(paper_root() / "sections" / value)
        add(paper_root() / "sections" / "body" / value)
        add(paper_root() / "sections" / "appendix" / value)

    for candidate in candidates:
        if candidate.exists():
            if candidate.is_dir():
                main_tex = candidate / "main.tex"
                if main_tex.exists():
                    return main_tex.resolve()
            elif candidate.is_file():
                return candidate.resolve()

    raise FileNotFoundError(f"Unable to resolve section entry from {raw!r}")


def relative_to_paper(path: Path) -> str:
    return str(path.resolve().relative_to(paper_root()))


def resolve_include(current_file: Path, include_target: str) -> Path | None:
    raw = include_target.strip()
    if not raw:
        return None
    if raw.startswith("sections/"):
        candidate = paper_root() / raw
    else:
        candidate = current_file.parent / raw
    if candidate.suffix == "":
        candidate = candidate.with_suffix(".tex")
    if candidate.exists():
        return candidate.resolve()
    return None


def collect_slice_files(entry: Path) -> tuple[list[Path], list[str]]:
    visited: set[Path] = set()
    ordered: list[Path] = []
    missing_includes: list[str] = []

    def visit(path: Path) -> None:
        resolved = path.resolve()
        if resolved in visited:
            return
        visited.add(resolved)
        ordered.append(resolved)
        text = resolved.read_text(encoding="utf-8")
        for include in INCLUDE_RE.findall(text):
            target = resolve_include(resolved, include)
            if target is None:
                missing_includes.append(f"{relative_to_paper(resolved)} -> {include}")
                continue
            visit(target)

    visit(entry)
    return ordered, sorted(dict.fromkeys(missing_includes))


def latex_to_plain(text: str) -> str:
    cleaned = re.sub(r"\\label\{[^}]+\}", " ", text)
    cleaned = re.sub(r"\\cite[a-zA-Z*]*\{[^}]+\}", " ", cleaned)
    cleaned = re.sub(r"\\[A-Za-z*]+(?:\[[^\]]*\])?", " ", cleaned)
    cleaned = re.sub(r"[\{\}]", " ", cleaned)
    cleaned = re.sub(r"\s+", " ", cleaned)
    return cleaned.strip()


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def extract_headings(text: str, rel_path: str) -> list[HeadingRecord]:
    headings: list[HeadingRecord] = []
    for match in HEADING_RE.finditer(text):
        headings.append(
            HeadingRecord(
                file=rel_path,
                line=line_number(text, match.start()),
                level=match.group(1),
                title=latex_to_plain(match.group(2)),
            )
        )
    return headings


def extract_claims(text: str, rel_path: str) -> list[ClaimRecord]:
    claims: list[ClaimRecord] = []
    for match in CLAIM_ENV_RE.finditer(text):
        env = match.group(1)
        title = latex_to_plain(match.group(2) or "")
        end_marker = f"\\end{{{env}}}"
        end = text.find(end_marker, match.end())
        if end < 0:
            end = len(text)
        body = text[match.end() : end]
        label_match = CLAIM_LABEL_RE.search(body)
        label = label_match.group(1).strip() if label_match else ""
        summary = latex_to_plain(body)[:240]
        claims.append(
            ClaimRecord(
                file=rel_path,
                line=line_number(text, match.start()),
                environment=env,
                label=label,
                title=title,
                summary=summary,
            )
        )
    return claims


def extract_citation_keys(text: str) -> list[str]:
    keys: list[str] = []
    for match in CITE_RE.finditer(text):
        raw = match.group(1)
        for key in raw.split(","):
            value = key.strip()
            if value:
                keys.append(value)
    return keys


def parse_bib_entries(path: Path) -> dict[str, str]:
    text = path.read_text(encoding="utf-8")
    entries: dict[str, str] = {}
    i = 0
    while i < len(text):
        at = text.find("@", i)
        if at < 0:
            break
        brace = text.find("{", at)
        if brace < 0:
            break
        comma = text.find(",", brace)
        if comma < 0:
            break
        key = text[brace + 1 : comma].strip()
        depth = 1
        j = brace + 1
        while j < len(text) and depth > 0:
            if text[j] == "{":
                depth += 1
            elif text[j] == "}":
                depth -= 1
            j += 1
        entry = text[at:j].strip()
        if key:
            entries[key] = entry
        i = j
    return entries


def label_query_terms(label: str) -> str:
    return " ".join(LABEL_WORD_RE.findall(label.replace(":", " ").replace("-", " ")))


def unique_preserve(items: Iterable[str]) -> list[str]:
    return list(dict.fromkeys(item for item in items if item))


def build_literature_queries(
    *,
    slice_name: str,
    headings: list[HeadingRecord],
    claims: list[ClaimRecord],
) -> list[str]:
    queries: list[str] = [slice_name]
    queries.extend(heading.title for heading in headings[:10])
    queries.extend(claim.title for claim in claims if claim.title)
    queries.extend(label_query_terms(claim.label) for claim in claims if claim.label)
    cleaned = []
    for query in unique_preserve(queries):
        query = re.sub(r"\s+", " ", query).strip()
        if len(query) >= 6:
            cleaned.append(query)
    return cleaned[:25]


def build_formalization_backlog(
    *,
    claims: list[ClaimRecord],
    omega_ci: Any,
    top_suggestions: int,
    context: dict[str, Any] | None = None,
) -> dict[str, Any]:
    if context is None:
        context = build_formalization_context(omega_ci)
    declarations = context["declarations"]
    search_index = context["search_index"]
    registry_labels = context["registry_labels"]
    matched_labels = sorted(
        claim.label
        for claim in claims
        if claim.label and claim.label in registry_labels
    )
    missing_claims: list[dict[str, Any]] = []

    def try_search(query: str) -> list[dict[str, Any]]:
        query = query.strip()
        if not query:
            return []
        try:
            return omega_ci.search_declarations(
                declarations,
                query,
                top_suggestions,
                search_index=search_index,
            )
        except ValueError:
            return []

    for claim in claims:
        if not claim.label or claim.label in registry_labels:
            continue
        suggestions = try_search(claim.label)
        if not suggestions and claim.title:
            suggestions = try_search(claim.title)
        if not suggestions and claim.summary:
            suggestions = try_search(claim.summary)
        missing_claims.append(
            {
                "file": claim.file,
                "line": claim.line,
                "environment": claim.environment,
                "label": claim.label,
                "title": claim.title,
                "summary": claim.summary,
                "suggestions": suggestions,
            }
        )

    reasoning_frontier = sorted(
        [
            {
                "label": claim.label,
                "environment": claim.environment,
                "title": claim.title,
                "file": claim.file,
                "line": claim.line,
                "reason": (
                    "paper_conjecture"
                    if claim.environment == "conjecture"
                    else "missing_lean_registration"
                ),
            }
            for claim in claims
            if claim.environment == "conjecture"
            or (claim.label and claim.label not in registry_labels)
        ],
        key=lambda item: (
            0 if item["reason"] == "missing_lean_registration" else 1,
            CLAIM_PRIORITY.get(str(item["environment"]), 99),
            str(item["label"]),
        ),
    )

    return {
        "claims_total": len(claims),
        "claims_with_labels": sum(1 for claim in claims if claim.label),
        "matched_labels_total": len(set(matched_labels)),
        "missing_labels_total": len(missing_claims),
        "matched_labels": sorted(set(matched_labels)),
        "missing_claims": missing_claims,
        "reasoning_frontier": reasoning_frontier,
    }


def build_formalization_context(omega_ci: Any) -> dict[str, Any]:
    declarations, _ = omega_ci.build_inventory()
    return {
        "declarations": declarations,
        "search_index": omega_ci.build_search_index(declarations),
        "registry_labels": {
            label
            for decl in declarations
            for label in decl.registry_labels
        },
    }


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def render_slice_markdown(
    *,
    slice_name: str,
    entry: Path,
    files: list[Path],
    headings: list[HeadingRecord],
    claims: list[ClaimRecord],
    citations: list[str],
) -> str:
    lines = [
        f"# Paper Slice: {slice_name}",
        "",
        f"- Entry file: `{relative_to_paper(entry)}`",
        f"- TeX files in closure: {len(files)}",
        f"- Claim environments: {len(claims)}",
        f"- Citation keys: {len(citations)}",
        "",
        "## Headings",
    ]
    for heading in headings[:20]:
        lines.append(f"- [{heading.level}] {heading.title} ({heading.file}:{heading.line})")
    lines.extend(["", "## Claims"])
    for claim in claims[:30]:
        label = claim.label or "<unlabeled>"
        title = claim.title or claim.summary[:80]
        lines.append(f"- [{claim.environment}] {label} :: {title} ({claim.file}:{claim.line})")
    return "\n".join(lines) + "\n"


def render_literature_markdown(
    *,
    citations: list[str],
    bib_entries: dict[str, str],
    queries: list[str],
) -> str:
    lines = [
        "# Literature Survey Seed",
        "",
        "## Local Bibliography Hits",
    ]
    if citations:
        for key in citations[:40]:
            lines.append(f"- `{key}`")
    else:
        lines.append("- None")
    lines.extend(["", "## Suggested Search Queries"])
    for query in queries:
        lines.append(f"- {query}")
    lines.extend(["", "## Resolved Bib Entries"])
    resolved = 0
    for key in citations[:20]:
        entry = bib_entries.get(key)
        if entry is None:
            continue
        resolved += 1
        lines.append("")
        lines.append(f"### `{key}`")
        lines.append("```bibtex")
        lines.append(entry)
        lines.append("```")
    if resolved == 0:
        lines.append("- No local bibliography entries resolved.")
    return "\n".join(lines) + "\n"


def render_next_steps_markdown(
    *,
    backlog: dict[str, Any],
    slice_slug: str,
) -> str:
    missing_claims = backlog.get("missing_claims", [])
    reasoning_frontier = backlog.get("reasoning_frontier", [])
    lines = [
        "# Workflow Next Steps",
        "",
        "## Formalization Loop",
    ]
    if missing_claims:
        for claim in missing_claims[:10]:
            lines.append(
                f"- Formalize `{claim['label']}` from `{claim['file']}`:{claim['line']}; "
                f"start with `python lean4/scripts/omega_ci.py search \"{claim['label']}\" --top-k 5`."
            )
    else:
        lines.append("- No missing labeled claims in this slice.")

    lines.extend(["", "## Reasoning Frontier"])
    if reasoning_frontier:
        for item in reasoning_frontier[:10]:
            label = item["label"] or "<unlabeled>"
            lines.append(f"- {item['reason']}: `{label}` in `{item['file']}`:{item['line']}.")
    else:
        lines.append("- No frontier items extracted.")

    lines.extend(
        [
            "",
            "## Verification",
            "- Re-run `python lean4/scripts/omega_ci.py inventory --strict` after each batch of Lean changes.",
            "- Re-run `python lean4/scripts/omega_ci.py paper-coverage --sections body` to track exact label coverage drift.",
            "- Re-run `python3 automation/run_all.py` and `python3 automation/pipeline_contract.py validate` after experiment-side changes.",
            "",
            "## Artifact Location",
            f"- `artifacts/export/research_cycles/{slice_slug}/`",
        ]
    )
    return "\n".join(lines) + "\n"


def build_cycle_report(
    *,
    slice_slug: str,
    slice_name: str,
    entry: Path,
    files: list[Path],
    generated_files: list[Path],
    missing_includes: list[str],
    headings: list[HeadingRecord],
    claims: list[ClaimRecord],
    citations: list[str],
    resolved_citations: list[str],
    backlog: dict[str, Any],
    output_dir: Path,
) -> dict[str, Any]:
    return {
        "slice_slug": slice_slug,
        "slice_name": slice_name,
        "entry_file": relative_to_paper(entry),
        "output_dir": str(output_dir),
        "tex_files_total": len(files),
        "generated_files_total": len(generated_files),
        "missing_includes_total": len(missing_includes),
        "headings_total": len(headings),
        "claims_total": len(claims),
        "claims_labeled_total": sum(1 for claim in claims if claim.label),
        "citations_total": len(citations),
        "resolved_citations_total": len(resolved_citations),
        "matched_labels_total": backlog["matched_labels_total"],
        "missing_labels_total": backlog["missing_labels_total"],
        "reasoning_frontier_total": len(backlog["reasoning_frontier"]),
        "required_files": list(REQUIRED_CYCLE_FILES),
    }


def default_output_dir(slice_slug: str) -> Path:
    return export_dir() / "research_cycles" / slice_slug


def default_batch_output_dir(batch_slug: str) -> Path:
    return export_dir() / "research_cycles" / "_batch" / batch_slug


def default_seed_dir(seed_slug: str) -> Path:
    return export_dir() / "paper_seeds" / seed_slug


def default_journal_pack_dir(pack_slug: str) -> Path:
    return export_dir() / "journal_packs" / pack_slug


def default_journal_recon_dir(recon_slug: str) -> Path:
    return export_dir() / "journal_recon" / recon_slug


def validate_cycle_dir(path: Path) -> tuple[bool, list[str]]:
    errors: list[str] = []
    for name in REQUIRED_CYCLE_FILES:
        target = path / name
        if not target.is_file() or target.stat().st_size == 0:
            errors.append(f"Missing required cycle artifact: {name}")
    for json_name in ("slice_manifest.json", "formalization_backlog.json", "cycle_report.json"):
        target = path / json_name
        if target.is_file():
            try:
                json.loads(target.read_text(encoding="utf-8"))
            except json.JSONDecodeError as exc:
                errors.append(f"{json_name} invalid JSON: {exc}")
    return len(errors) == 0, errors


def validate_journal_pack_dir(path: Path) -> tuple[bool, list[str]]:
    errors: list[str] = []
    for name in REQUIRED_JOURNAL_PACK_FILES:
        target = path / name
        if not target.is_file() or target.stat().st_size == 0:
            errors.append(f"Missing required journal-pack artifact: {name}")
    for json_name in (
        "journal_profile.json",
        "journal_pack_manifest.json",
        "boundary_profile.json",
        "keep_drop_matrix.json",
        "recon_profile.json",
        "recent_papers.json",
    ):
        target = path / json_name
        if target.is_file():
            try:
                json.loads(target.read_text(encoding="utf-8"))
            except json.JSONDecodeError as exc:
                errors.append(f"{json_name} invalid JSON: {exc}")
    return len(errors) == 0, errors


def collect_cycle_files(entries: Iterable[Path]) -> tuple[list[Path], list[str]]:
    ordered: list[Path] = []
    seen: set[Path] = set()
    missing: list[str] = []
    for entry in entries:
        files, file_missing = collect_slice_files(entry)
        for path in files:
            resolved = path.resolve()
            if resolved in seen:
                continue
            seen.add(resolved)
            ordered.append(resolved)
        missing.extend(file_missing)
    return ordered, sorted(dict.fromkeys(missing))


def materialize_cycle_packet(
    *,
    entries: list[Path],
    source_sections: list[str],
    slice_slug: str,
    output_dir: Path,
    top_suggestions: int,
    omega_ci: Any | None,
    formalization_context: dict[str, Any] | None,
) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)

    files, missing_includes = collect_cycle_files(entries)
    generated_files = [path for path in files if "sections/generated/" in relative_to_paper(path).replace("\\", "/")]
    source_files = [path for path in files if path not in generated_files]

    headings: list[HeadingRecord] = []
    claims: list[ClaimRecord] = []
    citation_keys: list[str] = []
    for path in source_files:
        rel = relative_to_paper(path)
        text = path.read_text(encoding="utf-8")
        headings.extend(extract_headings(text, rel))
        claims.extend(extract_claims(text, rel))
        citation_keys.extend(extract_citation_keys(text))
    citation_keys = unique_preserve(citation_keys)

    bib_entries = parse_bib_entries(paper_root() / "references.bib")
    if headings:
        slice_name = headings[0].title
    else:
        source_names = [section.split("/")[-1] for section in source_sections if section]
        slice_name = " + ".join(source_names[:4]) if source_names else slice_slug
    queries = build_literature_queries(
        slice_name=slice_name,
        headings=headings,
        claims=claims,
    )

    runtime_omega_ci = omega_ci or load_omega_ci()
    backlog = build_formalization_backlog(
        claims=claims,
        omega_ci=runtime_omega_ci,
        top_suggestions=top_suggestions,
        context=formalization_context,
    )

    slice_manifest = {
        "slice_slug": slice_slug,
        "section": source_sections[0] if len(source_sections) == 1 else "",
        "sections": source_sections,
        "slice_name": slice_name,
        "entry_file": relative_to_paper(entries[0]),
        "entry_files": [relative_to_paper(path) for path in entries],
        "source_tex_files": [relative_to_paper(path) for path in source_files],
        "generated_tex_files": [relative_to_paper(path) for path in generated_files],
        "missing_includes": missing_includes,
        "headings": [asdict(item) for item in headings],
        "claims": [asdict(item) for item in claims],
        "citation_keys": citation_keys,
        "literature_queries": queries,
    }
    report = build_cycle_report(
        slice_slug=slice_slug,
        slice_name=slice_name,
        entry=entries[0],
        files=source_files,
        generated_files=generated_files,
        missing_includes=missing_includes,
        headings=headings,
        claims=claims,
        citations=citation_keys,
        resolved_citations=[key for key in citation_keys if key in bib_entries],
        backlog=backlog,
        output_dir=output_dir,
    )
    report["source_sections_total"] = len(source_sections)
    report["entry_files"] = [relative_to_paper(path) for path in entries]

    write_json(output_dir / "slice_manifest.json", slice_manifest)
    (output_dir / "paper_slice.md").write_text(
        render_slice_markdown(
            slice_name=slice_name,
            entry=entries[0],
            files=source_files,
            headings=headings,
            claims=claims,
            citations=citation_keys,
        ),
        encoding="utf-8",
    )
    write_json(output_dir / "formalization_backlog.json", backlog)
    (output_dir / "literature_survey_seed.md").write_text(
        render_literature_markdown(
            citations=citation_keys,
            bib_entries=bib_entries,
            queries=queries,
        ),
        encoding="utf-8",
    )
    (output_dir / "workflow_next_steps.md").write_text(
        render_next_steps_markdown(backlog=backlog, slice_slug=slice_slug),
        encoding="utf-8",
    )
    write_json(output_dir / "cycle_report.json", report)

    ok, errors = validate_cycle_dir(output_dir)
    if not ok:
        raise RuntimeError("; ".join(errors))

    print(
        "[research-cycle] create:"
        f" sections={source_sections!r}"
        f" slug={slice_slug}"
        f" files={len(source_files)}"
        f" claims={len(claims)}"
        f" missing_labels={backlog['missing_labels_total']}"
        f" citations={len(citation_keys)}"
        f" output={output_dir}"
    )
    return {
        "section": source_sections[0] if len(source_sections) == 1 else "",
        "sections": source_sections,
        "slice_slug": slice_slug,
        "slice_name": slice_name,
        "output_dir": str(output_dir),
        "slice_manifest": slice_manifest,
        "cycle_report": report,
        "formalization_backlog": backlog,
    }


def create_cycle_packet(
    *,
    section: str,
    slice_slug: str | None,
    output_dir: Path | None,
    top_suggestions: int,
    omega_ci: Any | None = None,
    formalization_context: dict[str, Any] | None = None,
) -> dict[str, Any]:
    entry = section_entry(section)
    resolved_slug = slice_slug or slugify(relative_to_paper(entry).replace("/", "_"))
    target_dir = output_dir.resolve() if output_dir else default_output_dir(resolved_slug)
    return materialize_cycle_packet(
        entries=[entry],
        source_sections=[section],
        slice_slug=resolved_slug,
        output_dir=target_dir,
        top_suggestions=top_suggestions,
        omega_ci=omega_ci,
        formalization_context=formalization_context,
    )


def create_multi_cycle_packet(
    *,
    sections: list[str],
    slice_slug: str | None,
    output_dir: Path | None,
    top_suggestions: int,
    omega_ci: Any | None = None,
    formalization_context: dict[str, Any] | None = None,
) -> dict[str, Any]:
    if not sections:
        raise RuntimeError("create_multi_cycle_packet requires at least one section")
    entries = [section_entry(section) for section in sections]
    default_slug = slugify("_".join(section.replace("/", "_") for section in sections))
    resolved_slug = slice_slug or default_slug
    target_dir = output_dir.resolve() if output_dir else default_output_dir(resolved_slug)
    return materialize_cycle_packet(
        entries=entries,
        source_sections=sections,
        slice_slug=resolved_slug,
        output_dir=target_dir,
        top_suggestions=top_suggestions,
        omega_ci=omega_ci,
        formalization_context=formalization_context,
    )


def load_cycle_packet(path: Path) -> dict[str, Any]:
    target = path.resolve()
    ok, errors = validate_cycle_dir(target)
    if not ok:
        raise RuntimeError("; ".join(errors))
    return {
        "path": target,
        "slice_manifest": json.loads((target / "slice_manifest.json").read_text(encoding="utf-8")),
        "cycle_report": json.loads((target / "cycle_report.json").read_text(encoding="utf-8")),
        "formalization_backlog": json.loads((target / "formalization_backlog.json").read_text(encoding="utf-8")),
    }


def read_optional_text(path: Path | None) -> str:
    if path is None:
        return ""
    return path.read_text(encoding="utf-8").strip()


def load_recon_notes(
    *,
    journal: str,
    journal_short: str,
    recon_dir: Path | None,
) -> tuple[str, Path | None]:
    candidates: list[Path] = []
    if recon_dir is not None:
        resolved = recon_dir.resolve()
        if resolved.is_dir():
            candidates.append(resolved / "recent_paper_notes.md")
        else:
            candidates.append(resolved)
    else:
        for slug in dict.fromkeys(
            [
                slugify(journal_short),
                slugify(journal),
            ]
        ):
            if slug:
                candidates.append(default_journal_recon_dir(slug) / "recent_paper_notes.md")
    for candidate in candidates:
        if candidate.is_file():
            return candidate.read_text(encoding="utf-8").strip(), candidate
    return "", None


def auto_fill_recon_notes(
    *,
    journal: str,
    journal_short: str,
    recon_dir: Path | None,
    max_papers: int,
    years_back: int,
) -> tuple[str, Path | None, Path | None, str]:
    journal_recon = load_journal_recon()
    target_dir = recon_dir.resolve() if recon_dir else default_journal_recon_dir(slugify(journal_short or journal))
    error_message = ""
    try:
        result = journal_recon.run_recon(
            journal=journal,
            journal_short=journal_short,
            max_papers=max_papers,
            years_back=years_back,
            output_dir=target_dir,
            slug=target_dir.name,
            skip_landing_fetch=False,
        )
        resolved_dir = Path(result["output_dir"]).resolve()
        notes, notes_path = load_recon_notes(
            journal=journal,
            journal_short=journal_short,
            recon_dir=resolved_dir,
        )
        return notes, notes_path, resolved_dir, ""
    except Exception as exc:
        error_message = str(exc)
        return "", None, target_dir, error_message


def load_research_source(path: Path) -> dict[str, Any]:
    target = path.resolve()
    seed_manifest_path = target / "seed_manifest.json"
    if seed_manifest_path.is_file():
        seed_manifest = json.loads(seed_manifest_path.read_text(encoding="utf-8"))
        cycle_packet = None
        cycle_dir_value = str(seed_manifest.get("source_cycle_dir") or "").strip()
        if cycle_dir_value:
            cycle_dir = Path(cycle_dir_value)
            ok, _ = validate_cycle_dir(cycle_dir)
            if ok:
                cycle_packet = load_cycle_packet(cycle_dir)
        return {
            "source_type": "seed",
            "source_dir": str(target),
            "seed_manifest": seed_manifest,
            "seed_readme": read_optional_text(target / "README.md"),
            "seed_files": seed_manifest.get("files", []),
            "cycle_packet": cycle_packet,
        }

    ok, _ = validate_cycle_dir(target)
    if ok:
        cycle_packet = load_cycle_packet(target)
        return {
            "source_type": "cycle",
            "source_dir": str(target),
            "seed_manifest": None,
            "seed_readme": "",
            "seed_files": [],
            "cycle_packet": cycle_packet,
        }

    raise RuntimeError(f"Unsupported source directory: {target}")


def source_slug(source: dict[str, Any]) -> str:
    seed_manifest = source.get("seed_manifest")
    if isinstance(seed_manifest, dict):
        return str(seed_manifest.get("seed_slug") or seed_manifest.get("source_slice_slug") or "journal_pack_source")
    cycle_packet = source.get("cycle_packet")
    if isinstance(cycle_packet, dict):
        return str(cycle_packet["slice_manifest"].get("slice_slug") or "journal_pack_source")
    return "journal_pack_source"


def source_cycle_report(source: dict[str, Any]) -> dict[str, Any]:
    cycle_packet = source.get("cycle_packet")
    if isinstance(cycle_packet, dict):
        return cycle_packet["cycle_report"]
    return {}


def source_backlog(source: dict[str, Any]) -> dict[str, Any]:
    cycle_packet = source.get("cycle_packet")
    if isinstance(cycle_packet, dict):
        return cycle_packet["formalization_backlog"]
    return {}


def source_slice_manifest(source: dict[str, Any]) -> dict[str, Any]:
    cycle_packet = source.get("cycle_packet")
    if isinstance(cycle_packet, dict):
        return cycle_packet["slice_manifest"]
    return {}


def resolve_dashboard_path(path: Path | None) -> Path | None:
    if path is not None:
        candidate = path.resolve()
        if candidate.is_dir():
            candidate = candidate / "dashboard.json"
        return candidate if candidate.is_file() else None
    if DEFAULT_BATCH_DASHBOARD.is_file():
        return DEFAULT_BATCH_DASHBOARD
    return None


def load_batch_dashboard(path: Path | None) -> dict[str, Any] | None:
    resolved = resolve_dashboard_path(path)
    if resolved is None:
        return None
    payload = json.loads(resolved.read_text(encoding="utf-8"))
    payload["_dashboard_path"] = str(resolved)
    return payload


def normalize_theme_text(*parts: str) -> str:
    text = " ".join(part for part in parts if part)
    text = text.replace("/", " ").replace("_", " ").replace("-", " ").lower()
    return re.sub(r"\s+", " ", text).strip()


def classify_section_theme(section: str, slice_name: str) -> dict[str, Any]:
    section_name = section.split("/")[-1].strip().lower()
    scores = {theme: 0 for theme in THEME_KEYWORDS}
    if section_name in SECTION_SUPPORT_KEYWORDS:
        scores["support_scaffold"] = 10
    else:
        scores["support_scaffold"] = 0
    haystack = normalize_theme_text(section, slice_name)
    for theme, keywords in THEME_KEYWORDS.items():
        for keyword in keywords:
            if keyword in haystack:
                scores[theme] += 1
    primary_theme = max(scores, key=lambda key: (scores[key], key))
    if scores[primary_theme] <= 0:
        primary_theme = "misc_program"
    ranked = [
        {"theme": theme, "score": score}
        for theme, score in sorted(scores.items(), key=lambda item: (-item[1], item[0]))
        if score > 0
    ]
    return {
        "section": section,
        "slice_name": slice_name,
        "primary_theme": primary_theme,
        "ranked_themes": ranked,
    }


def build_theme_map_from_dashboard(dashboard: dict[str, Any] | None) -> list[dict[str, Any]]:
    if dashboard is None:
        return []
    themed: list[dict[str, Any]] = []
    for item in dashboard.get("sections", []):
        theme_info = classify_section_theme(str(item.get("section", "")), str(item.get("slice_name", "")))
        themed.append({**item, **theme_info})
    return themed


def infer_journal_boundary_preferences(journal: str) -> dict[str, Any]:
    lowered = journal.lower()
    include = ["core_algebra"]
    secondary = ["projection_dynamics"]
    exclude = ["physics_speculative"]
    notes = [
        "Prefer a smaller number of structurally strong results over a broad manifesto.",
        "Rewrite support material for the new submission rather than copying original global sections verbatim.",
    ]
    if "algebra" in lowered:
        include = ["core_algebra", "zeta_number"]
        secondary = ["projection_dynamics"]
        exclude = ["physics_speculative"]
        notes.append("Foreground algebraic structures, ring/module language, and rigorous combinatorial lemmas.")
    elif "dynamics" in lowered or "ergodic" in lowered or "symbolic" in lowered:
        include = ["projection_dynamics"]
        secondary = ["core_algebra"]
        exclude = ["physics_speculative"]
        notes.append("Foreground shift, sofic, entropy, and transfer-operator narratives.")
    elif "number" in lowered or "analytic" in lowered or "zeta" in lowered:
        include = ["zeta_number"]
        secondary = ["core_algebra"]
        exclude = ["physics_speculative"]
        notes.append("Strip speculative framing and push arithmetic / zeta structure to the front.")
    elif "physics" in lowered:
        include = ["physics_speculative", "projection_dynamics"]
        secondary = ["core_algebra"]
        exclude = []
        notes.append("Keep mathematically rigorous structure, but allow physically motivated interpretation.")
    return {
        "include_themes": include,
        "secondary_themes": secondary,
        "exclude_themes": exclude,
        "notes": notes,
    }


def current_source_sections(source: dict[str, Any]) -> list[str]:
    slice_manifest = source_slice_manifest(source)
    sections = slice_manifest.get("sections")
    if isinstance(sections, list):
        cleaned = [str(section).strip() for section in sections if str(section).strip()]
        if cleaned:
            return cleaned
    section = str(slice_manifest.get("section") or "").strip()
    if section:
        return [section]
    entry_file = str(slice_manifest.get("entry_file") or "")
    if entry_file.startswith("sections/") and entry_file.endswith("/main.tex"):
        return [entry_file.removeprefix("sections/").removesuffix("/main.tex")]
    return []


def build_keep_drop_matrix(
    *,
    source: dict[str, Any],
    dashboard: dict[str, Any] | None,
    journal: str,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    preferences = infer_journal_boundary_preferences(journal)
    themed_sections = build_theme_map_from_dashboard(dashboard)
    source_sections = set(current_source_sections(source))
    slice_manifest = source_slice_manifest(source)
    source_theme = "misc_program"
    if source_sections:
        source_theme = classify_section_theme(next(iter(source_sections)), str(slice_manifest.get("slice_name", ""))).get("primary_theme", "misc_program")

    matrix: list[dict[str, Any]] = []
    for item in themed_sections:
        theme = str(item.get("primary_theme", "misc_program"))
        section = str(item.get("section", ""))
        if section in source_sections:
            decision = "keep_primary"
            rationale = "Current manuscript focus."
        elif theme == "support_scaffold":
            decision = "rewrite_support"
            rationale = "Use only as a rewrite template; do not carry global support text verbatim."
        elif theme in preferences["exclude_themes"]:
            decision = "split_out"
            rationale = "Theme is outside the inferred journal boundary."
        elif theme == source_theme and theme in preferences["include_themes"]:
            decision = "merge_candidate"
            rationale = "Same primary theme as the current source and naturally mergeable."
        elif theme in preferences["include_themes"]:
            decision = "consider_in_scope"
            rationale = "Within the inferred journal boundary, but not the current narrative core."
        elif theme in preferences["secondary_themes"]:
            decision = "consider_secondary"
            rationale = "Potentially relevant, but should not dominate the submission."
        else:
            decision = "out_of_scope"
            rationale = "Does not sharpen the target journal positioning."
        matrix.append(
            {
                "section": section,
                "slice_name": item.get("slice_name", ""),
                "primary_theme": theme,
                "claims_total": item.get("claims_total", 0),
                "matched_labels_total": item.get("matched_labels_total", 0),
                "missing_labels_total": item.get("missing_labels_total", 0),
                "decision": decision,
                "rationale": rationale,
                "cycle_dir": item.get("cycle_dir", ""),
            }
        )

    boundary_profile = {
        "journal": journal,
        "dashboard_path": dashboard.get("_dashboard_path", "") if dashboard else "",
        "source_sections": sorted(source_sections),
        "source_theme": source_theme,
        "include_themes": preferences["include_themes"],
        "secondary_themes": preferences["secondary_themes"],
        "exclude_themes": preferences["exclude_themes"],
        "notes": preferences["notes"],
    }
    return boundary_profile, matrix


def render_boundary_report(profile: dict[str, Any], matrix: list[dict[str, Any]]) -> str:
    groups = {
        "keep_primary": "Keep As Core",
        "merge_candidate": "Merge Candidates",
        "consider_in_scope": "In-Scope But Optional",
        "consider_secondary": "Secondary / Conditional",
        "rewrite_support": "Rewrite-Only Support",
        "split_out": "Split Out",
        "out_of_scope": "Out Of Scope",
    }
    lines = [
        f"# Boundary Report: {profile['journal']}",
        "",
        f"- Source sections: {', '.join(profile['source_sections']) or 'none'}",
        f"- Source theme: `{profile['source_theme']}`",
        f"- Included themes: {', '.join(profile['include_themes']) or 'none'}",
        f"- Secondary themes: {', '.join(profile['secondary_themes']) or 'none'}",
        f"- Excluded themes: {', '.join(profile['exclude_themes']) or 'none'}",
        "",
        "## Editorial Notes",
    ]
    for note in profile.get("notes", []):
        lines.append(f"- {note}")
    for decision, title in groups.items():
        lines.extend(["", f"## {title}"])
        subset = [item for item in matrix if item["decision"] == decision]
        if not subset:
            lines.append("- None")
            continue
        for item in sorted(subset, key=lambda value: (-int(value["claims_total"]), str(value["section"]))):
            lines.append(
                "- "
                f"`{item['section']}` ({item['primary_theme']}, claims={item['claims_total']}, missing={item['missing_labels_total']}) "
                f"- {item['rationale']}"
            )
    return "\n".join(lines) + "\n"


def render_split_strategy(profile: dict[str, Any], matrix: list[dict[str, Any]]) -> str:
    primary = [item["section"] for item in matrix if item["decision"] == "keep_primary"]
    merge = [item["section"] for item in matrix if item["decision"] == "merge_candidate"]
    rewrite = [item["section"] for item in matrix if item["decision"] == "rewrite_support"]
    split_out = [item["section"] for item in matrix if item["decision"] in {"split_out", "out_of_scope"}]
    lines = [
        f"# Split Strategy for {profile['journal']}",
        "",
        "## Recommended Core Boundary",
        f"- Keep now: {', '.join(primary) or 'none'}",
        f"- Strong same-theme merge candidates: {', '.join(merge) or 'none'}",
        f"- Rewrite-only support sources: {', '.join(rewrite) or 'none'}",
        f"- Sections to spin out: {', '.join(split_out) or 'none'}",
    ]
    if primary or merge:
        suggested_sections = primary + merge[:3]
        suggested_slug = f"{slugify(profile['journal'])}_{slugify(profile['source_theme'])}_bundle"
        lines.extend(
            [
                "",
                "## Suggested Packet Command",
                "```bash",
                "python3 automation/research_cycle.py create --sections "
                + " ".join(suggested_sections)
                + f" --slug {suggested_slug}",
                "```",
            ]
        )
    return "\n".join(lines) + "\n"


def render_boundary_gate_prompt(profile: dict[str, Any], matrix: list[dict[str, Any]]) -> str:
    merge = [item["section"] for item in matrix if item["decision"] == "merge_candidate"]
    split_out = [item["section"] for item in matrix if item["decision"] in {"split_out", "out_of_scope"}]
    lines = [
        f"# Boundary Gate Prompt for {profile['journal']}",
        "",
        "你是目标期刊的编辑。请只判断稿件边界是否正确，而不是泛泛润色。",
        "",
        "## Current Boundary",
        f"- Core source sections: {', '.join(profile['source_sections']) or 'none'}",
        f"- Inferred source theme: {profile['source_theme']}",
        f"- Same-theme merge candidates: {', '.join(merge) or 'none'}",
        f"- Sections to split out: {', '.join(split_out) or 'none'}",
        "",
        "## Required Decision",
        "1. 当前边界是否足以支持该期刊投稿？",
        "2. 若不足，请明确指出必须删除、下沉、拆分或并入的 section。",
        "3. 明确回答：如果你是编辑，你会允许这篇文章以当前边界送外审吗？",
        "4. 禁止停留在温和建议；必须给出边界级别的 Yes / No 判断。",
    ]
    return "\n".join(lines) + "\n"


def top_frontier_labels(backlog: dict[str, Any], limit: int = 12) -> list[str]:
    labels: list[str] = []
    for claim in backlog.get("missing_claims", []):
        label = str(claim.get("label") or "").strip()
        if label and label not in labels:
            labels.append(label)
        if len(labels) >= limit:
            break
    return labels


def render_recent_paper_notes_template(*, journal: str, journal_short: str, article_type: str) -> str:
    lines = [
        f"# Recent Accepted Paper Notes: {journal}",
        "",
        f"- Journal short name: {journal_short or journal}",
        f"- Target article type: {article_type}",
        "",
        "## Recent Papers To Study",
        "- Paper 1:",
        "  title:",
        "  year:",
        "  stylistic takeaways:",
        "- Paper 2:",
        "  title:",
        "  year:",
        "  stylistic takeaways:",
        "- Paper 3:",
        "  title:",
        "  year:",
        "  stylistic takeaways:",
        "",
        "## Structure Signals",
        "- Typical abstract cadence:",
        "- Introduction length and tone:",
        "- Main-body / appendix proportion:",
        "- Theorem density and proof placement:",
        "- Related work integration style:",
        "",
        "## Editorial Red Flags",
        "-",
        "",
    ]
    return "\n".join(lines) + "\n"


def render_editorial_notes_template(*, journal: str) -> str:
    lines = [
        f"# Editorial Notes Template: {journal}",
        "",
        "## Non-Negotiable Constraints",
        "-",
        "",
        "## Positioning",
        "- Why this journal instead of adjacent venues:",
        "- What the paper must contribute at editor level:",
        "",
        "## Revision Priorities",
        "1. ",
        "2. ",
        "3. ",
        "",
    ]
    return "\n".join(lines) + "\n"


def build_journal_profile(
    *,
    source: dict[str, Any],
    journal: str,
    journal_short: str,
    article_type: str,
    paper_language: str,
    positioning: str,
    scope_fit: str,
    recent_paper_notes: str,
    recon_notes_path: str,
    recon_dir: str,
    auto_recon_attempted: bool,
    auto_recon_succeeded: bool,
    auto_recon_error: str,
    recon_max_papers: int,
    recon_years_back: int,
    editorial_notes: str,
) -> dict[str, Any]:
    cycle_report = source_cycle_report(source)
    backlog = source_backlog(source)
    slice_manifest = source_slice_manifest(source)
    seed_manifest = source.get("seed_manifest") or {}
    return {
        "journal": journal,
        "journal_short": journal_short or journal,
        "article_type": article_type,
        "paper_language": paper_language,
        "positioning": positioning,
        "scope_fit": scope_fit,
        "source_type": source["source_type"],
        "source_dir": source["source_dir"],
        "source_slug": source_slug(source),
        "source_entry_file": slice_manifest.get("entry_file") or seed_manifest.get("source_entry_file", ""),
        "claims_total": cycle_report.get("claims_total", seed_manifest.get("claims_total", 0)),
        "matched_labels_total": backlog.get("matched_labels_total", 0),
        "missing_labels_total": backlog.get("missing_labels_total", seed_manifest.get("missing_labels_total", 0)),
        "resolved_bibliography_total": seed_manifest.get("resolved_bibliography_total", 0),
        "citation_keys_total": len(slice_manifest.get("citation_keys", [])),
        "frontier_labels": top_frontier_labels(backlog),
        "recent_paper_notes_provided": bool(recent_paper_notes),
        "recon_notes_path": recon_notes_path,
        "recon_dir": recon_dir,
        "auto_recon_attempted": auto_recon_attempted,
        "auto_recon_succeeded": auto_recon_succeeded,
        "auto_recon_error": auto_recon_error,
        "recon_max_papers": recon_max_papers,
        "recon_years_back": recon_years_back,
        "editorial_notes_provided": bool(editorial_notes),
        "seed_files": source.get("seed_files", []),
    }


def render_journal_brief_markdown(profile: dict[str, Any]) -> str:
    lines = [
        f"# Journal Pack Brief: {profile['journal']}",
        "",
        f"- Source type: `{profile['source_type']}`",
        f"- Source directory: `{profile['source_dir']}`",
        f"- Source slug: `{profile['source_slug']}`",
        f"- Article type: `{profile['article_type']}`",
        f"- Manuscript language: `{profile['paper_language']}`",
        f"- Claims in source slice: {profile['claims_total']}",
        f"- Exact Lean label matches: {profile['matched_labels_total']}",
        f"- Missing labeled claims: {profile['missing_labels_total']}",
        f"- Local bibliography subset in seed: {profile['resolved_bibliography_total']}",
        f"- Recent-paper notes available: {profile['recent_paper_notes_provided']}",
        f"- Auto recon attempted: {profile['auto_recon_attempted']}",
        f"- Auto recon succeeded: {profile['auto_recon_succeeded']}",
        "",
        "## Positioning",
        profile["positioning"] or "- Not supplied.",
        "",
        "## Scope Fit",
        profile["scope_fit"] or "- Not supplied.",
        "",
        "## Journal Recon",
        f"- Recon notes path: `{profile['recon_notes_path'] or 'none'}`",
        f"- Recon directory: `{profile['recon_dir'] or 'none'}`",
        f"- Recon sample target: {profile['recon_max_papers']} papers within {profile['recon_years_back']} years",
    ]
    if profile.get("auto_recon_error"):
        lines.extend(["", "## Auto Recon Error", profile["auto_recon_error"]])
    lines.extend(
        [
            "",
        "## High-Leverage Frontier Labels",
        ]
    )
    frontier_labels = profile.get("frontier_labels", [])
    if frontier_labels:
        for label in frontier_labels:
            lines.append(f"- `{label}`")
    else:
        lines.append("- None extracted from the current source.")
    return "\n".join(lines) + "\n"


def render_deep_revision_prompt(profile: dict[str, Any], recent_paper_notes: str, editorial_notes: str) -> str:
    lines = [
        f"# Deep Revision Prompt for {profile['journal']}",
        "",
        "## Role",
        (
            f"你是 {profile['journal']} 的资深编辑、审稿人和成熟作者。"
            "请将当前论文从研究草案提升到你愿意送外审并倾向接收的水准。"
        ),
        "",
        "## Source Dossier",
        f"- Source type: `{profile['source_type']}`",
        f"- Source directory: `{profile['source_dir']}`",
        f"- Claims in current slice: {profile['claims_total']}",
        f"- Missing labeled claims: {profile['missing_labels_total']}",
        f"- Frontier labels to prioritize: {', '.join(profile.get('frontier_labels', [])[:10]) or 'none'}",
        "",
        "## Hard Requirements",
        "1. 先研究目标期刊近年被接收论文的语言风格、结构组织、引言节奏、定理密度、附录比例、摘要写法与结论落点，再开始重写。",
        "2. 不得机械润色。允许重构全文、重排章节、重写摘要与引言、重构附录与主文比例，只以投稿效果为准。",
        "3. 不得重复本文已有表述的低增量改写，不得重复公开文献中已经发表的推理过程、定理、推论、命题、猜想及证明。",
        "4. 可以调用已发表结论，但必须明确其用途并保留引用空间；新增内容必须体现可投稿的新价值，而非中间过程结论。",
        "5. 只保留真正能支撑投稿叙事的深刻结论，主动删除冗余、过度铺垫、空泛价值判断和明显 AI 味表达。",
        "6. 行文必须学术化，禁止口语，禁止模板式吹捧，禁止机械重复“值得注意的是”“可以看到”等空洞转折。",
        "7. 若当前稿件不达接收线，必须直接重构并补强到你愿意接收的水平，而不是停在建议列表。",
        "",
        "## Required Work Sequence",
        "1. 明确该稿件对目标期刊的最佳定位，判断哪些结果应进入主文，哪些应下沉为附录，哪些应删除。",
        "2. 学习近期已接收论文的表述和篇幅分布，重写摘要、引言、相关工作、主结果陈述与结论。",
        "3. 将核心贡献压缩成少数强结论，突出最令人信服和最有发表价值的结论，不要挤牙膏式追加。",
        "4. 对证明叙事做取舍：正文只保留支撑主结论的关键论证脉络，避免重复已有公开证明套路。",
        "5. 调整附录比例与组织，使全文更接近期刊真实已发表文章的结构习惯。",
        "6. 给出一版编辑视角下可接受的完整优化结果，而不是停留在粗糙纲要。",
        "",
        "## Output Requirements",
        "- 直接输出可执行的全面修订方案与重构后的文章框架。",
        "- 只保留有发表价值的最终结论，不输出中间试探性结论。",
        "- 若删改原结构，请解释新的叙事主线如何更符合目标期刊。",
    ]
    if recent_paper_notes:
        lines.extend(["", "## Recent Accepted Paper Notes", recent_paper_notes])
    else:
        lines.extend(
            [
                "",
                "## Recent Accepted Paper Notes",
                "请先自行检索并阅读目标期刊近期被接收论文，再据此重构语言、篇幅比例和附录组织。",
            ]
        )
    if editorial_notes:
        lines.extend(["", "## Editorial Notes", editorial_notes])
    return "\n".join(lines) + "\n"


def render_research_extension_prompt(profile: dict[str, Any], recent_paper_notes: str) -> str:
    lines = [
        f"# Research Extension Prompt for {profile['journal']}",
        "",
        "## Role",
        (
            "你需要基于当前稿件继续向前研究，直到识别出足以显著提升投稿价值的深刻结论。"
            "只有出现可发表、非低增量、非重复公开文献的结果后才停止。"
        ),
        "",
        "## Research Constraints",
        "1. 不要重复本文已写出的内容，不要重复他人已经公开发表的推理过程、定理、命题、推论、猜想和证明。",
        "2. 可以调用他人成果，但仅作为前提、工具或背景，并为正式引用保留位置。",
        "3. 不要给出中间过程结果，不要用碎片化、未收敛的结论充数。",
        "4. 必须优先寻找足以惊艳严肃审稿人的深刻结论，并解释其相对现有稿件的真实增益。",
        "5. 表述必须学术化、紧凑、克制，避免口语和宣传语气。",
        "",
        "## Source Priorities",
        f"- Current claims: {profile['claims_total']}",
        f"- Current missing labeled claims: {profile['missing_labels_total']}",
        f"- Priority frontier labels: {', '.join(profile.get('frontier_labels', [])[:12]) or 'none'}",
        "",
        "## Required Output",
        "- 只报告真正有发表价值的新结论、其必要假设、与现有稿件的差异、以及为什么值得进入目标期刊版本。",
        "- 如果现有结果还不足支撑目标期刊定位，请明确指出必须补强的理论缺口，而不是给温和评价。",
        "- 新增结论必须能够服务主叙事，而不是制造旁支。",
    ]
    if recent_paper_notes:
        lines.extend(["", "## Recent Accepted Paper Notes", recent_paper_notes])
    return "\n".join(lines) + "\n"


def render_editorial_review_prompt(profile: dict[str, Any], editorial_notes: str) -> str:
    lines = [
        f"# Editorial Review Prompt for {profile['journal']}",
        "",
        "## Role",
        f"请以 {profile['journal']} 编辑和严格审稿人的标准审阅当前稿件，并给出明确结论：Accept / Minor Revision / Major Revision / Reject。",
        "",
        "## Review Standard",
        "1. 不要泛泛而谈，先给出会阻止接收的核心问题，再给次级问题。",
        "2. 重点检查贡献的新颖性、叙事密度、结构成熟度、文献定位、证明取舍、附录比例以及语言是否像真实已发表论文。",
        "3. 若不接收，必须明确说明为何当前稿件尚未达到编辑允许送外审或接收的标准。",
        "4. 若勉强可接收，也必须指出残余风险和需要最终清理的部分。",
        "",
        "## Required Output Shape",
        "- Decision",
        "- Fatal issues",
        "- Non-fatal but necessary revisions",
        "- Whether the manuscript now looks like a real paper for this journal rather than an AI-produced draft",
        "- Final acceptance likelihood after one more strong revision pass",
    ]
    if editorial_notes:
        lines.extend(["", "## Editorial Notes", editorial_notes])
    return "\n".join(lines) + "\n"


def render_journal_workflow_markdown(profile: dict[str, Any]) -> str:
    recon_command = (
        f"python3 automation/journal_recon.py run --journal \"{profile['journal']}\""
        + (f" --journal-short {profile['journal_short']}" if profile.get("journal_short") else "")
        + f" --max-papers {profile.get('recon_max_papers', 6)}"
        + f" --years-back {profile.get('recon_years_back', 3)}"
        + f" --slug {slugify(profile.get('journal_short') or profile['journal'])}"
    )
    step_one = "1. Review `recent_paper_notes.md` and tighten its takeaways after reading the sampled recent papers."
    if not profile.get("recent_paper_notes_provided"):
        step_one = (
            "1. Run journal reconnaissance first to seed recent-paper notes: "
            f"`{recon_command}`."
        )
    lines = [
        f"# Journal Workflow: {profile['journal']}",
        "",
        step_one,
        "2. Fill `editorial_notes_template.md` with venue-specific red flags, desired appendix ratio, and positioning constraints.",
        "3. Run the deep revision prompt to restructure the manuscript around a smaller set of stronger conclusions.",
        "4. Run the research extension prompt only after the narrative spine is stable; add only results that materially raise publication value.",
        "5. Run the editorial review prompt as a hard gate. If the answer is not at least close to accept, iterate again instead of polishing surface language.",
        "6. Before final submission, ensure the main text / appendix split, citation style, and theorem presentation match the journal's recent accepted papers rather than generic templates.",
        "",
        "## Local Source References",
        f"- Source directory: `{profile['source_dir']}`",
        f"- Source slug: `{profile['source_slug']}`",
        f"- Claims total: {profile['claims_total']}",
        f"- Missing labeled claims: {profile['missing_labels_total']}",
        f"- Recon notes path: `{profile.get('recon_notes_path') or 'none'}`",
    ]
    return "\n".join(lines) + "\n"


def render_submission_checklist(profile: dict[str, Any]) -> str:
    lines = [
        f"# Submission Checklist: {profile['journal']}",
        "",
        "- The abstract reads like the target journal rather than a generic AI summary.",
        "- The introduction states one clear editorial narrative and does not diffuse attention across too many side claims.",
        "- The strongest results are in the main text; weaker or technical material is moved to appendices or removed.",
        "- No section is kept solely because it was already written.",
        "- The paper does not restate publicly known proof patterns as if they were new contributions.",
        "- Related work is selective, strategic, and positioned against the target journal's actual discourse.",
        "- The appendix / main-body ratio is aligned with recent accepted papers in the target journal.",
        "- The manuscript answers the question: why this paper belongs in this journal rather than a neighboring venue.",
        "- A strict editorial self-review still gives at least a plausible path to acceptance.",
    ]
    return "\n".join(lines) + "\n"


def build_journal_pack_manifest(*, output_dir: Path, profile: dict[str, Any], copied_files: list[str]) -> dict[str, Any]:
    return {
        "journal": profile["journal"],
        "journal_short": profile["journal_short"],
        "source_type": profile["source_type"],
        "source_dir": profile["source_dir"],
        "source_slug": profile["source_slug"],
        "output_dir": str(output_dir),
        "claims_total": profile["claims_total"],
        "missing_labels_total": profile["missing_labels_total"],
        "files": copied_files,
    }


def create_journal_pack(
    *,
    source_dir: Path,
    journal: str,
    journal_short: str,
    article_type: str,
    paper_language: str,
    positioning: str,
    scope_fit: str,
    recent_paper_notes_file: Path | None,
    recon_dir: Path | None,
    auto_recon: bool,
    recon_max_papers: int,
    recon_years_back: int,
    editorial_notes_file: Path | None,
    batch_dashboard_path: Path | None,
    output_dir: Path | None,
    pack_slug: str | None,
) -> dict[str, Any]:
    source = load_research_source(source_dir)
    resolved_slug = pack_slug or slugify(f"{journal}_{source_slug(source)}")
    target_dir = output_dir.resolve() if output_dir else default_journal_pack_dir(resolved_slug)
    target_dir.mkdir(parents=True, exist_ok=True)

    recent_paper_notes = read_optional_text(recent_paper_notes_file)
    recon_notes_path: Path | None = None
    resolved_recon_dir = recon_dir.resolve() if recon_dir else None
    auto_recon_attempted = False
    auto_recon_error = ""
    auto_recon_succeeded = False
    if not recent_paper_notes:
        recent_paper_notes, recon_notes_path = load_recon_notes(
            journal=journal,
            journal_short=journal_short,
            recon_dir=recon_dir,
        )
        if recon_notes_path is not None:
            resolved_recon_dir = recon_notes_path.parent.resolve()
    if not recent_paper_notes and auto_recon:
        auto_recon_attempted = True
        recent_paper_notes, recon_notes_path, resolved_recon_dir, auto_recon_error = auto_fill_recon_notes(
            journal=journal,
            journal_short=journal_short,
            recon_dir=resolved_recon_dir,
            max_papers=recon_max_papers,
            years_back=recon_years_back,
        )
        auto_recon_succeeded = bool(recent_paper_notes)
    editorial_notes = read_optional_text(editorial_notes_file)
    profile = build_journal_profile(
        source=source,
        journal=journal,
        journal_short=journal_short,
        article_type=article_type,
        paper_language=paper_language,
        positioning=positioning,
        scope_fit=scope_fit,
        recent_paper_notes=recent_paper_notes,
        recon_notes_path=str(recon_notes_path) if recon_notes_path else "",
        recon_dir=str(resolved_recon_dir) if resolved_recon_dir else "",
        auto_recon_attempted=auto_recon_attempted,
        auto_recon_succeeded=auto_recon_succeeded or bool(recon_notes_path),
        auto_recon_error=auto_recon_error,
        recon_max_papers=recon_max_papers,
        recon_years_back=recon_years_back,
        editorial_notes=editorial_notes,
    )
    batch_dashboard = load_batch_dashboard(batch_dashboard_path)
    boundary_profile, keep_drop_matrix = build_keep_drop_matrix(
        source=source,
        dashboard=batch_dashboard,
        journal=journal,
    )

    write_json(target_dir / "journal_profile.json", profile)
    (target_dir / "journal_brief.md").write_text(render_journal_brief_markdown(profile), encoding="utf-8")
    (target_dir / "deep_revision_prompt.md").write_text(
        render_deep_revision_prompt(profile, recent_paper_notes, editorial_notes),
        encoding="utf-8",
    )
    (target_dir / "research_extension_prompt.md").write_text(
        render_research_extension_prompt(profile, recent_paper_notes),
        encoding="utf-8",
    )
    (target_dir / "editorial_review_prompt.md").write_text(
        render_editorial_review_prompt(profile, editorial_notes),
        encoding="utf-8",
    )
    write_json(target_dir / "boundary_profile.json", boundary_profile)
    write_json(
        target_dir / "keep_drop_matrix.json",
        {"boundary_profile": boundary_profile, "sections": keep_drop_matrix},
    )
    (target_dir / "boundary_report.md").write_text(
        render_boundary_report(boundary_profile, keep_drop_matrix),
        encoding="utf-8",
    )
    (target_dir / "split_strategy.md").write_text(
        render_split_strategy(boundary_profile, keep_drop_matrix),
        encoding="utf-8",
    )
    (target_dir / "boundary_gate_prompt.md").write_text(
        render_boundary_gate_prompt(boundary_profile, keep_drop_matrix),
        encoding="utf-8",
    )
    (target_dir / "workflow.md").write_text(render_journal_workflow_markdown(profile), encoding="utf-8")
    (target_dir / "submission_checklist.md").write_text(render_submission_checklist(profile), encoding="utf-8")
    (target_dir / "recent_paper_notes_template.md").write_text(
        render_recent_paper_notes_template(
            journal=journal,
            journal_short=journal_short,
            article_type=article_type,
        ),
        encoding="utf-8",
    )
    (target_dir / "editorial_notes_template.md").write_text(
        render_editorial_notes_template(journal=journal),
        encoding="utf-8",
    )
    copied_files = list(REQUIRED_JOURNAL_PACK_FILES)
    if recent_paper_notes:
        (target_dir / "recent_paper_notes.md").write_text(recent_paper_notes + "\n", encoding="utf-8")
        copied_files.append("recent_paper_notes.md")
    if editorial_notes:
        (target_dir / "editorial_notes.md").write_text(editorial_notes + "\n", encoding="utf-8")
        copied_files.append("editorial_notes.md")
    if resolved_recon_dir is not None and resolved_recon_dir.is_dir():
        for name in ("recon_profile.json", "recent_papers.json", "style_summary.md"):
            source_path = resolved_recon_dir / name
            if source_path.is_file():
                (target_dir / name).write_text(source_path.read_text(encoding="utf-8"), encoding="utf-8")
                copied_files.append(name)
    copied_files = list(dict.fromkeys(copied_files))
    write_json(
        target_dir / "journal_pack_manifest.json",
        build_journal_pack_manifest(output_dir=target_dir, profile=profile, copied_files=copied_files),
    )

    ok, errors = validate_journal_pack_dir(target_dir)
    if not ok:
        raise RuntimeError("; ".join(errors))
    print(
        "[research-cycle] journal-pack:"
        f" journal={journal!r}"
        f" slug={resolved_slug}"
        f" source_type={profile['source_type']}"
        f" claims={profile['claims_total']}"
        f" missing_labels={profile['missing_labels_total']}"
        f" output={target_dir}"
    )
    return {
        "output_dir": str(target_dir),
        "pack_slug": resolved_slug,
    }


def default_batch_sections() -> list[str]:
    body_root = paper_root() / "sections" / "body"
    sections: list[str] = []
    for path in sorted(body_root.iterdir()):
        if path.is_dir() and (path / "main.tex").is_file():
            sections.append(f"body/{path.name}")
    return sections


def render_dashboard_markdown(*, batch_slug: str, sections: list[dict[str, Any]], failures: list[dict[str, str]]) -> str:
    total_claims = sum(int(item["claims_total"]) for item in sections)
    total_missing = sum(int(item["missing_labels_total"]) for item in sections)
    total_matched = sum(int(item["matched_labels_total"]) for item in sections)
    lines = [
        f"# Research Cycle Batch: {batch_slug}",
        "",
        f"- Successful sections: {len(sections)}",
        f"- Failed sections: {len(failures)}",
        f"- Claim environments: {total_claims}",
        f"- Exact Lean label matches: {total_matched}",
        f"- Missing Lean labels: {total_missing}",
        "",
        "## Section Summary",
    ]
    if sections:
        for item in sorted(sections, key=lambda value: (-int(value["missing_labels_total"]), str(value["section"]))):
            lines.append(
                "- "
                f"`{item['section']}` -> claims={item['claims_total']}, "
                f"matched={item['matched_labels_total']}, "
                f"missing={item['missing_labels_total']}, "
                f"cycle=`{item['cycle_dir']}`"
            )
            lines.append(
                "  "
                f"seed with `python3 automation/research_cycle.py seed-paper \"{item['cycle_dir']}\"`"
            )
    else:
        lines.append("- No sections completed successfully.")

    lines.extend(["", "## Failures"])
    if failures:
        for failure in failures:
            lines.append(f"- `{failure['section']}` :: {failure['error']}")
    else:
        lines.append("- None")
    return "\n".join(lines) + "\n"


def write_batch_dashboard(
    *,
    output_dir: Path,
    batch_slug: str,
    sections: list[dict[str, Any]],
    failures: list[dict[str, str]],
) -> dict[str, Any]:
    payload = {
        "batch_slug": batch_slug,
        "sections_total": len(sections),
        "failures_total": len(failures),
        "claims_total": sum(int(item["claims_total"]) for item in sections),
        "matched_labels_total": sum(int(item["matched_labels_total"]) for item in sections),
        "missing_labels_total": sum(int(item["missing_labels_total"]) for item in sections),
        "sections": sections,
        "failures": failures,
    }
    write_json(output_dir / "dashboard.json", payload)
    (output_dir / "dashboard.md").write_text(
        render_dashboard_markdown(batch_slug=batch_slug, sections=sections, failures=failures),
        encoding="utf-8",
    )
    return payload


def tex_escape(text: str) -> str:
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(ch, ch) for ch in text)


def seed_text(text: str, fallback: str = "see source label") -> str:
    cleaned = NON_ASCII_RE.sub(" ", text)
    cleaned = re.sub(r"\s+", " ", cleaned).strip()
    return cleaned or fallback


def resolved_bib_subset(citation_keys: Iterable[str], bib_entries: dict[str, str]) -> dict[str, str]:
    subset: dict[str, str] = {}
    for key in citation_keys:
        if key in bib_entries and key not in subset:
            subset[key] = bib_entries[key]
    return subset


def render_seed_main_tex(*, title: str, include_bibliography: bool) -> str:
    lines = [
        r"\documentclass[11pt]{article}",
        r"\usepackage[margin=1in]{geometry}",
        r"\usepackage{amsmath,amssymb,amsthm}",
        r"\usepackage{hyperref}",
        r"\usepackage[T1]{fontenc}",
        "",
        r"\theoremstyle{plain}",
        r"\newtheorem{theorem}{Theorem}[section]",
        r"\newtheorem{lemma}[theorem]{Lemma}",
        r"\newtheorem{proposition}[theorem]{Proposition}",
        r"\newtheorem{corollary}[theorem]{Corollary}",
        r"\newtheorem{conjecture}[theorem]{Conjecture}",
        r"\theoremstyle{definition}",
        r"\newtheorem{definition}[theorem]{Definition}",
        r"\theoremstyle{remark}",
        r"\newtheorem{remark}[theorem]{Remark}",
        "",
        rf"\title{{{tex_escape(title)}}}",
        r"\author{Automath Research Cycle Seed}",
        r"\date{\today}",
        "",
        r"\begin{document}",
        r"\maketitle",
        r"\tableofcontents",
        "",
        r"\input{sections/source_slice.tex}",
        r"\input{sections/formalization_frontier.tex}",
        r"\input{sections/literature_seed.tex}",
        r"\input{sections/verification_plan.tex}",
    ]
    if include_bibliography:
        lines.extend(
            [
                "",
                r"\bibliographystyle{amsplain}",
                r"\bibliography{references}",
            ]
        )
    lines.extend(["", r"\end{document}", ""])
    return "\n".join(lines)


def render_seed_section(
    *,
    kind: str,
    slice_manifest: dict[str, Any],
    cycle_report: dict[str, Any],
    backlog: dict[str, Any],
    literature_queries: list[str],
    resolved_citation_keys: list[str],
) -> str:
    headings = slice_manifest.get("headings", [])
    claims = slice_manifest.get("claims", [])
    citation_keys = slice_manifest.get("citation_keys", [])
    missing_claims = backlog.get("missing_claims", [])
    slice_name = seed_text(
        str(slice_manifest.get("slice_name") or cycle_report.get("slice_name") or slice_manifest.get("slice_slug") or "Research Slice"),
        fallback=str(slice_manifest.get("slice_slug") or "research slice"),
    )

    if kind == "source_slice":
        lines = [
            r"\section{Source Slice}",
            (
                "This draft seed was generated from "
                rf"\texttt{{{tex_escape(str(slice_manifest.get('entry_file', '')))}}} "
                f"and currently spans {int(cycle_report.get('tex_files_total', 0))} TeX files "
                f"with {int(cycle_report.get('claims_total', 0))} theorem-like environments."
            ),
            "",
            r"\subsection{Scope}",
            rf"\textbf{{Working slice}}: {tex_escape(slice_name)}.",
            "",
            r"\subsection{Headings}",
            r"\begin{itemize}",
        ]
        for heading in headings[:15]:
            lines.append(
                r"\item "
                + rf"{tex_escape(seed_text(str(heading.get('title', '')), fallback='untitled heading'))} "
                + rf"(\texttt{{{tex_escape(str(heading.get('file', '')))}:{heading.get('line', 0)}}})"
            )
        if not headings:
            lines.append(r"\item No headings extracted.")
        lines.extend([r"\end{itemize}", "", r"\subsection{Anchor Claims}", r"\begin{itemize}"])
        for claim in claims[:12]:
            label = str(claim.get("label") or "<unlabeled>")
            title = seed_text(str(claim.get("title") or claim.get("summary") or ""), fallback="see source claim")
            lines.append(
                r"\item "
                + rf"[{tex_escape(str(claim.get('environment', 'claim')))}] "
                + rf"\texttt{{{tex_escape(label)}}}: {tex_escape(title)}"
            )
        if not claims:
            lines.append(r"\item No claim environments extracted.")
        lines.extend([r"\end{itemize}", ""])
        return "\n".join(lines)

    if kind == "formalization_frontier":
        lines = [
            r"\section{Formalization Frontier}",
            (
                f"The current slice has {int(backlog.get('matched_labels_total', 0))} exact Lean label matches "
                f"and {int(backlog.get('missing_labels_total', 0))} missing labeled claims."
            ),
            "",
            r"\subsection{Immediate Missing Claims}",
            r"\begin{enumerate}",
        ]
        for claim in missing_claims[:12]:
            label = str(claim.get("label") or "<unlabeled>")
            title = seed_text(str(claim.get("title") or claim.get("summary") or ""), fallback="see source claim")
            lines.append(
                r"\item "
                + rf"\texttt{{{tex_escape(label)}}} "
                + rf"([{tex_escape(str(claim.get('environment', 'claim')))}]) "
                + rf"from \texttt{{{tex_escape(str(claim.get('file', '')))}:{claim.get('line', 0)}}}. "
                + tex_escape(title)
            )
            suggestions = claim.get("suggestions", [])
            if suggestions:
                joined = ", ".join(
                    rf"\texttt{{{tex_escape(str(item.get('name', '')))}}}"
                    for item in suggestions[:3]
                )
                lines.append(r"\\ Suggested Lean anchors: " + joined + ".")
        if not missing_claims:
            lines.append(r"\item No missing labeled claims detected for this slice.")
        lines.extend([r"\end{enumerate}", ""])
        return "\n".join(lines)

    if kind == "literature_seed":
        lines = [
            r"\section{Literature Seed}",
            (
                "The source slice cites "
                f"{len(citation_keys)} local bibliography keys, with {len(resolved_citation_keys)} copied into this seed, "
                f"and suggests {len(literature_queries)} survey queries."
            ),
        ]
        if resolved_citation_keys:
            cite_keys = ",".join(str(key) for key in resolved_citation_keys[:20])
            lines.extend(["", rf"Key local citations to inspect first: \cite{{{cite_keys}}}."])
        lines.extend(["", r"\subsection{Suggested Survey Queries}", r"\begin{itemize}"])
        for query in literature_queries[:15]:
            lines.append(r"\item " + tex_escape(seed_text(query, fallback="use source labels and headings")))
        if not literature_queries:
            lines.append(r"\item No query candidates extracted.")
        lines.extend([r"\end{itemize}", ""])
        return "\n".join(lines)

    if kind == "verification_plan":
        slice_slug = str(slice_manifest.get("slice_slug") or "research_cycle")
        lines = [
            r"\section{Verification Plan}",
            r"\begin{enumerate}",
            r"\item Formalize the first missing labels listed in Section 2 and re-run \texttt{python lean4/scripts/omega\_ci.py inventory --strict}.",
            r"\item Track coverage drift with \texttt{python lean4/scripts/omega\_ci.py paper-coverage --sections body}.",
            r"\item After experiment-side edits, run \texttt{python3 automation/run\_all.py} and validate with \texttt{python3 automation/pipeline\_contract.py validate}.",
            r"\item Regenerate this cycle packet or a newer one before merging a new paper branch.",
            r"\end{enumerate}",
            "",
            rf"\textbf{{Source packet}}: \texttt{{artifacts/export/research\_cycles/{tex_escape(slice_slug)}/}}.",
            "",
        ]
        return "\n".join(lines)

    raise ValueError(f"Unsupported seed section kind: {kind}")


def seed_paper_from_cycle(
    *,
    cycle_dir: Path,
    output_dir: Path | None,
    seed_slug: str | None,
    title: str | None,
) -> dict[str, Any]:
    packet = load_cycle_packet(cycle_dir)
    slice_manifest = packet["slice_manifest"]
    cycle_report = packet["cycle_report"]
    backlog = packet["formalization_backlog"]
    resolved_slug = seed_slug or f"{slice_manifest.get('slice_slug', 'research_cycle')}_seed"
    target_dir = output_dir.resolve() if output_dir else default_seed_dir(resolved_slug)
    sections_dir = target_dir / "sections"
    sections_dir.mkdir(parents=True, exist_ok=True)

    bibliography = parse_bib_entries(paper_root() / "references.bib")
    citation_keys = list(slice_manifest.get("citation_keys", []))
    resolved_entries = resolved_bib_subset(citation_keys, bibliography)
    literature_queries = list(slice_manifest.get("literature_queries", []))
    base_title = seed_text(
        str(slice_manifest.get("slice_name", "")),
        fallback=str(slice_manifest.get("slice_slug", "research_cycle")),
    )
    seed_title = title or f"Seed Draft from {base_title}"
    seed_title = seed_text(seed_title, fallback=f"Seed Draft from {slice_manifest.get('slice_slug', 'research_cycle')}")

    (target_dir / "main.tex").write_text(
        render_seed_main_tex(title=seed_title, include_bibliography=bool(resolved_entries)),
        encoding="utf-8",
    )
    (sections_dir / "source_slice.tex").write_text(
        render_seed_section(
            kind="source_slice",
            slice_manifest=slice_manifest,
            cycle_report=cycle_report,
            backlog=backlog,
            literature_queries=literature_queries,
            resolved_citation_keys=list(resolved_entries),
        ),
        encoding="utf-8",
    )
    (sections_dir / "formalization_frontier.tex").write_text(
        render_seed_section(
            kind="formalization_frontier",
            slice_manifest=slice_manifest,
            cycle_report=cycle_report,
            backlog=backlog,
            literature_queries=literature_queries,
            resolved_citation_keys=list(resolved_entries),
        ),
        encoding="utf-8",
    )
    (sections_dir / "literature_seed.tex").write_text(
        render_seed_section(
            kind="literature_seed",
            slice_manifest=slice_manifest,
            cycle_report=cycle_report,
            backlog=backlog,
            literature_queries=literature_queries,
            resolved_citation_keys=list(resolved_entries),
        ),
        encoding="utf-8",
    )
    (sections_dir / "verification_plan.tex").write_text(
        render_seed_section(
            kind="verification_plan",
            slice_manifest=slice_manifest,
            cycle_report=cycle_report,
            backlog=backlog,
            literature_queries=literature_queries,
            resolved_citation_keys=list(resolved_entries),
        ),
        encoding="utf-8",
    )
    if resolved_entries:
        (target_dir / "references.bib").write_text(
            "\n\n".join(entry.strip() for entry in resolved_entries.values()) + "\n",
            encoding="utf-8",
        )
    readme_lines = [
        f"# Seed Draft: {seed_title}",
        "",
        f"- Source cycle: `{packet['path']}`",
        f"- Slice entry: `{slice_manifest.get('entry_file', '')}`",
        f"- Missing labels carried forward: {backlog.get('missing_labels_total', 0)}",
        f"- Resolved bibliography entries copied: {len(resolved_entries)}",
        "",
        "Build locally with:",
        "",
        "```bash",
        "pdflatex -interaction=nonstopmode -halt-on-error -file-line-error main.tex",
        "```",
        "",
    ]
    (target_dir / "README.md").write_text("\n".join(readme_lines), encoding="utf-8")
    write_json(
        target_dir / "seed_manifest.json",
        {
            "seed_slug": resolved_slug,
            "seed_title": seed_title,
            "source_cycle_dir": str(packet["path"]),
            "source_slice_slug": slice_manifest.get("slice_slug"),
            "source_entry_file": slice_manifest.get("entry_file"),
            "missing_labels_total": backlog.get("missing_labels_total", 0),
            "claims_total": cycle_report.get("claims_total", 0),
            "resolved_bibliography_total": len(resolved_entries),
            "files": [
                "main.tex",
                "sections/source_slice.tex",
                "sections/formalization_frontier.tex",
                "sections/literature_seed.tex",
                "sections/verification_plan.tex",
                "README.md",
                "seed_manifest.json",
            ]
            + (["references.bib"] if resolved_entries else []),
        },
    )
    print(
        "[research-cycle] seed-paper:"
        f" cycle={packet['path']}"
        f" slug={resolved_slug}"
        f" resolved_bib={len(resolved_entries)}"
        f" output={target_dir}"
    )
    return {
        "output_dir": str(target_dir),
        "seed_slug": resolved_slug,
        "resolved_bibliography_total": len(resolved_entries),
    }


def cmd_create(args: argparse.Namespace) -> int:
    try:
        if bool(args.section) == bool(args.sections):
            raise RuntimeError("Provide exactly one of --section or --sections")
        if args.sections:
            create_multi_cycle_packet(
                sections=list(args.sections),
                slice_slug=args.slug,
                output_dir=Path(args.output_dir) if args.output_dir else None,
                top_suggestions=args.top_suggestions,
            )
        else:
            create_cycle_packet(
                section=args.section,
                slice_slug=args.slug,
                output_dir=Path(args.output_dir) if args.output_dir else None,
                top_suggestions=args.top_suggestions,
            )
    except Exception as exc:
        print(f"[research-cycle] create failed: {exc}", file=sys.stderr)
        return 1
    return 0


def cmd_batch(args: argparse.Namespace) -> int:
    sections = args.sections or default_batch_sections()
    batch_slug = args.slug or "body_batch"
    output_dir = Path(args.output_dir).resolve() if args.output_dir else default_batch_output_dir(batch_slug)
    cycles_dir = output_dir / "cycles"
    cycles_dir.mkdir(parents=True, exist_ok=True)
    omega_ci = load_omega_ci()
    formalization_context = build_formalization_context(omega_ci)

    successes: list[dict[str, Any]] = []
    failures: list[dict[str, str]] = []
    for section in sections:
        try:
            entry = section_entry(section)
            cycle_slug = slugify(relative_to_paper(entry).replace("/", "_"))
            packet = create_cycle_packet(
                section=section,
                slice_slug=cycle_slug,
                output_dir=cycles_dir / cycle_slug,
                top_suggestions=args.top_suggestions,
                omega_ci=omega_ci,
                formalization_context=formalization_context,
            )
            report = packet["cycle_report"]
            successes.append(
                {
                    "section": section,
                    "slice_slug": packet["slice_slug"],
                    "slice_name": packet["slice_name"],
                    "cycle_dir": packet["output_dir"],
                    "claims_total": report["claims_total"],
                    "matched_labels_total": report["matched_labels_total"],
                    "missing_labels_total": report["missing_labels_total"],
                    "reasoning_frontier_total": report["reasoning_frontier_total"],
                }
            )
        except Exception as exc:
            failures.append({"section": section, "error": str(exc)})
            print(f"[research-cycle] batch failed for {section}: {exc}", file=sys.stderr)

    payload = write_batch_dashboard(
        output_dir=output_dir,
        batch_slug=batch_slug,
        sections=successes,
        failures=failures,
    )
    print(
        "[research-cycle] batch:"
        f" slug={batch_slug}"
        f" sections={payload['sections_total']}"
        f" failures={payload['failures_total']}"
        f" missing_labels={payload['missing_labels_total']}"
        f" output={output_dir}"
    )
    return 0 if not failures else 1


def cmd_seed_paper(args: argparse.Namespace) -> int:
    try:
        seed_paper_from_cycle(
            cycle_dir=Path(args.cycle_dir),
            output_dir=Path(args.output_dir) if args.output_dir else None,
            seed_slug=args.slug,
            title=args.title,
        )
    except Exception as exc:
        print(f"[research-cycle] seed-paper failed: {exc}", file=sys.stderr)
        return 1
    return 0


def cmd_journal_pack(args: argparse.Namespace) -> int:
    try:
        create_journal_pack(
            source_dir=Path(args.source_dir),
            journal=args.journal,
            journal_short=args.journal_short or "",
            article_type=args.article_type,
            paper_language=args.paper_language,
            positioning=args.positioning or "",
            scope_fit=args.scope_fit or "",
            recent_paper_notes_file=Path(args.recent_paper_notes_file) if args.recent_paper_notes_file else None,
            recon_dir=Path(args.recon_dir) if args.recon_dir else None,
            auto_recon=not args.skip_auto_recon,
            recon_max_papers=args.recon_max_papers,
            recon_years_back=args.recon_years_back,
            editorial_notes_file=Path(args.editorial_notes_file) if args.editorial_notes_file else None,
            batch_dashboard_path=Path(args.batch_dashboard) if args.batch_dashboard else None,
            output_dir=Path(args.output_dir) if args.output_dir else None,
            pack_slug=args.slug,
        )
    except Exception as exc:
        print(f"[research-cycle] journal-pack failed: {exc}", file=sys.stderr)
        return 1
    return 0


def cmd_validate(args: argparse.Namespace) -> int:
    target = Path(args.path).resolve()
    ok, errors = validate_cycle_dir(target)
    print(
        "[research-cycle] validate:"
        f" path={target}"
        f" ok={ok}"
        f" errors={len(errors)}"
    )
    for error in errors[:50]:
        print(f"  {error}")
    return 0 if ok else 1


def cmd_validate_journal_pack(args: argparse.Namespace) -> int:
    target = Path(args.path).resolve()
    ok, errors = validate_journal_pack_dir(target)
    print(
        "[research-cycle] validate-journal-pack:"
        f" path={target}"
        f" ok={ok}"
        f" errors={len(errors)}"
    )
    for error in errors[:50]:
        print(f"  {error}")
    return 0 if ok else 1


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Automate one paper -> formalization -> literature cycle")
    sub = p.add_subparsers(dest="command", required=True)

    create_p = sub.add_parser("create", help="Generate a research cycle packet from one paper slice")
    create_p.add_argument(
        "--section",
        help="Section path, for example body/folding or sections/body/folding/main.tex",
    )
    create_p.add_argument(
        "--sections",
        nargs="+",
        help="Merge multiple sections into one research cycle packet",
    )
    create_p.add_argument("--slug", help="Override output slug")
    create_p.add_argument("--output-dir", help="Override output directory")
    create_p.add_argument(
        "--top-suggestions",
        type=int,
        default=3,
        help="How many Lean search suggestions to keep per missing claim",
    )
    create_p.set_defaults(func=cmd_create)

    batch_p = sub.add_parser("batch", help="Generate research cycle packets for multiple sections")
    batch_p.add_argument(
        "--sections",
        nargs="+",
        help="Explicit section list; default is every body/* directory with a main.tex",
    )
    batch_p.add_argument("--slug", help="Batch slug for dashboard output")
    batch_p.add_argument("--output-dir", help="Override batch output directory")
    batch_p.add_argument(
        "--top-suggestions",
        type=int,
        default=3,
        help="How many Lean search suggestions to keep per missing claim",
    )
    batch_p.set_defaults(func=cmd_batch)

    seed_p = sub.add_parser("seed-paper", help="Create a standalone draft seed from one cycle directory")
    seed_p.add_argument("cycle_dir", help="Path to a generated research cycle directory")
    seed_p.add_argument("--slug", help="Override seed slug")
    seed_p.add_argument("--title", help="Override seed paper title")
    seed_p.add_argument("--output-dir", help="Override seed output directory")
    seed_p.set_defaults(func=cmd_seed_paper)

    journal_p = sub.add_parser("journal-pack", help="Generate a journal-targeted prompt pack from one cycle or seed")
    journal_p.add_argument("source_dir", help="Path to a generated research cycle or paper seed directory")
    journal_p.add_argument("--journal", required=True, help="Target journal name")
    journal_p.add_argument("--journal-short", help="Journal abbreviation or short name")
    journal_p.add_argument(
        "--article-type",
        default="research article",
        help="Target submission type, for example research article or short note",
    )
    journal_p.add_argument(
        "--paper-language",
        default="English",
        help="Target manuscript language",
    )
    journal_p.add_argument("--positioning", help="One-line positioning for this journal")
    journal_p.add_argument("--scope-fit", help="Why this manuscript fits the journal")
    journal_p.add_argument(
        "--recent-paper-notes-file",
        help="Optional path to manually prepared notes from recent accepted papers",
    )
    journal_p.add_argument(
        "--recon-dir",
        help="Optional journal reconnaissance directory; if present, journal-pack auto-loads recent_paper_notes.md",
    )
    journal_p.add_argument(
        "--skip-auto-recon",
        action="store_true",
        help="Do not run online journal reconnaissance when recent-paper notes are missing",
    )
    journal_p.add_argument(
        "--recon-max-papers",
        type=int,
        default=6,
        help="How many recent papers the auto reconnaissance step should sample",
    )
    journal_p.add_argument(
        "--recon-years-back",
        type=int,
        default=3,
        help="How many years back the auto reconnaissance step should query",
    )
    journal_p.add_argument(
        "--editorial-notes-file",
        help="Optional path to extra editorial constraints or house-style notes",
    )
    journal_p.add_argument(
        "--batch-dashboard",
        help="Optional batch dashboard.json or batch directory for section split / boundary analysis",
    )
    journal_p.add_argument("--slug", help="Override output slug")
    journal_p.add_argument("--output-dir", help="Override output directory")
    journal_p.set_defaults(func=cmd_journal_pack)

    validate_p = sub.add_parser("validate", help="Validate one generated research cycle directory")
    validate_p.add_argument("path", help="Path to a generated research cycle directory")
    validate_p.set_defaults(func=cmd_validate)

    validate_journal_p = sub.add_parser("validate-journal-pack", help="Validate one generated journal-pack directory")
    validate_journal_p.add_argument("path", help="Path to a generated journal-pack directory")
    validate_journal_p.set_defaults(func=cmd_validate_journal_pack)
    return p


def main() -> int:
    args = parser().parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
