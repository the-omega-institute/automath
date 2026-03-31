#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Synchronize an external publication workspace into local automation artifacts."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from automation_paths import export_dir, paper_root


DIR_TOKEN_RE = re.compile(r"`((?:submitted_)?2026_[^`]+)`")
SECTION_PATH_RE = re.compile(r"sections/body/([A-Za-z0-9_]+)/")
SECTION_INLINE_RE = re.compile(r"`([A-Za-z0-9_]+)/`")
TITLE_RE = re.compile(r"^#\s+(.+)$", re.MULTILINE)
EN_JOURNAL_RE = re.compile(
    r"(?mi)^\s*-\s*(?:Primary target journal|Secondary targets|Target journal)\s*:\s*`?([^`\n]+?)`?\s*$"
)
ZH_JOURNAL_RE = re.compile(
    r"(?mi)^\s*-\s*(?:目标风格|目标期刊)\s*[:：]\s*`?([^`\n]+?)`?\s*$"
)
TRACK_RE = re.compile(r"^-\s*Track code:\s*`?([^`\n]+?)`?\s*$", re.MULTILINE)
REQUIRED_SYNC_FILES = (
    "sync_manifest.json",
    "publication_inventory.json",
    "section_status.json",
    "lean_linkage.json",
    "publication_audit.json",
    "publication_audit_report.md",
    "publication_sync_report.md",
)
PROGRAM_ACTIONS = {
    "submitted": "support_existing_submission",
    "planned_batch_1": "support_priority_publication",
    "planned_batch_2": "prepare_after_batch_1",
    "planned_batch_3": "defer_until_upstream_feedback",
    "archived": "keep_archived_only",
    "frozen": "hold_no_independent_project",
    "unassigned": "needs_program_decision",
}
ACTIVE_PUBLICATION_STATUSES = {"submitted", "planned_batch_1", "planned_batch_2", "planned_batch_3", "unknown"}
CONTRACT_REQUIRED_FILES = ("README.md",)
ACTIVE_REQUIRED_FILES = ("main.tex",)
MAPPING_REQUIRED_FILES = ("SOURCE_MAP.md", "THEOREM_LIST.md")
STATUS_MARKER_FILES = ("SUBMITTED",)
STATUS_NOTE_FILES = (
    "review_notes.txt",
    "review_notes.md",
    "REVISION_NOTES.md",
    "revise.md",
    "submission_checklist.md",
)
TRACK_SECTION_ALIASES = {
    "syntax": ("zeta_finite_part",),
    "online_kernel": ("zeta_finite_part",),
    "operator": ("zeta_finite_part",),
    "finite_part": ("zeta_finite_part",),
    "xi": ("zeta_finite_part",),
}
LEAN_LABEL_RE = re.compile(
    r"\b(?:thm|prop|cor|lem|def|con|bridge|cond|cert|aux|infra):[A-Za-z0-9_.-]+\b"
)
LEAN_DECL_CODE_RE = re.compile(r"`([A-Za-z][A-Za-z0-9_'.]*(?:\.[A-Za-z0-9_'.]+)*)`")
CLAIM_ENV_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition|conjecture)\}(?:\[[^\]]*\])?",
    re.DOTALL,
)
CLAIM_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")


@dataclass
class PublicationEntry:
    directory: str
    path: str
    status: str
    phase_heading: str | None
    track_code: str | None
    title: str | None
    target_journal: str | None
    source_sections: list[str]
    source_paths: list[str]
    files: list[str]
    file_count: int
    has_main_tex: bool
    has_outline: bool
    has_source_map: bool
    has_theorem_list: bool
    has_status_marker: bool
    status_marker_files: list[str]
    missing_required_files: list[str]


@dataclass
class SectionStatus:
    section: str
    file_count: int
    line_count: int
    publication_statuses: list[str]
    publications: list[str]
    primary_status: str
    frozen: bool
    action: str


@dataclass
class LeanLinkageRecord:
    directory: str
    basis: str
    source_sections: list[str]
    source_map_labels_total: int
    theorem_list_labels_total: int
    explicit_declaration_names_total: int
    fallback_claim_labels_total: int
    matched_labels_total: int
    missing_labels_total: int
    matched_declarations_total: int
    matched_labels_sample: list[str]
    missing_labels_sample: list[str]
    matched_declarations: list[dict[str, Any]]
    suggested_declarations: list[dict[str, Any]]
    coverage_rate: float | None


@dataclass
class PublicationAuditRecord:
    directory: str
    status: str
    has_readme: bool
    has_main_tex: bool
    has_source_map: bool
    has_theorem_list: bool
    has_status_marker: bool
    status_marker_files: list[str]
    critical_issues: list[str]
    warning_issues: list[str]


def read_text(path: Path) -> str:
    with open(io_path(path), "r", encoding="utf-8") as handle:
        return handle.read()


def write_json(path: Path, payload: Any) -> None:
    with open(io_path(path), "w", encoding="utf-8") as handle:
        handle.write(json.dumps(payload, ensure_ascii=False, indent=2) + "\n")


def write_markdown(path: Path, content: str) -> None:
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


def omega_ci_path() -> Path:
    return paper_root().parents[1] / "lean4" / "scripts" / "omega_ci.py"


def load_omega_ci():
    target = omega_ci_path()
    if not target.is_file():
        raise FileNotFoundError(f"Missing omega_ci.py: {target}")
    spec = importlib.util.spec_from_file_location("automath_omega_ci_runtime", target)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Unable to load omega_ci from {target}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def status_rank(status: str) -> int:
    order = {
        "submitted": 0,
        "planned_batch_1": 1,
        "planned_batch_2": 2,
        "planned_batch_3": 3,
        "archived": 4,
        "frozen": 5,
        "unassigned": 6,
    }
    return order.get(status, 99)


def normalize_status_from_heading(heading: str | None) -> str:
    if not heading:
        return "unknown"
    if "已投稿" in heading:
        return "submitted"
    if "第一批" in heading:
        return "planned_batch_1"
    if "第二批" in heading:
        return "planned_batch_2"
    if "第三批" in heading:
        return "planned_batch_3"
    if "旧计划" in heading:
        return "archived"
    return "unknown"


def extract_section_refs(text: str) -> tuple[list[str], list[str]]:
    section_names = {match.group(1) for match in SECTION_PATH_RE.finditer(text)}
    source_paths = sorted({match.group(0) for match in SECTION_PATH_RE.finditer(text)})
    return sorted(section_names), source_paths


def extract_inline_section_tokens(text: str) -> list[str]:
    body_sections = known_body_sections()
    tokens: set[str] = set()
    for token in SECTION_INLINE_RE.findall(text):
        if token.startswith("2026_") or token.startswith("submitted_"):
            continue
        if token in {"README.md", "OUTLINE.md", "SOURCE_MAP.md", "MIN_SKELETON.md"}:
            continue
        normalized = token.rstrip("/")
        if normalized in body_sections:
            tokens.add(normalized)
    return sorted(tokens)


def extract_first(patterns: list[re.Pattern[str]], text: str) -> str | None:
    for pattern in patterns:
        match = pattern.search(text)
        if match:
            return match.group(1).strip()
    return None


def known_body_sections() -> set[str]:
    return {
        path.name
        for path in (paper_root() / "sections" / "body").iterdir()
        if path.is_dir()
    }


def track_code_sections(track_code: str | None) -> list[str]:
    if not track_code:
        return []
    token = track_code.strip().strip("`").strip("/")
    if not token:
        return []
    head = token.split("/", 1)[0]
    if head in known_body_sections():
        return [head]
    return list(TRACK_SECTION_ALIASES.get(head, ()))


def parse_workspace_readme(path: Path) -> tuple[dict[str, dict[str, str | list[str]]], set[str]]:
    text = read_text(path)
    current_heading: str | None = None
    dir_meta: dict[str, dict[str, str | list[str]]] = {}
    frozen_sections: set[str] = set()
    in_frozen_block = False
    body_sections = known_body_sections()

    for raw_line in text.splitlines():
        line = raw_line.strip()
        if line.startswith("## "):
            current_heading = line[3:].strip()
            in_frozen_block = "显式冻结" in current_heading
            continue
        if in_frozen_block:
            for section in SECTION_PATH_RE.findall(line):
                frozen_sections.add(section)
        if "|" not in line:
            continue
        dirs = DIR_TOKEN_RE.findall(line)
        if not dirs:
            continue
        backticked_tokens = re.findall(r"`([^`]+)`", line)
        track_code = None
        for token in backticked_tokens:
            if token in dirs:
                continue
            if token.startswith("sections/"):
                continue
            if token.startswith("2026_") or token.startswith("submitted_"):
                continue
            track_code = token
            break
        row_sections = sorted(
            {
                token.rstrip("/")
                for token in backticked_tokens
                if token not in dirs
                and not token.startswith("submitted_")
                and not token.startswith("2026_")
                and token.rstrip("/") in body_sections
            }
        )
        for directory in dirs:
            meta = dir_meta.setdefault(directory, {"phase_heading": current_heading or "", "track_code": track_code or "", "row_sections": []})
            meta["phase_heading"] = current_heading or ""
            meta["track_code"] = track_code or ""
            existing = set(meta.get("row_sections", []))
            existing.update(row_sections)
            meta["row_sections"] = sorted(existing)
    return dir_meta, frozen_sections


def count_tex_stats(section_dir: Path) -> tuple[int, int]:
    file_count = 0
    line_count = 0
    for path in sorted(section_dir.rglob("*.tex")):
        file_count += 1
        line_count += read_text(path).count("\n") + 1
    return file_count, line_count


def collect_publication_entries(publication_root: Path, dir_meta: dict[str, dict[str, str | list[str]]]) -> list[PublicationEntry]:
    entries: list[PublicationEntry] = []
    for child in sorted(publication_root.iterdir()):
        if not child.is_dir():
            continue
        readme_path = child / "README.md"
        readme_text = read_text(readme_path) if readme_path.is_file() else ""
        file_names = sorted(path.name for path in child.iterdir() if path.is_file())
        meta = dir_meta.get(child.name, {})
        phase_heading = (meta.get("phase_heading") or None) if meta else None
        status = normalize_status_from_heading(phase_heading)
        if status == "unknown" and child.name.startswith("submitted_"):
            status = "submitted"
        section_names, source_paths = extract_section_refs(readme_text)
        section_names = sorted(
            set(section_names)
            | set(extract_inline_section_tokens(readme_text))
            | set(meta.get("row_sections", []))
            | set(track_code_sections((meta.get("track_code") or None) if meta else None))
        )
        status_markers = [name for name in file_names if name in STATUS_MARKER_FILES or name in STATUS_NOTE_FILES]
        missing_required = [name for name in CONTRACT_REQUIRED_FILES if name not in file_names]
        entries.append(
            PublicationEntry(
                directory=child.name,
                path=str(child),
                status=status,
                phase_heading=phase_heading,
                track_code=(meta.get("track_code") or None) if meta else None,
                title=extract_first([TITLE_RE], readme_text),
                target_journal=extract_first([EN_JOURNAL_RE, ZH_JOURNAL_RE], readme_text),
                source_sections=section_names,
                source_paths=source_paths,
                files=file_names,
                file_count=len(file_names),
                has_main_tex="main.tex" in file_names,
                has_outline="OUTLINE.md" in file_names,
                has_source_map="SOURCE_MAP.md" in file_names,
                has_theorem_list="THEOREM_LIST.md" in file_names,
                has_status_marker=bool(status_markers),
                status_marker_files=status_markers,
                missing_required_files=missing_required,
            )
        )
    return entries


def extract_label_tokens(text: str) -> list[str]:
    return sorted(dict.fromkeys(LEAN_LABEL_RE.findall(text)))


def extract_decl_tokens(text: str) -> list[str]:
    filtered: list[str] = []
    for token in LEAN_DECL_CODE_RE.findall(text):
        if token.endswith((".md", ".tex", ".bib", ".pdf", ".json")):
            continue
        filtered.append(token)
    return sorted(dict.fromkeys(filtered))


def optional_text(path: Path) -> str:
    return read_text(path) if path.is_file() else ""


def collect_section_claim_labels(section: str) -> list[str]:
    section_root = paper_root() / "sections" / "body" / section
    labels: set[str] = set()
    if not section_root.is_dir():
        return []
    for path in sorted(section_root.rglob("*.tex")):
        text = read_text(path)
        for match in CLAIM_ENV_RE.finditer(text):
            env = match.group(1)
            end_marker = f"\\end{{{env}}}"
            end_idx = text.find(end_marker, match.end())
            if end_idx < 0:
                end_idx = len(text)
            body = text[match.end() : end_idx]
            label_match = CLAIM_LABEL_RE.search(body)
            if label_match:
                labels.add(label_match.group(1))
    return sorted(labels)


def build_section_claim_cache() -> dict[str, list[str]]:
    cache: dict[str, list[str]] = {}
    for section in known_body_sections():
        cache[section] = collect_section_claim_labels(section)
    return cache


def build_lean_linkages(entries: list[PublicationEntry]) -> list[LeanLinkageRecord]:
    omega_ci = load_omega_ci()
    declarations, _ = omega_ci.build_inventory()
    search_index = omega_ci.build_search_index(declarations)
    label_to_decls: dict[str, list[Any]] = {}
    name_to_decls: dict[str, list[Any]] = {}
    for decl in declarations:
        name_to_decls.setdefault(str(decl.name), []).append(decl)
        for label in list(decl.registry_labels) + list(decl.paper_labels):
            label_to_decls.setdefault(str(label), []).append(decl)

    section_claim_cache = build_section_claim_cache()
    linkages: list[LeanLinkageRecord] = []

    for entry in entries:
        publication_dir = Path(entry.path)
        source_map_text = optional_text(publication_dir / "SOURCE_MAP.md")
        theorem_list_text = optional_text(publication_dir / "THEOREM_LIST.md")

        source_map_labels = extract_label_tokens(source_map_text)
        theorem_list_labels = extract_label_tokens(theorem_list_text)
        explicit_labels = sorted(dict.fromkeys(source_map_labels + theorem_list_labels))
        explicit_names = sorted(
            dict.fromkeys(extract_decl_tokens(source_map_text) + extract_decl_tokens(theorem_list_text))
        )
        fallback_labels = sorted(
            {
                label
                for section in entry.source_sections
                for label in section_claim_cache.get(section, [])
            }
        )

        if explicit_labels or explicit_names:
            basis = "source_map_or_theorem_list"
            candidate_labels = explicit_labels
        elif entry.source_sections:
            basis = "section_claim_fallback"
            candidate_labels = fallback_labels
        else:
            basis = "unmapped"
            candidate_labels = []

        matched_labels = [label for label in candidate_labels if label in label_to_decls]
        missing_labels = [label for label in candidate_labels if label not in label_to_decls]

        matched_decls: list[Any] = []
        seen_decl_keys: set[tuple[str, int, str]] = set()
        for label in matched_labels:
            for decl in label_to_decls.get(label, []):
                key = (str(decl.file), int(decl.line), str(decl.name))
                if key in seen_decl_keys:
                    continue
                seen_decl_keys.add(key)
                matched_decls.append(decl)
        for name in explicit_names:
            for decl in name_to_decls.get(name, []):
                key = (str(decl.file), int(decl.line), str(decl.name))
                if key in seen_decl_keys:
                    continue
                seen_decl_keys.add(key)
                matched_decls.append(decl)

        suggestion_queries = missing_labels[:3] + [name for name in explicit_names if name not in name_to_decls][:2]
        suggested: list[dict[str, Any]] = []
        seen_suggestions: set[tuple[str, int, str]] = set()
        for query in suggestion_queries:
            try:
                for result in omega_ci.search_declarations(
                    declarations,
                    query,
                    3,
                    search_index=search_index,
                ):
                    key = (str(result["file"]), int(result["line"]), str(result["name"]))
                    if key in seen_suggestions:
                        continue
                    seen_suggestions.add(key)
                    suggested.append(
                        {
                            "query": query,
                            "file": result["file"],
                            "line": result["line"],
                            "module": result["module"],
                            "kind": result["kind"],
                            "name": result["name"],
                            "registry_labels": result["registry_labels"],
                            "paper_labels": result["paper_labels"],
                            "score": result["score"],
                        }
                    )
            except ValueError:
                continue

        coverage_rate = None
        if candidate_labels:
            coverage_rate = len(matched_labels) / len(candidate_labels)

        linkages.append(
            LeanLinkageRecord(
                directory=entry.directory,
                basis=basis,
                source_sections=entry.source_sections,
                source_map_labels_total=len(source_map_labels),
                theorem_list_labels_total=len(theorem_list_labels),
                explicit_declaration_names_total=len(explicit_names),
                fallback_claim_labels_total=len(fallback_labels),
                matched_labels_total=len(matched_labels),
                missing_labels_total=len(missing_labels),
                matched_declarations_total=len(matched_decls),
                matched_labels_sample=matched_labels[:12],
                missing_labels_sample=missing_labels[:12],
                matched_declarations=[
                    {
                        "file": str(decl.file),
                        "line": int(decl.line),
                        "module": str(decl.module),
                        "kind": str(decl.kind),
                        "name": str(decl.name),
                        "registry_labels": list(decl.registry_labels),
                        "paper_labels": list(decl.paper_labels),
                    }
                    for decl in matched_decls[:20]
                ],
                suggested_declarations=suggested[:20],
                coverage_rate=coverage_rate,
            )
        )

    return linkages


def build_publication_audit(entries: list[PublicationEntry], linkages: list[LeanLinkageRecord]) -> tuple[dict[str, Any], list[PublicationAuditRecord]]:
    linkage_by_dir = {linkage.directory: linkage for linkage in linkages}
    records: list[PublicationAuditRecord] = []
    critical_dirs = 0
    warning_dirs = 0

    for entry in entries:
        linkage = linkage_by_dir.get(entry.directory)
        critical: list[str] = []
        warning: list[str] = []

        if entry.missing_required_files:
            critical.append("missing README.md")
        if entry.status in ACTIVE_PUBLICATION_STATUSES and not entry.has_main_tex:
            critical.append("active publication directory missing main.tex")
        if entry.status in {"submitted", "planned_batch_1", "planned_batch_2", "planned_batch_3"} and not entry.has_source_map:
            warning.append("missing SOURCE_MAP.md")
        if entry.status in {"submitted", "planned_batch_1", "planned_batch_2", "planned_batch_3"} and not entry.has_theorem_list:
            warning.append("missing THEOREM_LIST.md")
        if entry.status == "submitted" and not entry.has_status_marker:
            warning.append("submitted directory has no explicit status marker or status notes")
        if entry.status in ACTIVE_PUBLICATION_STATUSES and not entry.source_sections:
            warning.append("directory has no mapped source sections")
        if entry.status in ACTIVE_PUBLICATION_STATUSES and linkage and linkage.basis == "unmapped":
            warning.append("no lean linkage basis available")
        elif (
            entry.status in ACTIVE_PUBLICATION_STATUSES
            and linkage
            and linkage.basis != "unmapped"
            and linkage.matched_declarations_total == 0
        ):
            warning.append("no matched Lean declarations found")

        if critical:
            critical_dirs += 1
        if warning:
            warning_dirs += 1

        records.append(
            PublicationAuditRecord(
                directory=entry.directory,
                status=entry.status,
                has_readme="README.md" in entry.files,
                has_main_tex=entry.has_main_tex,
                has_source_map=entry.has_source_map,
                has_theorem_list=entry.has_theorem_list,
                has_status_marker=entry.has_status_marker,
                status_marker_files=entry.status_marker_files,
                critical_issues=critical,
                warning_issues=warning,
            )
        )

    summary = {
        "directory_total": len(entries),
        "critical_directories_total": critical_dirs,
        "warning_directories_total": warning_dirs,
        "critical_issue_total": sum(len(record.critical_issues) for record in records),
        "warning_issue_total": sum(len(record.warning_issues) for record in records),
    }
    return summary, records


def _legacy_render_audit_report(summary: dict[str, Any], records: list[PublicationAuditRecord]) -> str:
    lines = [
        "# Publication Audit Report",
        "",
        f"- Directories scanned: `{summary['directory_total']}`",
        f"- Directories with critical issues: `{summary['critical_directories_total']}`",
        f"- Directories with warnings: `{summary['warning_directories_total']}`",
        f"- Critical issues total: `{summary['critical_issue_total']}`",
        f"- Warning issues total: `{summary['warning_issue_total']}`",
        "",
        "| Directory | Status | Critical | Warnings |",
        "|---|---|---|---|",
    ]
    for record in records:
        critical = "; ".join(record.critical_issues) if record.critical_issues else "—"
        warning = "; ".join(record.warning_issues) if record.warning_issues else "—"
        lines.append(f"| `{record.directory}` | `{record.status}` | {critical} | {warning} |")
    linkage_problems = [
        linkage
        for linkage in linkages
        if linkage.basis == "unmapped" or linkage.missing_labels_total > 0
    ]
    if linkage_problems:
        lines.extend([
            "",
            "## Lean Linkage Gaps",
            "",
        ])
        for linkage in linkage_problems[:20]:
            lines.append(
                f"- `{linkage.directory}` basis=`{linkage.basis}` "
                f"matched_labels=`{linkage.matched_labels_total}` "
                f"missing_labels=`{linkage.missing_labels_total}` "
                f"matched_declarations=`{linkage.matched_declarations_total}`"
            )

    return "\n".join(lines)


def build_section_statuses(entries: list[PublicationEntry], frozen_sections: set[str]) -> list[SectionStatus]:
    body_root = paper_root() / "sections" / "body"
    section_map: dict[str, dict[str, Any]] = {}
    for section_dir in sorted(path for path in body_root.iterdir() if path.is_dir()):
        file_count, line_count = count_tex_stats(section_dir)
        section_map[section_dir.name] = {
            "publications": set(),
            "statuses": set(),
            "file_count": file_count,
            "line_count": line_count,
        }
    for entry in entries:
        for section in entry.source_sections:
            if section not in section_map:
                continue
            section_map[section]["publications"].add(entry.directory)
            section_map[section]["statuses"].add(entry.status)

    statuses: list[SectionStatus] = []
    for section, data in sorted(section_map.items()):
        publication_statuses = sorted(data["statuses"], key=status_rank)
        publications = sorted(data["publications"])
        if publication_statuses:
            primary_status = publication_statuses[0]
        elif section in frozen_sections:
            primary_status = "frozen"
        else:
            primary_status = "unassigned"
        statuses.append(
            SectionStatus(
                section=section,
                file_count=int(data["file_count"]),
                line_count=int(data["line_count"]),
                publication_statuses=publication_statuses,
                publications=publications,
                primary_status=primary_status,
                frozen=section in frozen_sections,
                action=PROGRAM_ACTIONS.get(primary_status, "needs_program_decision"),
            )
        )
    return statuses


def build_manifest(
    publication_root: Path,
    entries: list[PublicationEntry],
    sections: list[SectionStatus],
    frozen_sections: set[str],
    linkages: list[LeanLinkageRecord],
    audit_summary: dict[str, Any],
) -> dict[str, Any]:
    status_counts: dict[str, int] = {}
    for entry in entries:
        status_counts[entry.status] = status_counts.get(entry.status, 0) + 1
    section_status_counts: dict[str, int] = {}
    for section in sections:
        section_status_counts[section.primary_status] = section_status_counts.get(section.primary_status, 0) + 1
    missing_readme = sorted(entry.directory for entry in entries if entry.missing_required_files)
    unmapped_publications = sorted(entry.directory for entry in entries if not entry.source_sections)
    linkage_counts: dict[str, int] = {}
    for linkage in linkages:
        linkage_counts[linkage.basis] = linkage_counts.get(linkage.basis, 0) + 1
    return {
        "publication_root": str(publication_root),
        "workspace_readme": str(publication_root / "README.md"),
        "workspace_pubplan": str(publication_root / "pubplan.md"),
        "publication_count": len(entries),
        "section_count": len(sections),
        "frozen_sections": sorted(frozen_sections),
        "publication_status_counts": status_counts,
        "section_status_counts": section_status_counts,
        "lean_linkage_basis_counts": linkage_counts,
        "audit_summary": audit_summary,
        "submitted_directories": sorted(entry.directory for entry in entries if entry.status == "submitted"),
        "directories_missing_readme": missing_readme,
        "directories_without_section_mapping": unmapped_publications,
        "unassigned_sections": [section.section for section in sections if section.primary_status == "unassigned"],
    }


def _legacy_render_report(
    manifest: dict[str, Any],
    entries: list[PublicationEntry],
    sections: list[SectionStatus],
    linkages: list[LeanLinkageRecord],
) -> str:
    lines = [
        "# Publication Sync Report",
        "",
        f"- Publication root: `{manifest['publication_root']}`",
        f"- Publication directories: `{manifest['publication_count']}`",
        f"- Body sections tracked: `{manifest['section_count']}`",
        f"- Frozen sections: `{len(manifest['frozen_sections'])}`",
        "",
        "## Publication Status Counts",
        "",
    ]
    for status, count in sorted(manifest["publication_status_counts"].items(), key=lambda item: status_rank(item[0])):
        lines.append(f"- `{status}`: `{count}`")
    lines.extend([
        "",
        "## Section Status Counts",
        "",
    ])
    for status, count in sorted(manifest["section_status_counts"].items(), key=lambda item: status_rank(item[0])):
        lines.append(f"- `{status}`: `{count}`")
    lines.extend([
        "",
        "## Lean Linkage",
        "",
    ])
    for basis, count in sorted(manifest["lean_linkage_basis_counts"].items()):
        lines.append(f"- `{basis}`: `{count}`")
    lines.append(f"- Audit critical directories: `{manifest['audit_summary']['critical_directories_total']}`")
    lines.append(f"- Audit warning directories: `{manifest['audit_summary']['warning_directories_total']}`")
    if manifest["directories_missing_readme"] or manifest["directories_without_section_mapping"]:
        lines.extend([
            "",
            "## Metadata Gaps",
            "",
            f"- Directories missing `README.md`: `{len(manifest['directories_missing_readme'])}`",
            f"- Directories without section mapping: `{len(manifest['directories_without_section_mapping'])}`",
        ])
        if manifest["directories_missing_readme"]:
            lines.append(
                "- Missing README directories: "
                + ", ".join(f"`{name}`" for name in manifest["directories_missing_readme"][:12])
            )
        if manifest["directories_without_section_mapping"]:
            lines.append(
                "- Unmapped directories: "
                + ", ".join(f"`{name}`" for name in manifest["directories_without_section_mapping"][:12])
            )

    lines.extend([
        "",
        "## Active Publication Tracks",
        "",
        "| Directory | Status | Journal | Sections | Files |",
        "|---|---|---|---|---:|",
    ])
    for entry in entries:
        journal = entry.target_journal or "—"
        sections_text = ", ".join(entry.source_sections) if entry.source_sections else "—"
        lines.append(
            f"| `{entry.directory}` | `{entry.status}` | {journal} | {sections_text} | {entry.file_count} |"
        )

    lines.extend([
        "",
        "## Section Program Status",
        "",
        "| Section | Primary Status | Action | Files | Lines | Publications |",
        "|---|---|---|---:|---:|---|",
    ])
    for section in sections:
        pubs = ", ".join(section.publications) if section.publications else "—"
        lines.append(
            f"| `{section.section}` | `{section.primary_status}` | `{section.action}` | "
            f"{section.file_count} | {section.line_count} | {pubs} |"
        )

    unassigned = [section for section in sections if section.primary_status == "unassigned"]
    if unassigned:
        lines.extend([
            "",
            "## Unassigned Sections",
            "",
        ])
        for section in sorted(unassigned, key=lambda item: (-item.line_count, item.section))[:20]:
            lines.append(f"- `{section.section}` — `{section.line_count}` lines, `{section.file_count}` TeX files")

    return "\n".join(lines)


def render_report(
    manifest: dict[str, Any],
    entries: list[PublicationEntry],
    sections: list[SectionStatus],
    linkages: list[LeanLinkageRecord],
) -> str:
    lines = [
        "# Publication Sync Report",
        "",
        f"- Publication root: `{manifest['publication_root']}`",
        f"- Publication directories: `{manifest['publication_count']}`",
        f"- Body sections tracked: `{manifest['section_count']}`",
        f"- Frozen sections: `{len(manifest['frozen_sections'])}`",
        "",
        "## Publication Status Counts",
        "",
    ]
    for status, count in sorted(manifest["publication_status_counts"].items(), key=lambda item: status_rank(item[0])):
        lines.append(f"- `{status}`: `{count}`")
    lines.extend([
        "",
        "## Section Status Counts",
        "",
    ])
    for status, count in sorted(manifest["section_status_counts"].items(), key=lambda item: status_rank(item[0])):
        lines.append(f"- `{status}`: `{count}`")
    lines.extend([
        "",
        "## Lean Linkage",
        "",
    ])
    for basis, count in sorted(manifest["lean_linkage_basis_counts"].items()):
        lines.append(f"- `{basis}`: `{count}`")
    lines.append(f"- Audit critical directories: `{manifest['audit_summary']['critical_directories_total']}`")
    lines.append(f"- Audit warning directories: `{manifest['audit_summary']['warning_directories_total']}`")
    if manifest["directories_missing_readme"] or manifest["directories_without_section_mapping"]:
        lines.extend([
            "",
            "## Metadata Gaps",
            "",
            f"- Directories missing `README.md`: `{len(manifest['directories_missing_readme'])}`",
            f"- Directories without section mapping: `{len(manifest['directories_without_section_mapping'])}`",
        ])
        if manifest["directories_missing_readme"]:
            lines.append(
                "- Missing README directories: "
                + ", ".join(f"`{name}`" for name in manifest["directories_missing_readme"][:12])
            )
        if manifest["directories_without_section_mapping"]:
            lines.append(
                "- Unmapped directories: "
                + ", ".join(f"`{name}`" for name in manifest["directories_without_section_mapping"][:12])
            )

    lines.extend([
        "",
        "## Active Publication Tracks",
        "",
        "| Directory | Status | Journal | Sections | Files |",
        "|---|---|---|---|---:|",
    ])
    for entry in entries:
        journal = entry.target_journal or "—"
        sections_text = ", ".join(entry.source_sections) if entry.source_sections else "—"
        lines.append(
            f"| `{entry.directory}` | `{entry.status}` | {journal} | {sections_text} | {entry.file_count} |"
        )

    lines.extend([
        "",
        "## Section Program Status",
        "",
        "| Section | Primary Status | Action | Files | Lines | Publications |",
        "|---|---|---|---:|---:|---|",
    ])
    for section in sections:
        pubs = ", ".join(section.publications) if section.publications else "—"
        lines.append(
            f"| `{section.section}` | `{section.primary_status}` | `{section.action}` | "
            f"{section.file_count} | {section.line_count} | {pubs} |"
        )

    unassigned = [section for section in sections if section.primary_status == "unassigned"]
    if unassigned:
        lines.extend([
            "",
            "## Unassigned Sections",
            "",
        ])
        for section in sorted(unassigned, key=lambda item: (-item.line_count, item.section))[:20]:
            lines.append(f"- `{section.section}` — `{section.line_count}` lines, `{section.file_count}` TeX files")

    linkage_problems = [
        linkage
        for linkage in linkages
        if linkage.basis == "unmapped" or linkage.missing_labels_total > 0
    ]
    if linkage_problems:
        lines.extend([
            "",
            "## Lean Linkage Gaps",
            "",
        ])
        for linkage in linkage_problems[:20]:
            lines.append(
                f"- `{linkage.directory}` basis=`{linkage.basis}` "
                f"matched_labels=`{linkage.matched_labels_total}` "
                f"missing_labels=`{linkage.missing_labels_total}` "
                f"matched_declarations=`{linkage.matched_declarations_total}`"
            )

    return "\n".join(lines)


def render_audit_report(summary: dict[str, Any], records: list[PublicationAuditRecord]) -> str:
    lines = [
        "# Publication Audit Report",
        "",
        f"- Directories scanned: `{summary['directory_total']}`",
        f"- Directories with critical issues: `{summary['critical_directories_total']}`",
        f"- Directories with warnings: `{summary['warning_directories_total']}`",
        f"- Critical issues total: `{summary['critical_issue_total']}`",
        f"- Warning issues total: `{summary['warning_issue_total']}`",
        "",
        "| Directory | Status | Critical | Warnings |",
        "|---|---|---|---|",
    ]
    for record in records:
        critical = "; ".join(record.critical_issues) if record.critical_issues else "—"
        warning = "; ".join(record.warning_issues) if record.warning_issues else "—"
        lines.append(f"| `{record.directory}` | `{record.status}` | {critical} | {warning} |")
    return "\n".join(lines)


def validate_sync_directory(path: Path) -> tuple[bool, list[str]]:
    errors: list[str] = []
    if not os.path.isdir(io_path(path)):
        errors.append(f"Missing sync directory: {path}")
        return False, errors
    for filename in REQUIRED_SYNC_FILES:
        target = path / filename
        if not os.path.isfile(io_path(target)):
            errors.append(f"Missing required file: {target}")
    return len(errors) == 0, errors


def sync_publication_workspace(publication_root: Path, slug: str) -> tuple[Path, dict[str, Any], dict[str, Any]]:
    if not publication_root.is_dir():
        raise SystemExit(f"publication root does not exist: {publication_root}")
    workspace_readme = publication_root / "README.md"
    if not workspace_readme.is_file():
        raise SystemExit(f"publication workspace missing README.md: {workspace_readme}")

    dir_meta, frozen_sections = parse_workspace_readme(workspace_readme)
    entries = collect_publication_entries(publication_root, dir_meta)
    linkages = build_lean_linkages(entries)
    audit_summary, audit_records = build_publication_audit(entries, linkages)
    sections = build_section_statuses(entries, frozen_sections)
    manifest = build_manifest(publication_root, entries, sections, frozen_sections, linkages, audit_summary)
    report = render_report(manifest, entries, sections, linkages)
    audit_report = render_audit_report(audit_summary, audit_records)

    output_dir = export_dir() / "publication_sync" / slug
    output_dir.mkdir(parents=True, exist_ok=True)
    write_json(output_dir / "sync_manifest.json", manifest)
    write_json(output_dir / "publication_inventory.json", [asdict(entry) for entry in entries])
    write_json(output_dir / "section_status.json", [asdict(section) for section in sections])
    write_json(output_dir / "lean_linkage.json", [asdict(linkage) for linkage in linkages])
    write_json(
        output_dir / "publication_audit.json",
        {
            "summary": audit_summary,
            "records": [asdict(record) for record in audit_records],
        },
    )
    write_markdown(output_dir / "publication_audit_report.md", audit_report)
    write_markdown(output_dir / "publication_sync_report.md", report)
    return output_dir, manifest, audit_summary


def cmd_sync(args: argparse.Namespace) -> int:
    publication_root = Path(args.publication_root).resolve()
    output_dir, manifest, _ = sync_publication_workspace(publication_root, slug=args.slug)
    print(
        "[publication-sync] sync: "
        f"publication_root={publication_root} slug={args.slug} output={output_dir} "
        f"publications={manifest['publication_count']} sections={manifest['section_count']}",
        flush=True,
    )
    return 0


def cmd_audit(args: argparse.Namespace) -> int:
    publication_root = Path(args.publication_root).resolve()
    output_dir, _, audit_summary = sync_publication_workspace(publication_root, slug=args.slug)
    ok = audit_summary["critical_directories_total"] == 0 and (
        not args.strict or audit_summary["warning_directories_total"] == 0
    )
    print(
        "[publication-sync] audit: "
        f"publication_root={publication_root} slug={args.slug} output={output_dir} "
        f"critical_dirs={audit_summary['critical_directories_total']} "
        f"warning_dirs={audit_summary['warning_directories_total']} strict={args.strict}",
        flush=True,
    )
    return 0 if ok else 1


def cmd_validate(args: argparse.Namespace) -> int:
    target = Path(args.path).resolve()
    ok, errors = validate_sync_directory(target)
    print(
        "[publication-sync] validate: "
        f"path={target} ok={ok} errors={len(errors)}",
        flush=True,
    )
    for error in errors:
        print(f"  - {error}", flush=True)
    return 0 if ok else 1


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Synchronize an external publication workspace into automath artifacts"
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    sync_parser = subparsers.add_parser("sync", help="Scan one publication workspace and build a sync report")
    sync_parser.add_argument("--publication-root", required=True, help="Path to the external publication workspace")
    sync_parser.add_argument("--slug", required=True, help="Output slug under artifacts/export/publication_sync/")
    sync_parser.set_defaults(func=cmd_sync)

    audit_parser = subparsers.add_parser("audit", help="Run contract checks for one publication workspace")
    audit_parser.add_argument("--publication-root", required=True, help="Path to the external publication workspace")
    audit_parser.add_argument("--slug", required=True, help="Output slug under artifacts/export/publication_sync/")
    audit_parser.add_argument("--strict", action="store_true", help="Fail on warnings as well as critical issues")
    audit_parser.set_defaults(func=cmd_audit)

    validate_parser = subparsers.add_parser("validate", help="Validate one generated sync directory")
    validate_parser.add_argument("path", help="Path to artifacts/export/publication_sync/<slug>")
    validate_parser.set_defaults(func=cmd_validate)

    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
