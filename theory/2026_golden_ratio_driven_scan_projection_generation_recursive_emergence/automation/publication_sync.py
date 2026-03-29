#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Synchronize an external publication workspace into local automation artifacts."""

from __future__ import annotations

import argparse
import json
import os
import re
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
    tokens: set[str] = set()
    for token in SECTION_INLINE_RE.findall(text):
        if token.startswith("2026_") or token.startswith("submitted_"):
            continue
        if token in {"README.md", "OUTLINE.md", "SOURCE_MAP.md", "MIN_SKELETON.md"}:
            continue
        tokens.add(token.rstrip("/"))
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
        section_names = sorted(set(section_names) | set(meta.get("row_sections", [])))
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
                missing_required_files=[] if "README.md" in file_names else ["README.md"],
            )
        )
    return entries


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
) -> dict[str, Any]:
    status_counts: dict[str, int] = {}
    for entry in entries:
        status_counts[entry.status] = status_counts.get(entry.status, 0) + 1
    section_status_counts: dict[str, int] = {}
    for section in sections:
        section_status_counts[section.primary_status] = section_status_counts.get(section.primary_status, 0) + 1
    missing_readme = sorted(entry.directory for entry in entries if entry.missing_required_files)
    unmapped_publications = sorted(entry.directory for entry in entries if not entry.source_sections)
    return {
        "publication_root": str(publication_root),
        "workspace_readme": str(publication_root / "README.md"),
        "workspace_pubplan": str(publication_root / "pubplan.md"),
        "publication_count": len(entries),
        "section_count": len(sections),
        "frozen_sections": sorted(frozen_sections),
        "publication_status_counts": status_counts,
        "section_status_counts": section_status_counts,
        "submitted_directories": sorted(entry.directory for entry in entries if entry.status == "submitted"),
        "directories_missing_readme": missing_readme,
        "directories_without_section_mapping": unmapped_publications,
        "unassigned_sections": [section.section for section in sections if section.primary_status == "unassigned"],
    }


def render_report(manifest: dict[str, Any], entries: list[PublicationEntry], sections: list[SectionStatus]) -> str:
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


def validate_sync_directory(path: Path) -> tuple[bool, list[str]]:
    errors: list[str] = []
    if not path.is_dir():
        errors.append(f"Missing sync directory: {path}")
        return False, errors
    for filename in REQUIRED_SYNC_FILES:
        target = path / filename
        if not target.is_file():
            errors.append(f"Missing required file: {target}")
    return len(errors) == 0, errors


def sync_publication_workspace(publication_root: Path, slug: str) -> Path:
    if not publication_root.is_dir():
        raise SystemExit(f"publication root does not exist: {publication_root}")
    workspace_readme = publication_root / "README.md"
    if not workspace_readme.is_file():
        raise SystemExit(f"publication workspace missing README.md: {workspace_readme}")

    dir_meta, frozen_sections = parse_workspace_readme(workspace_readme)
    entries = collect_publication_entries(publication_root, dir_meta)
    sections = build_section_statuses(entries, frozen_sections)
    manifest = build_manifest(publication_root, entries, sections, frozen_sections)
    report = render_report(manifest, entries, sections)

    output_dir = export_dir() / "publication_sync" / slug
    output_dir.mkdir(parents=True, exist_ok=True)
    write_json(output_dir / "sync_manifest.json", manifest)
    write_json(output_dir / "publication_inventory.json", [asdict(entry) for entry in entries])
    write_json(output_dir / "section_status.json", [asdict(section) for section in sections])
    write_markdown(output_dir / "publication_sync_report.md", report)
    return output_dir


def cmd_sync(args: argparse.Namespace) -> int:
    publication_root = Path(args.publication_root).resolve()
    output_dir = sync_publication_workspace(publication_root, slug=args.slug)
    print(
        "[publication-sync] sync: "
        f"publication_root={publication_root} slug={args.slug} output={output_dir}",
        flush=True,
    )
    return 0


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
