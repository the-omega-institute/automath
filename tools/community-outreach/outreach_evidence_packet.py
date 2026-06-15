#!/usr/bin/env python3
"""Build paper-style evidence packets for outreach Oracle deep reasoning.

The Oracle boundary for deep math work is intentionally narrow:
Codex/local tools own repository inspection, artifact selection, and
writeback. Oracle receives a curated mathematical note as an attachment and
reasons from that note, without inferring repository layout.
"""

from __future__ import annotations

import hashlib
import json
import re
import textwrap
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

from outreach_board_parser import TodoSpec

REPO_ROOT_DEFAULT = Path(__file__).resolve().parents[2]
TARGETS_DIR_DEFAULT = REPO_ROOT_DEFAULT / "tools/community-outreach/targets"

CORE_CONTEXT_FILES = (
    "next_oracle_question.md",
    "codex_workup.md",
    "local_repair_report.md",
    "research.md",
)
EXCLUDED_MD_NAMES = {
    "oracle_evidence_packet.md",
    "research.md",
    "codex_workup.md",
    "local_repair_report.md",
    "next_oracle_question.md",
    "submission_draft.md",
}
CERTIFICATE_NAME_RE = re.compile(
    r"(certificate|criterion|decomposition|obstruction|guardrail|lemma|proof|"
    r"claim|route|gap)",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class EvidencePacket:
    markdown_path: Path
    pdf_path: Path
    markdown_sha256: str
    pdf_sha256: str
    source_files: list[str]


def build_evidence_packet(
    todo: TodoSpec,
    *,
    repo_root: Path = REPO_ROOT_DEFAULT,
    slug: str | None = None,
    max_core_chars: int = 9000,
    max_note_chars: int = 7000,
    max_json_chars: int = 2500,
) -> EvidencePacket:
    """Write oracle_evidence_packet.md and .pdf for one target."""
    target_slug = slug or todo.slug()
    target_dir = repo_root / "tools/community-outreach/targets" / target_slug
    target_dir.mkdir(parents=True, exist_ok=True)
    md_path = target_dir / "oracle_evidence_packet.md"
    pdf_path = target_dir / "oracle_evidence_packet.pdf"

    source_files: list[Path] = []
    parts: list[str] = []
    generated_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
    next_question = _read_target_file(target_dir, "next_oracle_question.md", max_core_chars)
    codex_workup = _read_target_file(target_dir, "codex_workup.md", max_core_chars)
    local_repair = _read_target_file(target_dir, "local_repair_report.md", max_core_chars // 2)
    research = _read_target_file(target_dir, "research.md", max_core_chars // 2)
    for name in CORE_CONTEXT_FILES:
        p = target_dir / name
        if p.exists():
            source_files.append(p)

    parts.extend(
        [
            f"# Evidence packet for {todo.todo_id}: {todo.title}",
            "",
            f"Generated: {generated_at}",
            "",
            "## Boundary of this request",
            "",
            "This packet is the mathematical context. Oracle is the primary proof-search",
            "worker for the target. Reason from this note and the problem statement only.",
            "Do not infer repository structure, do not ask Codex to read local paths, and",
            "do not return file blocks. Codex/local tools are responsible for repository",
            "inspection, verifier execution, and writeback after Oracle supplies the",
            "mathematical argument or a precise verifier request.",
            "",
            "## Problem statement",
            "",
            _compact_plain(todo.statement or "(no board statement recorded)", 5000, target_slug),
            "",
            "## Source and intended outcome",
            "",
            f"- Source: {_one_line(todo.source)}",
            f"- Claimed untouched/source status: {_one_line(todo.untouched)}",
            f"- Success gate: {_one_line(todo.success_gate)}",
            f"- Final venue: {_one_line(todo.final_display)}",
            "",
            "## Exact question for Oracle",
            "",
            _compact_plain(
                next_question
                or "Find one concrete proof move, obstruction, or bounded theorem that materially advances this target.",
                5000,
                target_slug,
            ),
            "",
            "## What Oracle must not assume",
            "",
            "- Do not assume any unstated local file, script, package, or repository layout.",
            "- Do not treat previous Oracle text as verified unless this note says Codex checked it.",
            "- Do not treat a named file, script, certificate, or hash as produced unless",
            "  the complete contents are included in this packet or in your answer.",
            "- Do not solve a software task. Solve the mathematical question above.",
            "- If a local computation would decide a subclaim, state the exact verifier",
            "  specification: input objects, finite ranges or hypotheses, expected",
            "  invariant/output, and how the result would close or refute the subclaim.",
            "- If a gap remains, turn it into the next proof obligation and attack it;",
            "  do not stop at a referee-style statement that the route is not closed.",
            "",
        ]
    )

    if codex_workup:
        parts.extend(
            [
                "## Local workup distilled by Codex",
                "",
                _compact_plain(codex_workup, max_core_chars, target_slug),
                "",
            ]
        )
    if local_repair:
        parts.extend(
            [
                "## Latest local replay or verifier report",
                "",
                _compact_plain(local_repair, max_core_chars // 2, target_slug),
                "",
            ]
        )
    if research:
        parts.extend(
            [
                "## Prior research note excerpt",
                "",
                _compact_plain(research, max_core_chars // 2, target_slug),
                "",
            ]
        )

    note_files = _select_certificate_notes(target_dir)
    if note_files:
        parts.extend(["## Curated mathematical notes and certificates", ""])
        for path in note_files:
            source_files.append(path)
            parts.extend(
                [
                    f"### {_human_title(path.stem)}",
                    "",
                    _compact_plain(_read_text(path, max_note_chars), max_note_chars, target_slug),
                    "",
                ]
            )

    json_files = _select_json_summaries(target_dir)
    if json_files:
        parts.extend(["## Computation and verifier summaries", ""])
        for path in json_files:
            source_files.append(path)
            parts.extend(_json_summary_block(path, max_json_chars=max_json_chars, slug=target_slug))

    parts.extend(
        [
            "## Requested Oracle output",
            "",
            "Answer as the primary mathematical proof-search worker:",
            "",
            "1. State the current proof target you will close next.",
            "2. Prove the strongest theorem/lemma you can from the packet, with explicit",
            "   hypotheses and proof steps.",
            "3. If the full target is not closed, give the next proof obligation as a",
            "   precise mathematical claim and immediately push that claim as far as possible.",
            "4. If local verification is needed, give a verifier specification Codex can run",
            "   and explain exactly how each possible output changes the proof state.",
            "5. If you claim a certificate or verifier exists, include the full",
            "   self-contained mathematical data or source text needed to replay it.",
            "",
            "Do not mention repository paths in the answer except when quoting a theorem or",
            "computation label from this packet. Do not emit FILE blocks.",
            "",
            "## Reproducibility appendix",
            "",
            "The following local artifacts were used by Codex to assemble this note.",
            "They are listed only for auditability; Oracle need not understand the layout.",
            "",
        ]
    )
    for path in _unique_paths(source_files):
        parts.append(f"- {_artifact_label(path)}: sha256={_sha256_path(path)[:16]}")
    parts.append("")

    markdown = "\n".join(parts)
    md_path.write_text(markdown, encoding="utf-8")
    _write_simple_text_pdf(markdown, pdf_path, title=f"{todo.todo_id} evidence packet")
    return EvidencePacket(
        markdown_path=md_path,
        pdf_path=pdf_path,
        markdown_sha256=_sha256_path(md_path),
        pdf_sha256=_sha256_path(pdf_path),
        source_files=[str(p.relative_to(repo_root)) if _is_relative_to(p, repo_root) else str(p)
                      for p in _unique_paths(source_files)],
    )


def build_attachment_prompt(todo: TodoSpec, packet: EvidencePacket) -> str:
    """Short prompt paired with the evidence-packet PDF attachment."""
    return "\n".join(
        [
            "Read the attached evidence packet as a mathematical research note.",
            "Do not infer repository structure and do not ask for local files or paths.",
            "You are the primary proof-search worker. Your job is to continue the proof from",
            "the attachment, not to merely referee whether it is already closed.",
            "",
            f"Target: {todo.todo_id} - {todo.title}",
            "",
            "Answer the exact Oracle question inside the packet. Do the next mathematical",
            "work needed for closure:",
            "1. state the proof target you are closing next;",
            "2. prove the strongest theorem/lemma you can from the packet;",
            "3. if not fully closed, convert the remaining gap into the next precise proof",
            "   obligation and push it as far as possible;",
            "4. if local verification is needed, give a concrete verifier specification",
            "   Codex can run and explain how its outputs would advance the proof.",
            "",
            "Do not emit FILE blocks. Do not mention repository paths unless quoting labels from the packet.",
            f"Packet audit: md_sha256={packet.markdown_sha256[:16]}, pdf_sha256={packet.pdf_sha256[:16]}.",
        ]
    )


def _select_certificate_notes(target_dir: Path, *, limit: int = 8) -> list[Path]:
    candidates = [
        p for p in target_dir.glob("*.md")
        if p.name not in EXCLUDED_MD_NAMES and not p.name.startswith("oracle_claim_packet_")
    ]
    scored = []
    for path in candidates:
        score = 10 if CERTIFICATE_NAME_RE.search(path.name) else 0
        try:
            score += min(5, int(path.stat().st_size // 2000))
        except OSError:
            pass
        scored.append((score, path.name, path))
    scored.sort(key=lambda item: (-item[0], item[1]))
    return [path for score, _name, path in scored[:limit] if score > 0]


def _select_json_summaries(target_dir: Path, *, limit: int = 6) -> list[Path]:
    skip = {"local_repair_last.json", "profile.json"}
    paths = [
        p for p in target_dir.glob("*.json")
        if p.name not in skip and not p.name.startswith("outreach_")
    ]
    paths.sort(key=lambda p: (0 if p.name == "results.json" else 1, p.name))
    return paths[:limit]


def _json_summary_block(path: Path, *, max_json_chars: int, slug: str) -> list[str]:
    text = _read_text(path, max_json_chars)
    summary = ""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(data, dict):
            keys = ", ".join(str(k) for k in list(data.keys())[:20])
            summary = f"JSON object with keys: {keys}"
        elif isinstance(data, list):
            summary = f"JSON list with {len(data)} entries"
    except Exception:
        summary = "JSON parse summary unavailable"
    return [
        f"### {_human_title(path.stem)}",
        "",
        summary,
        "",
        "Excerpt:",
        "",
        "```json",
        _compact_plain(text, max_json_chars, slug),
        "```",
        "",
    ]


def _read_target_file(target_dir: Path, name: str, max_chars: int) -> str:
    return _read_text(target_dir / name, max_chars)


def _read_text(path: Path, max_chars: int) -> str:
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""
    if len(text) <= max_chars:
        return text.strip()
    return text[:max_chars].rstrip() + "\n\n[... clipped by evidence-packet builder ...]"


def _compact_plain(text: str, max_chars: int, slug: str) -> str:
    text = _redact_repo_paths(text.strip(), slug)
    text = text.replace("FILE:", "Artifact block:")
    if len(text) > max_chars:
        text = text[:max_chars].rstrip() + "\n\n[... clipped by evidence-packet builder ...]"
    return text or "(none)"


def _redact_repo_paths(text: str, slug: str) -> str:
    text = text.replace(f"tools/community-outreach/targets/{slug}/", "[target artifact]/")
    text = re.sub(
        r"/Users/[^ \n`]+/automath-outreach/tools/community-outreach/targets/"
        + re.escape(slug)
        + r"/",
        "[target artifact]/",
        text,
    )
    text = text.replace("tools/community-outreach/targets/<slug>/", "[target artifact]/")
    return text


def _write_simple_text_pdf(markdown: str, path: Path, *, title: str) -> None:
    """Write a small dependency-free PDF containing wrapped plain text."""
    text = _markdown_to_pdf_text(markdown)
    lines: list[str] = []
    for raw in text.splitlines():
        if not raw.strip():
            lines.append("")
            continue
        indent = "  " if raw.startswith(("- ", "1. ", "2. ", "3. ", "4. ")) else ""
        wrapped = textwrap.wrap(raw, width=92, replace_whitespace=False) or [""]
        lines.extend((indent + line if idx else line) for idx, line in enumerate(wrapped))

    page_height = 792
    margin_x = 44
    top_y = 748
    font_size = 9
    leading = 12
    lines_per_page = 58
    pages = [lines[i:i + lines_per_page] for i in range(0, len(lines), lines_per_page)] or [[]]

    objects: list[bytes] = []
    objects.append(b"<< /Type /Catalog /Pages 2 0 R >>")
    objects.append(b"")
    objects.append(b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>")
    page_refs: list[str] = []
    for page_lines in pages:
        content = [
            "BT",
            f"/F1 {font_size} Tf",
            f"{margin_x} {top_y} Td",
            f"{leading} TL",
        ]
        for line in page_lines:
            content.append(f"({_pdf_escape(line)}) Tj")
            content.append("T*")
        content.append("ET")
        stream = "\n".join(content).encode("latin-1", errors="replace")
        page_obj_id = len(objects) + 1
        content_obj_id = page_obj_id + 1
        page_refs.append(f"{page_obj_id} 0 R")
        objects.append(
            (
                f"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 {page_height}] "
                f"/Resources << /Font << /F1 3 0 R >> >> /Contents {content_obj_id} 0 R >>"
            ).encode("ascii")
        )
        objects.append(
            b"<< /Length " + str(len(stream)).encode("ascii") + b" >>\nstream\n"
            + stream + b"\nendstream"
        )
    objects[1] = (
        f"<< /Type /Pages /Kids [{' '.join(page_refs)}] /Count {len(page_refs)} >>"
    ).encode("ascii")

    info_obj = (
        f"<< /Title ({_pdf_escape(title)}) /Creator (outreach_evidence_packet.py) >>"
    ).encode("latin-1", errors="replace")
    objects.append(info_obj)
    info_id = len(objects)

    chunks = [b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n"]
    offsets = [0]
    for idx, obj in enumerate(objects, start=1):
        offsets.append(sum(len(c) for c in chunks))
        chunks.append(f"{idx} 0 obj\n".encode("ascii"))
        chunks.append(obj)
        chunks.append(b"\nendobj\n")
    xref_offset = sum(len(c) for c in chunks)
    chunks.append(f"xref\n0 {len(objects) + 1}\n".encode("ascii"))
    chunks.append(b"0000000000 65535 f \n")
    for off in offsets[1:]:
        chunks.append(f"{off:010d} 00000 n \n".encode("ascii"))
    chunks.append(
        (
            f"trailer\n<< /Size {len(objects) + 1} /Root 1 0 R /Info {info_id} 0 R >>\n"
            f"startxref\n{xref_offset}\n%%EOF\n"
        ).encode("ascii")
    )
    path.write_bytes(b"".join(chunks))


def _markdown_to_pdf_text(markdown: str) -> str:
    lines = []
    for line in markdown.splitlines():
        stripped = line.strip()
        if stripped.startswith("#"):
            stripped = stripped.lstrip("#").strip().upper()
        stripped = stripped.replace("`", "")
        lines.append(stripped)
    return "\n".join(lines)


def _pdf_escape(text: str) -> str:
    safe = text.encode("latin-1", errors="replace").decode("latin-1")
    return safe.replace("\\", "\\\\").replace("(", "\\(").replace(")", "\\)")


def _sha256_path(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _unique_paths(paths: Iterable[Path]) -> list[Path]:
    seen: set[Path] = set()
    out: list[Path] = []
    for path in paths:
        resolved = path.resolve()
        if resolved in seen:
            continue
        seen.add(resolved)
        out.append(path)
    return out


def _artifact_label(path: Path) -> str:
    return _human_title(path.stem)


def _human_title(value: str) -> str:
    return value.replace("_", " ").replace("-", " ").strip().title()


def _one_line(value: str) -> str:
    return " ".join(str(value or "").split()) or "(none)"


def _is_relative_to(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
        return True
    except ValueError:
        return False
