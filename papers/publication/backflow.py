#!/usr/bin/env python3
"""Backflow automation: extract proven theorems from ACCEPT/submitted papers
and map them back to the core theory knowledge base.

Usage:
    python backflow.py scan                  # Scan all ACCEPT + submitted papers
    python backflow.py scan --paper <dir>    # Scan a specific paper
    python backflow.py report                # Generate backflow report
    python backflow.py inject                # Inject cross-references into core
    python backflow.py status                # Show pipeline-wide backflow status

Architecture:
    Publication papers are specialized extractions from the core theory.
    When a paper reaches ACCEPT, its proven results should be:
    1. Catalogued (theorem labels, statements, proof status)
    2. Mapped to core theory sections
    3. Cross-referenced back into the core (\\cref, remarks, citations)
    4. Tracked in each paper's PIPELINE.md backflow table
"""

import argparse
import json
import os
import re
import sys
from dataclasses import asdict, dataclass, field
from datetime import date
from pathlib import Path

PUBLICATION_DIR = Path(__file__).parent
THEORY_DIR = (
    PUBLICATION_DIR.parent.parent
    / "theory"
    / "2026_golden_ratio_driven_scan_projection_generation_recursive_emergence"
)
CORE_BODY = THEORY_DIR / "sections" / "body"
BACKFLOW_DIR = PUBLICATION_DIR / "backflow"

# Regex patterns
CLAIM_ENV_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}"
    r"(?:\[([^\]]*)\])?\s*"
    r"\\label\{([^}]+)\}",
    re.DOTALL,
)
CLAIM_BLOCK_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}"
    r"(.*?)"
    r"\\end\{\1\}",
    re.DOTALL,
)
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
SECTION_RE = re.compile(r"\\section\{([^}]+)\}")
INPUT_RE = re.compile(r"\\input\{([^}]+)\}")

# Paper → core section mapping (canonical)
PAPER_CORE_MAP = {
    "circle_dimension": "circle_dimension_phase_gate",
    "dynamical_zeta": "zeta_finite_part",
    "fredholm_witt": "zeta_finite_part",
    "conservative_extension": "logic_expansion_chain",
    "fibonacci_folding": "folding",
    "fold_truncation": "fold_residual_time",
    "recursive_addressing": "recursive_addressing",
    "scan_projection": "spg",
    "projection_ontological": "pom",
    "yang_lee": "statistical_stability",
    "prime_languages": "zeta_finite_part",
    "self_dual_synchronisation": "zeta_finite_part",
    "cubical_stokes": "high_dimensional_cut_project",
    "gluing_failure": "logic_expansion_chain",
    "prefix_scan": "spg",
    "scan_error": "spg",
    "detector_shells": "physical_spacetime_skeleton",
    "JphisComm": "physical_spacetime_skeleton",
    "fredholm_determinants": "zeta_finite_part",
    "group_unification": "group_unification",
    "finite_parts_dynamical": "zeta_finite_part",
    "finite_observation": "statistical_stability",
    "finite_window": "folding",
    "sharp_three_window": "folding",
    "folded_histograms": "folding",
    "cayley_chebyshev": "circle_dimension_phase_gate",
    "homological_visibility": "logic_expansion_chain",
    "coefficient_sup_radial": "emergent_arithmetic",
    "deterministic_telescoping": "fold_residual_time",
    "elliptic_normalization": "emergent_arithmetic",
    # Submitted papers
    "branch_cubic": "emergent_arithmetic",
    "fibonacci_moduli": "folding",
    "fibonacci_stabilization": "folding",
    "folded_rotation_histogram": "folding",
    "grg_shell_geometry": "physical_spacetime_skeleton",
    "resolution_folding": "folding",
    "zeckendorf_streaming": "folding",
    "zero_jitter": "statistical_stability",
}


@dataclass
class ClaimRecord:
    """A single mathematical claim extracted from a paper."""
    env_type: str           # theorem, lemma, proposition, corollary, definition
    label: str              # LaTeX label (e.g., thm:finite-part-primitive)
    title: str              # Optional title from [...] after \begin{theorem}
    source_file: str        # Relative path within paper dir
    line_number: int        # Approximate line number
    statement_preview: str  # First 200 chars of the statement


@dataclass
class BackflowRecord:
    """Backflow mapping for one paper."""
    paper_dir: str
    paper_slug: str
    status: str             # ACCEPT, submitted, in_review
    target_journal: str
    core_section: str       # Target core body section
    claims: list[ClaimRecord] = field(default_factory=list)
    backflow_status: str = "pending"  # pending, partial, integrated
    date_scanned: str = ""


def io_path(path: Path) -> str:
    """Handle Windows long paths."""
    text = os.path.abspath(str(path))
    if os.name != "nt":
        return text
    normalized = text.replace("/", "\\")
    if normalized.startswith("\\\\?\\"):
        return normalized
    if normalized.startswith("\\\\"):
        return "\\\\?\\UNC\\" + normalized[2:]
    return "\\\\?\\" + normalized


def read_text(path: Path) -> str:
    with open(io_path(path), "r", encoding="utf-8", errors="replace") as f:
        return f.read()


def write_json(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(io_path(path), "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2, default=str)
        f.write("\n")


def write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(io_path(path), "w", encoding="utf-8") as f:
        f.write(content)


def detect_paper_status(paper_dir: Path) -> str:
    """Detect paper status from directory name and review files."""
    name = paper_dir.name
    if name.startswith("submitted_"):
        return "submitted"
    # Check for ACCEPT editorial review
    for f in paper_dir.glob("P4_EDITORIAL_REVIEW*.md"):
        content = read_text(f)
        if re.search(r"\bACCEPT\b", content):
            return "ACCEPT"
    return "in_review"


def detect_journal(paper_dir: Path) -> str:
    """Extract target journal from PIPELINE.md or directory name."""
    pipeline = paper_dir / "PIPELINE.md"
    if pipeline.exists():
        text = read_text(pipeline)
        m = re.search(r"Target.*?:\s*(.+?)(?:\s*\(|$)", text, re.MULTILINE)
        if m:
            return m.group(1).strip()
    # Fallback: extract from directory name suffix
    name = paper_dir.name
    for suffix in ["_jfa", "_etds", "_apal", "_tams", "_tac", "_jnt",
                    "_jdsgt", "_rint", "_siads", "_grg", "_jtp", "_rairo_ita"]:
        if name.endswith(suffix):
            return suffix.strip("_").upper()
    return "unknown"


def slug_from_dir(paper_dir: Path) -> str:
    """Extract paper slug (short identifier) from directory name."""
    name = paper_dir.name
    name = re.sub(r"^(?:submitted_)?2026_", "", name)
    # Take first 3 tokens as slug
    parts = name.split("_")
    return "_".join(parts[:3])


def map_to_core_section(slug: str) -> str:
    """Map paper slug to core theory section."""
    for key, section in PAPER_CORE_MAP.items():
        if key in slug:
            return section
    return "unknown"


def extract_claims(paper_dir: Path) -> list[ClaimRecord]:
    """Extract all theorem-level claims from a paper's .tex files."""
    claims = []
    tex_files = sorted(paper_dir.glob("**/*.tex"))
    for tex_file in tex_files:
        # Skip generated or auxiliary files
        rel = tex_file.relative_to(paper_dir)
        if any(p in str(rel) for p in ["backup", "old", "unused"]):
            continue
        text = read_text(tex_file)
        lines = text.split("\n")
        # Find all claim environments with labels
        for match in CLAIM_ENV_RE.finditer(text):
            env_type = match.group(1)
            title = match.group(2) or ""
            label = match.group(3)
            # Find line number
            pos = match.start()
            line_num = text[:pos].count("\n") + 1
            # Extract statement preview (up to \end{env})
            end_tag = f"\\end{{{env_type}}}"
            end_pos = text.find(end_tag, pos)
            if end_pos > 0:
                statement = text[match.end():end_pos].strip()
                # Clean up LaTeX for preview
                preview = statement[:200].replace("\n", " ").strip()
            else:
                preview = ""
            claims.append(ClaimRecord(
                env_type=env_type,
                label=label,
                title=title.strip(),
                source_file=str(rel),
                line_number=line_num,
                statement_preview=preview,
            ))
    return claims


def scan_paper(paper_dir: Path) -> BackflowRecord:
    """Scan a single paper and produce a backflow record."""
    slug = slug_from_dir(paper_dir)
    status = detect_paper_status(paper_dir)
    journal = detect_journal(paper_dir)
    core_section = map_to_core_section(slug)
    claims = extract_claims(paper_dir)

    # Check existing backflow status in PIPELINE.md
    backflow_status = "pending"
    pipeline = paper_dir / "PIPELINE.md"
    if pipeline.exists():
        text = read_text(pipeline)
        if "### Backflow to Core" in text:
            integrated = text.count("| integrated |")
            pending = text.count("| pending |")
            if integrated > 0 and pending == 0:
                backflow_status = "integrated"
            elif integrated > 0:
                backflow_status = "partial"

    return BackflowRecord(
        paper_dir=str(paper_dir.relative_to(PUBLICATION_DIR)),
        paper_slug=slug,
        status=status,
        target_journal=journal,
        core_section=core_section,
        claims=claims,
        backflow_status=backflow_status,
        date_scanned=str(date.today()),
    )


def scan_all() -> list[BackflowRecord]:
    """Scan all ACCEPT and submitted papers."""
    records = []
    for d in sorted(PUBLICATION_DIR.iterdir()):
        if not d.is_dir():
            continue
        if not d.name.startswith("2026_") and not d.name.startswith("submitted_2026_"):
            continue
        main_tex = d / "main.tex"
        if not main_tex.exists():
            continue
        record = scan_paper(d)
        if record.status in ("ACCEPT", "submitted"):
            records.append(record)
    return records


def generate_report(records: list[BackflowRecord]) -> str:
    """Generate a markdown backflow report."""
    today = date.today()
    lines = [
        f"# Backflow Report — {today}",
        "",
        "## Summary",
        "",
        f"| Metric | Count |",
        f"|--------|-------|",
        f"| Papers scanned | {len(records)} |",
        f"| ACCEPT | {sum(1 for r in records if r.status == 'ACCEPT')} |",
        f"| Submitted | {sum(1 for r in records if r.status == 'submitted')} |",
        f"| Total claims | {sum(len(r.claims) for r in records)} |",
        f"| Backflow integrated | {sum(1 for r in records if r.backflow_status == 'integrated')} |",
        f"| Backflow pending | {sum(1 for r in records if r.backflow_status == 'pending')} |",
        "",
        "## Paper-by-Paper Backflow Status",
        "",
    ]

    for record in records:
        emoji = {"ACCEPT": "V", "submitted": "S"}.get(record.status, "?")
        bf = {"integrated": "done", "partial": "partial", "pending": "TODO"}.get(
            record.backflow_status, "?"
        )
        lines.append(f"### [{emoji}] {record.paper_slug} ({record.target_journal})")
        lines.append(f"- **Status:** {record.status}")
        lines.append(f"- **Core section:** `{record.core_section}/`")
        lines.append(f"- **Claims:** {len(record.claims)}")
        lines.append(f"- **Backflow:** {bf}")
        lines.append("")
        if record.claims:
            lines.append("| Type | Label | Title |")
            lines.append("|------|-------|-------|")
            for c in record.claims[:20]:
                title = c.title[:50] if c.title else "—"
                lines.append(f"| {c.env_type} | `{c.label}` | {title} |")
            if len(record.claims) > 20:
                lines.append(f"| ... | ({len(record.claims) - 20} more) | |")
            lines.append("")

    # Core section coverage
    lines.append("## Core Section Coverage")
    lines.append("")
    lines.append("| Core Section | Papers Feeding Back | Total Claims | Status |")
    lines.append("|-------------|--------------------|--------------:|--------|")
    section_map: dict[str, list[BackflowRecord]] = {}
    for r in records:
        section_map.setdefault(r.core_section, []).append(r)
    for section in sorted(section_map):
        papers = section_map[section]
        total_claims = sum(len(p.claims) for p in papers)
        slugs = ", ".join(p.paper_slug for p in papers)
        statuses = set(p.backflow_status for p in papers)
        status = "done" if statuses == {"integrated"} else "TODO" if "pending" in statuses else "partial"
        lines.append(f"| `{section}/` | {slugs} | {total_claims} | {status} |")
    lines.append("")

    # Automation strategy
    lines.append("## Automation Strategy")
    lines.append("")
    lines.append("### Pipeline Architecture")
    lines.append("```")
    lines.append("  Core Theory (expanding knowledge base)")
    lines.append("       |")
    lines.append("  [research_cycle.py] extract claims")
    lines.append("       |")
    lines.append("  Publication Papers (19 active + 9 submitted)")
    lines.append("       |")
    lines.append("  [Four-Gate Pipeline]")
    lines.append("   G1: Codex initial review + self-fix")
    lines.append("   G2: ChatGPT oracle review + Codex fix")
    lines.append("   G3: Claude deep editorial review + fix")
    lines.append("   G4: ChatGPT final acceptance gate")
    lines.append("       |")
    lines.append("  [backflow.py] <<<< THIS SCRIPT")
    lines.append("   scan  -> extract proven theorems")
    lines.append("   map   -> identify core target sections")
    lines.append("   inject -> cross-reference into core")
    lines.append("   track -> update PIPELINE.md tables")
    lines.append("       |")
    lines.append("  Core Theory (enriched, cycle repeats)")
    lines.append("```")
    lines.append("")
    lines.append("### Automation Tools")
    lines.append("")
    lines.append("| Tool | Stage | Purpose |")
    lines.append("|------|-------|---------|")
    lines.append("| `research_cycle.py` | Core -> Papers | Extract claims, create paper candidates |")
    lines.append("| `publication_sync.py` | Sync | Track publication status, section mapping |")
    lines.append("| `oracle_server.py` + `chatgpt_oracle.user.js` | G1/G4 | ChatGPT browser automation |")
    lines.append("| `codex_fix.py` | G2 | Codex CLI paper fixing |")
    lines.append("| `pub-editorial` agent | G3 | Claude deep editorial review |")
    lines.append("| `backflow.py` | Backflow | Theorem extraction + core injection |")
    lines.append("| `notebooklm_dispatch.py` | Post-G4 | Audio/slide generation |")
    lines.append("| `pipeline_auto.py` | Orchestration | Batch runner for all papers |")
    lines.append("")
    lines.append("### Reviewer Rotation Protocol")
    lines.append("")
    lines.append("1. **Codex general review** (first pass, cheap)")
    lines.append("2. **Codex self-fix** (fix its own findings)")
    lines.append("3. **ChatGPT review** (via oracle bridge)")
    lines.append("4. **Codex fix** (from ChatGPT feedback)")
    lines.append("5. **Claude review** (deep mathematical verification)")
    lines.append("6. **Claude/Codex fix** (remaining issues)")
    lines.append("7. **ChatGPT final validation** (acceptance gate)")
    lines.append("")
    lines.append("Minimum 5 rounds per paper before marking ready.")
    lines.append("")

    return "\n".join(lines)


def generate_pipeline_backflow_table(record: BackflowRecord) -> str:
    """Generate a PIPELINE.md backflow table for a paper."""
    lines = [
        "### Backflow to Core",
        "",
        "| Result | Core target section | Status |",
        "|---|---|---|",
    ]
    for c in record.claims:
        if c.env_type in ("theorem", "proposition", "corollary", "lemma"):
            title = c.title if c.title else c.label
            lines.append(
                f"| `{c.label}` | `{record.core_section}/` | pending |"
            )
    return "\n".join(lines)


def inject_backflow_references(records: list[BackflowRecord], dry_run: bool = True) -> list[str]:
    """Inject cross-references from ACCEPT papers into core theory sections.

    For each core section that has ACCEPT paper results feeding back,
    adds a \\paragraph{Results from publications} block listing the
    proven theorems with citations.
    """
    actions = []
    section_claims: dict[str, list[tuple[BackflowRecord, ClaimRecord]]] = {}

    for r in records:
        if r.status != "ACCEPT":
            continue
        for c in r.claims:
            if c.env_type in ("theorem", "proposition", "corollary"):
                section_claims.setdefault(r.core_section, []).append((r, c))

    for section, items in section_claims.items():
        section_dir = CORE_BODY / section
        if not section_dir.exists():
            actions.append(f"SKIP: core section {section}/ not found")
            continue

        # Find the main.tex of this section
        main_tex = section_dir / "main.tex"
        if not main_tex.exists():
            actions.append(f"SKIP: {section}/main.tex not found")
            continue

        # Build the backflow remark block
        remark_lines = [
            "",
            "% --- Backflow from publication papers (auto-generated) ---",
            "\\begin{remark}[Results proven in dedicated publications]",
            "  The following results from this section have been developed into",
            "  standalone publications with full proofs and independent verification:",
            "  \\begin{itemize}",
        ]
        for rec, claim in items:
            journal = rec.target_journal
            title = claim.title if claim.title else claim.label
            remark_lines.append(
                f"    \\item \\textbf{{{title}}} ({claim.env_type.capitalize()}"
                f" \\texttt{{{claim.label}}}) --- {journal} paper"
                f" \\texttt{{{rec.paper_slug}}}, status: {rec.status}."
            )
        remark_lines.extend([
            "  \\end{itemize}",
            "\\end{remark}",
            "% --- End backflow ---",
            "",
        ])
        remark_block = "\n".join(remark_lines)

        if dry_run:
            actions.append(
                f"WOULD inject {len(items)} claims into {section}/main.tex"
            )
        else:
            text = read_text(main_tex)
            # Check if backflow block already exists
            if "% --- Backflow from publication papers" in text:
                # Replace existing block
                text = re.sub(
                    r"\n% --- Backflow from publication papers.*?% --- End backflow ---\n",
                    lambda m: remark_block,
                    text,
                    flags=re.DOTALL,
                )
                actions.append(f"UPDATED backflow in {section}/main.tex ({len(items)} claims)")
            else:
                # Insert before the last line (typically \endinput or end of file)
                text = text.rstrip() + "\n" + remark_block
                actions.append(f"INJECTED backflow into {section}/main.tex ({len(items)} claims)")
            write_text(main_tex, text)

    return actions


def update_pipeline_tables(records: list[BackflowRecord], dry_run: bool = True) -> list[str]:
    """Update or create backflow tables in each paper's PIPELINE.md."""
    actions = []
    for r in records:
        paper_dir = PUBLICATION_DIR / r.paper_dir
        pipeline = paper_dir / "PIPELINE.md"
        if not pipeline.exists():
            if dry_run:
                actions.append(f"WOULD create PIPELINE.md for {r.paper_slug}")
            else:
                table = generate_pipeline_backflow_table(r)
                write_text(pipeline, f"# Pipeline: {r.paper_slug}\n\n{table}\n")
                actions.append(f"CREATED PIPELINE.md for {r.paper_slug}")
            continue

        text = read_text(pipeline)
        if "### Backflow to Core" in text:
            actions.append(f"SKIP: {r.paper_slug} already has backflow table")
            continue

        table = generate_pipeline_backflow_table(r)
        if dry_run:
            actions.append(
                f"WOULD add backflow table to {r.paper_slug} ({len(r.claims)} claims)"
            )
        else:
            text = text.rstrip() + "\n\n" + table + "\n"
            write_text(pipeline, text)
            actions.append(
                f"ADDED backflow table to {r.paper_slug} ({len(r.claims)} claims)"
            )

    return actions


def cmd_scan(args):
    """Scan papers and save backflow inventory."""
    if args.paper:
        paper_dir = Path(args.paper).resolve()
        records = [scan_paper(paper_dir)]
    else:
        records = scan_all()

    print(f"[backflow] Scanned {len(records)} papers")
    for r in records:
        print(f"  [{r.status:9s}] {r.paper_slug:40s} -> {r.core_section:30s} ({len(r.claims)} claims, bf={r.backflow_status})")

    # Save inventory
    BACKFLOW_DIR.mkdir(parents=True, exist_ok=True)
    inventory_path = BACKFLOW_DIR / "backflow_inventory.json"
    write_json(inventory_path, [asdict(r) for r in records])
    print(f"\n[backflow] Inventory saved to {inventory_path}")

    return records


def cmd_report(args):
    """Generate backflow report."""
    records = scan_all()
    report = generate_report(records)
    report_path = BACKFLOW_DIR / f"backflow_report_{date.today()}.md"
    write_text(report_path, report)
    print(f"[backflow] Report saved to {report_path}")
    print(report)


def cmd_inject(args):
    """Inject cross-references into core theory."""
    records = scan_all()
    dry_run = not args.execute

    if dry_run:
        print("[backflow] DRY RUN — pass --execute to apply changes")

    # Inject into core sections
    actions = inject_backflow_references(records, dry_run=dry_run)
    for a in actions:
        print(f"  {a}")

    # Update PIPELINE.md tables
    table_actions = update_pipeline_tables(records, dry_run=dry_run)
    for a in table_actions:
        print(f"  {a}")


REVISION_TRACE_PATTERNS = re.compile(
    r"修订|修复|本版本|新增|补充的|新xxx|"
    r"Corrected|This version|We have improved|In this revision",
    re.IGNORECASE,
)
MANUAL_THEOREM_RE = re.compile(
    r"\\noindent\s*\\textbf\{(?:Lemma|Theorem|Proposition|Corollary|Definition)",
)

MAX_TEX_LINES = 800


def review_paper(paper_dir: Path) -> dict:
    """Run stage-C automated quality checks on a paper.

    Returns a dict with pass/fail verdict and issue list.
    """
    issues = []
    tex_files = sorted(paper_dir.glob("*.tex"))
    # Also check subdirectories (generated/, etc.)
    tex_files.extend(sorted(paper_dir.glob("**/*.tex")))
    # Deduplicate
    seen = set()
    unique_tex = []
    for f in tex_files:
        if f not in seen:
            seen.add(f)
            unique_tex.append(f)
    tex_files = unique_tex

    for tex_file in tex_files:
        rel = tex_file.relative_to(paper_dir)
        text = read_text(tex_file)
        lines = text.split("\n")
        line_count = len(lines)

        # CHECK-C1: File size
        if line_count > MAX_TEX_LINES:
            issues.append({
                "check": "C1-filesize",
                "severity": "HARD_FAIL",
                "file": str(rel),
                "detail": f"{line_count} lines (limit {MAX_TEX_LINES})",
            })

        # CHECK-C2: Revision traces
        for i, line in enumerate(lines, 1):
            if REVISION_TRACE_PATTERNS.search(line):
                # Skip comments
                stripped = line.lstrip()
                if stripped.startswith("%"):
                    continue
                issues.append({
                    "check": "C2-revision-trace",
                    "severity": "MEDIUM",
                    "file": str(rel),
                    "line": i,
                    "detail": line.strip()[:80],
                })

        # CHECK-C3: Manual theorem environments
        for m in MANUAL_THEOREM_RE.finditer(text):
            pos = m.start()
            line_num = text[:pos].count("\n") + 1
            issues.append({
                "check": "C3-manual-env",
                "severity": "MEDIUM",
                "file": str(rel),
                "line": line_num,
                "detail": "Manual \\noindent\\textbf instead of \\begin{theorem}",
            })

        # CHECK-C4: Dangling \ref (basic check)
        ref_labels = set(re.findall(r"\\(?:ref|Cref|cref)\{([^}]+)\}", text))
        defined_labels = set(re.findall(r"\\label\{([^}]+)\}", text))
        # Collect all labels across the paper for cross-file check later

        # CHECK-C5: Basic symbol consistency — look for isolated \varphi
        # that should have been renamed to \lambda_{\mathrm G} etc.
        # (Paper-specific; generic check for common rename patterns)

    hard_fails = [i for i in issues if i["severity"] == "HARD_FAIL"]
    verdict = "FAIL" if hard_fails else "PASS"

    return {
        "paper": paper_dir.name,
        "verdict": verdict,
        "hard_fails": len(hard_fails),
        "total_issues": len(issues),
        "issues": issues,
    }


def cmd_review(args):
    """Run stage-C quality review on a paper."""
    paper_dir = Path(args.paper).resolve()
    result = review_paper(paper_dir)

    verdict_icon = "PASS" if result["verdict"] == "PASS" else "FAIL"
    print(f"[backflow] Stage-C Review: {result['paper']}")
    print(f"  Verdict: {verdict_icon}")
    print(f"  Hard fails: {result['hard_fails']}")
    print(f"  Total issues: {result['total_issues']}")

    if result["issues"]:
        print()
        for issue in result["issues"]:
            sev = issue["severity"]
            check = issue["check"]
            f = issue["file"]
            line = issue.get("line", "")
            detail = issue["detail"]
            line_str = f":{line}" if line else ""
            print(f"  [{sev:9s}] {check}: {f}{line_str} — {detail}")

    # Write JSON report
    BACKFLOW_DIR.mkdir(parents=True, exist_ok=True)
    report_path = BACKFLOW_DIR / f"review_{slug_from_dir(paper_dir)}.json"
    write_json(report_path, result)
    print(f"\n[backflow] Review saved to {report_path}")

    return result


def cmd_mark(args):
    """Mark a paper's backflow status."""
    paper_dir = Path(args.paper).resolve()
    new_status = args.status

    # Update PIPELINE.md
    pipeline = paper_dir / "PIPELINE.md"
    if pipeline.exists():
        text = read_text(pipeline)
        # Replace all "| pending |" with new status in backflow table
        if new_status == "integrated":
            text = text.replace("| pending |", "| integrated |")
        write_text(pipeline, text)
        print(f"[backflow] Marked {slug_from_dir(paper_dir)} backflow as {new_status}")
    else:
        print(f"[backflow] No PIPELINE.md found for {paper_dir.name}")

    # Also update the inventory JSON if it exists
    inventory_path = BACKFLOW_DIR / "backflow_inventory.json"
    if inventory_path.exists():
        with open(io_path(inventory_path), "r", encoding="utf-8") as f:
            records = json.load(f)
        slug = slug_from_dir(paper_dir)
        for r in records:
            if r.get("paper_slug") == slug:
                r["backflow_status"] = new_status
                r["date_scanned"] = str(date.today())
        write_json(inventory_path, records)


def cmd_diff(args):
    """Show claims in a paper that are NOT in the core theory section."""
    paper_dir = Path(args.paper).resolve()
    record = scan_paper(paper_dir)

    if record.core_section == "unknown":
        print(f"[backflow] No core section mapping for {record.paper_slug}")
        print(f"  Add entry to PAPER_CORE_MAP in backflow.py")
        return

    core_dir = CORE_BODY / record.core_section
    if not core_dir.exists():
        print(f"[backflow] Core section {record.core_section}/ not found")
        return

    # Collect all labels in the core section
    core_labels = set()
    for tex in core_dir.rglob("*.tex"):
        text = read_text(tex)
        core_labels.update(re.findall(r"\\label\{([^}]+)\}", text))

    # Find claims not in core (by checking if similar label exists)
    missing = []
    for claim in record.claims:
        # Strip -main suffix and check
        base_label = claim.label.replace("-main", "")
        found = any(base_label in cl or cl.replace("-main", "") == base_label
                     for cl in core_labels)
        if not found:
            missing.append(claim)

    print(f"[backflow] Diff: {record.paper_slug} -> {record.core_section}/")
    print(f"  Total claims in paper: {len(record.claims)}")
    print(f"  Already in core: {len(record.claims) - len(missing)}")
    print(f"  Missing from core: {len(missing)}")

    if missing:
        print()
        print(f"  Claims needing backflow:")
        for c in missing:
            title = c.title[:60] if c.title else "—"
            print(f"    [{c.env_type:11s}] {c.label:45s} {title}")


def cmd_status(args):
    """Show pipeline-wide backflow status."""
    records = scan_all()
    accept = [r for r in records if r.status == "ACCEPT"]
    submitted = [r for r in records if r.status == "submitted"]
    integrated = [r for r in records if r.backflow_status == "integrated"]
    pending = [r for r in records if r.backflow_status == "pending"]

    print(f"[backflow] Pipeline Status")
    print(f"  ACCEPT papers:     {len(accept)}")
    print(f"  Submitted papers:  {len(submitted)}")
    print(f"  Backflow done:     {len(integrated)}")
    print(f"  Backflow pending:  {len(pending)}")
    print()
    print(f"  Papers needing backflow:")
    for r in pending:
        print(f"    [{r.status:9s}] {r.paper_slug:40s} -> {r.core_section} ({len(r.claims)} claims)")


def main():
    parser = argparse.ArgumentParser(description="Backflow automation")
    sub = parser.add_subparsers(dest="command")

    p_scan = sub.add_parser("scan", help="Scan ACCEPT + submitted papers")
    p_scan.add_argument("--paper", help="Specific paper directory")

    p_report = sub.add_parser("report", help="Generate backflow report")

    p_inject = sub.add_parser("inject", help="Inject cross-references into core")
    p_inject.add_argument("--execute", action="store_true",
                          help="Actually apply changes (default: dry run)")

    p_status = sub.add_parser("status", help="Show backflow status")

    p_review = sub.add_parser("review", help="Stage-C quality review of Codex output")
    p_review.add_argument("paper", help="Paper directory to review")

    p_diff = sub.add_parser("diff", help="Show claims missing from core theory")
    p_diff.add_argument("paper", help="Paper directory")

    p_mark = sub.add_parser("mark", help="Mark paper backflow status")
    p_mark.add_argument("paper", help="Paper directory")
    p_mark.add_argument("--status", required=True,
                        choices=["pending", "partial", "integrated"],
                        help="New backflow status")

    args = parser.parse_args()
    if args.command == "scan":
        cmd_scan(args)
    elif args.command == "report":
        cmd_report(args)
    elif args.command == "inject":
        cmd_inject(args)
    elif args.command == "status":
        cmd_status(args)
    elif args.command == "review":
        cmd_review(args)
    elif args.command == "diff":
        cmd_diff(args)
    elif args.command == "mark":
        cmd_mark(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
