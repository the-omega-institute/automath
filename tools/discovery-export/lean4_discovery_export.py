#!/usr/bin/env python3
"""Discovery Report Export — extract theorem + proof from Lean 4 modules → JSON.

Parses all 11 Omega modules, extracts theorem/lemma/def declarations with
proofs, docstrings, and paper labels, then generates a discovery report JSON.

Usage:
    python lean4_discovery_export.py                    # Export all modules
    python lean4_discovery_export.py --module Zeta      # Export single module
    python lean4_discovery_export.py --stats             # Print statistics only
    python lean4_discovery_export.py --out report.json   # Custom output path

Schema per entry (ADR-008):
    discovery_id   : UUID (deterministic from module + theorem name)
    lean_module    : e.g. "Omega.Zeta.DynZeta"
    lean_file      : relative path from lean4/
    lean_theorem   : declaration name
    lean_type      : theorem | lemma | def | abbrev | instance
    lean_statement : type signature (the proposition)
    lean_proof     : proof term or tactic block
    docstring      : full docstring text
    paper_labels   : extracted cross-reference labels (prop:..., thm:..., etc.)
    exploration_context : "pre-registry" for backfill, or label-derived context
    is_novel       : true if in Frontier/Conjectures module
    git_commit     : latest commit touching this file
    git_date       : date of that commit
    imports        : list of import paths for dependency edges
"""

import argparse
import json
import re
import subprocess
import sys
import uuid
from pathlib import Path

LEAN4_DIR = Path(__file__).resolve().parent.parent.parent / "lean4"
OMEGA_DIR = LEAN4_DIR / "Omega"
OUTPUT_DIR = Path(__file__).resolve().parent / "discovery"

MODULES = [
    "CircleDimension", "Combinatorics", "Core", "EA", "Folding",
    "Frontier", "GU", "Graph", "SPG", "Zeta",
]

# Declaration patterns
DECL_RE = re.compile(
    r"^(theorem|lemma|def|abbrev|instance)\s+(\S+)",
    re.MULTILINE,
)
DOCSTRING_RE = re.compile(r"/--(.+?)-/", re.DOTALL)
LABEL_RE = re.compile(r"((?:def|prop|thm|lem|cor|rem|sec|subsec):[\w\-]+)")
IMPORT_RE = re.compile(r"^import\s+(.+)$", re.MULTILINE)

NOVEL_MODULES = {"Frontier", "Conjectures"}


def deterministic_uuid(module: str, name: str) -> str:
    """Generate a deterministic UUID5 from module + theorem name."""
    ns = uuid.UUID("d4e7c2a0-1234-5678-9abc-def012345678")
    return str(uuid.uuid5(ns, f"{module}::{name}"))


def git_info(filepath: Path) -> tuple[str, str]:
    """Get latest commit hash and date for a file."""
    try:
        result = subprocess.run(
            ["git", "log", "-1", "--format=%H %aI", "--", str(filepath)],
            capture_output=True, text=True, cwd=LEAN4_DIR, timeout=10,
        )
        if result.returncode == 0 and result.stdout.strip():
            parts = result.stdout.strip().split(" ", 1)
            return parts[0], parts[1] if len(parts) > 1 else ""
    except Exception:
        pass
    return "", ""


def parse_lean_file(filepath: Path) -> list[dict]:
    """Parse a single .lean file and extract all declarations."""
    text = filepath.read_text(encoding="utf-8", errors="replace")
    lines = text.split("\n")

    rel_path = filepath.relative_to(LEAN4_DIR)
    module_path = str(rel_path).replace("/", ".").replace("\\", ".").removesuffix(".lean")

    # Determine parent module name
    parts = rel_path.parts
    parent_module = parts[1] if len(parts) > 2 else parts[0]

    # Extract imports
    imports = [m.group(1).strip() for m in IMPORT_RE.finditer(text)]

    # Git info (cached per file)
    commit, date = git_info(filepath)

    # Find all docstrings with their end positions
    docstrings = []
    for m in DOCSTRING_RE.finditer(text):
        docstrings.append((m.end(), m.group(1).strip()))

    # Find all declarations
    entries = []
    decl_positions = list(DECL_RE.finditer(text))

    for i, m in enumerate(decl_positions):
        decl_type = m.group(1)
        decl_name = m.group(2)
        decl_start = m.start()
        decl_line = text[:decl_start].count("\n")

        # Find the end of this declaration (start of next decl, or section markers)
        if i + 1 < len(decl_positions):
            # Look backwards from next decl for docstring start
            next_start = decl_positions[i + 1].start()
            # Check if there's a docstring before next decl
            pre_next = text[m.end():next_start]
            doc_match = re.search(r"/--", pre_next)
            if doc_match:
                decl_end = m.end() + doc_match.start()
            else:
                decl_end = next_start
        else:
            decl_end = len(text)

        # Extract full declaration text
        full_text = text[decl_start:decl_end].rstrip()

        # Split into statement and proof
        statement, proof = _split_statement_proof(full_text)

        # Find associated docstring (closest one ending before this declaration)
        docstring = ""
        for doc_end, doc_text in reversed(docstrings):
            if doc_end <= decl_start + 5:  # allow small gap
                # Check this docstring is close (within 3 lines)
                gap_text = text[doc_end:decl_start]
                if gap_text.count("\n") <= 3:
                    docstring = doc_text
                break

        # Extract paper labels from docstring
        paper_labels = LABEL_RE.findall(docstring) if docstring else []

        # Determine exploration context
        if paper_labels:
            context = "; ".join(paper_labels)
        else:
            context = "pre-registry"

        is_novel = parent_module in NOVEL_MODULES

        entries.append({
            "discovery_id": deterministic_uuid(module_path, decl_name),
            "lean_module": module_path,
            "lean_file": str(rel_path).replace("\\", "/"),
            "lean_theorem": decl_name,
            "lean_type": decl_type,
            "lean_statement": statement.strip(),
            "lean_proof": proof.strip(),
            "docstring": docstring,
            "paper_labels": paper_labels,
            "exploration_context": context,
            "is_novel": is_novel,
            "git_commit": commit,
            "git_date": date,
            "line_number": decl_line + 1,
        })

    return entries, imports


def _split_statement_proof(text: str) -> tuple[str, str]:
    """Split a declaration into statement (type signature) and proof."""
    # Pattern: ... := by\n  <tactics>
    by_match = re.search(r":=\s*by\b", text)
    if by_match:
        statement = text[:by_match.start()].strip()
        proof = text[by_match.start():].strip()
        return statement, proof

    # Pattern: ... := <term>
    eq_match = re.search(r":=\s", text)
    if eq_match:
        statement = text[:eq_match.start()].strip()
        proof = text[eq_match.start():].strip()
        return statement, proof

    # No proof (e.g. axiom, opaque)
    return text.strip(), ""


def scan_module(module_name: str) -> tuple[list[dict], dict]:
    """Scan all .lean files in a module directory."""
    module_dir = OMEGA_DIR / module_name
    if not module_dir.is_dir():
        print(f"  WARN: Module directory not found: {module_dir}")
        return [], {}

    all_entries = []
    dep_graph = {}

    lean_files = sorted(module_dir.glob("**/*.lean"))
    for f in lean_files:
        entries, imports = parse_lean_file(f)
        rel = str(f.relative_to(LEAN4_DIR)).replace("\\", "/")
        dep_graph[rel] = imports
        all_entries.extend(entries)

    return all_entries, dep_graph


def main():
    parser = argparse.ArgumentParser(description="Lean 4 Discovery Report Export")
    parser.add_argument("--module", help="Scan single module (e.g. Zeta)")
    parser.add_argument("--out", help="Output JSON path")
    parser.add_argument("--stats", action="store_true", help="Print statistics only")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON")
    args = parser.parse_args()

    modules = [args.module] if args.module else MODULES

    all_entries = []
    all_deps = {}
    module_stats = {}

    for mod in modules:
        print(f"Scanning {mod}...", end=" ", flush=True)
        entries, deps = scan_module(mod)
        all_entries.extend(entries)
        all_deps.update(deps)

        # Stats
        type_counts = {}
        for e in entries:
            type_counts[e["lean_type"]] = type_counts.get(e["lean_type"], 0) + 1
        module_stats[mod] = {
            "total": len(entries),
            "files": len(deps),
            "by_type": type_counts,
        }
        print(f"{len(entries)} declarations in {len(deps)} files")

    # Summary
    total = len(all_entries)
    with_labels = sum(1 for e in all_entries if e["paper_labels"])
    novel = sum(1 for e in all_entries if e["is_novel"])
    print(f"\nTotal: {total} declarations, {with_labels} with paper labels, {novel} novel")

    if args.stats:
        for mod, stats in module_stats.items():
            print(f"  {mod}: {stats['total']} ({stats['by_type']})")
        return

    # Build report
    report = {
        "schema_version": "ADR-008-v1",
        "export_date": subprocess.run(
            ["git", "log", "-1", "--format=%aI"],
            capture_output=True, text=True, cwd=LEAN4_DIR,
        ).stdout.strip(),
        "total_declarations": total,
        "module_stats": module_stats,
        "dependency_graph": all_deps,
        "discoveries": all_entries,
    }

    # Output
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    out_path = Path(args.out) if args.out else OUTPUT_DIR / "discovery_report.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    indent = 2 if args.pretty else None
    out_path.write_text(
        json.dumps(report, indent=indent, ensure_ascii=False),
        encoding="utf-8",
    )
    print(f"\nReport written to {out_path} ({out_path.stat().st_size / 1024:.0f} KB)")


if __name__ == "__main__":
    main()
