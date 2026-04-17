#!/usr/bin/env python3
"""Scan lean4/Omega for 'abstract-Prop shell' files, extract their DAG, and classify.

Shell pattern (R1100+ codex-first output):
  structure FooData where
    fieldA : Prop           -- node: abstract
    fieldB : Prop           -- node: abstract
    fieldA_h : fieldA       -- leaf hypothesis
    deriveFieldC : fieldA -> fieldB -> fieldC   -- derivation arrow
  theorem paper_xyz (D : FooData) : D.fieldC := ...

Classification:
  A = fully abstract shell  (only Prop/hyp/derive fields; trivial tautology)
  B = partially concrete    (has some concrete ℕ/ℝ/Finset/etc fields; keep by default)
  skip = no matching Data structure

Report is written to lean4/scripts/salvaged_dags/REPORT.md, and one DAG-per-file
under salvaged_dags/<module-with-dots>.md for Class-A files.
"""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

SCRIPT_DIR = Path(__file__).resolve().parent
LEAN_ROOT = SCRIPT_DIR.parent
OMEGA_ROOT = LEAN_ROOT / "Omega"
OUT_DIR = SCRIPT_DIR / "salvaged_dags"
REPORT = OUT_DIR / "REPORT.md"

# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

STRUCT_RE = re.compile(r"^structure\s+(\w+Data)\s+where\s*$", re.MULTILINE)
THM_RE = re.compile(
    r"^theorem\s+(paper_\w+)\s*((?:\([^)]*\)\s*)*)\s*:\s*(.+?)\s*:=",
    re.MULTILINE | re.DOTALL,
)
PAPER_LABEL_RE = re.compile(r"((?:thm|prop|lemma):[a-z0-9\-]+)", re.IGNORECASE)


@dataclass
class Field:
    name: str
    type_str: str
    category: str  # 'prop', 'hyp', 'derive', 'concrete'


@dataclass
class FileInfo:
    path: Path
    module: str
    struct_name: str = ""
    doc: str = ""
    fields: list[Field] = field(default_factory=list)
    theorem_name: str = ""
    theorem_goal: str = ""
    theorem_doc: str = ""
    paper_label: str = ""
    classification: str = "skip"  # 'A', 'B', 'skip'


def module_name(p: Path) -> str:
    rel = p.relative_to(LEAN_ROOT)
    return ".".join(rel.with_suffix("").parts)


def parse_fields(body: str, node_names: set[str]) -> list[Field]:
    """Very tolerant field parser.

    Fields are lines indented two spaces (relative to `structure … where`).
    Types may span multiple lines if continuation lines are indented deeper.
    """
    lines = body.splitlines()
    fields: list[Field] = []
    cur: Optional[list[str]] = None
    cur_name: Optional[str] = None

    def flush() -> None:
        if cur_name and cur:
            type_str = " ".join(s.strip() for s in cur).strip()
            fields.append(Field(cur_name, type_str, ""))

    for ln in lines:
        if not ln.strip():
            continue
        m = re.match(r"^  (\w+)\s*:\s*(.*)$", ln)
        if m:
            flush()
            cur_name = m.group(1)
            cur = [m.group(2)]
        elif cur is not None and re.match(r"^    \S", ln):
            # continuation
            cur.append(ln.strip())
    flush()

    # Classify
    for f in fields:
        t = f.type_str.strip()
        if t == "Prop":
            f.category = "prop"
        elif f.name.endswith("_h") and t in node_names:
            f.category = "hyp"
        elif f.name.startswith("derive") and "→" in t:
            # Check that all arrow segments are node names
            parts = [p.strip() for p in t.split("→")]
            if all(p in node_names for p in parts):
                f.category = "derive"
            else:
                f.category = "concrete"
        else:
            f.category = "concrete"
    return fields


def extract_docstring_before(text: str, pos: int) -> str:
    """Return the content of the `/-- ... -/` doc block ending just before pos."""
    # Search backwards from pos for `-/`
    end = text.rfind("-/", 0, pos)
    if end == -1:
        return ""
    # Heuristic: make sure only whitespace between `-/` and pos
    between = text[end + 2 : pos]
    if between.strip():
        return ""
    start = text.rfind("/--", 0, end)
    if start == -1:
        return ""
    return text[start + 3 : end].strip()


def parse_file(p: Path) -> FileInfo:
    info = FileInfo(path=p, module=module_name(p))
    try:
        text = p.read_text(encoding="utf-8")
    except Exception:
        return info

    sm = STRUCT_RE.search(text)
    if not sm:
        return info

    info.struct_name = sm.group(1)
    info.doc = extract_docstring_before(text, sm.start())

    # Extract structure body: from end of `structure … where` line to next
    # top-level statement (column-0 line).
    body_start = sm.end()
    # Find next column-0 line
    rest = text[body_start:]
    tail = re.search(r"^\S", rest, re.MULTILINE)
    body = rest[: tail.start()] if tail else rest

    # Pass 1: collect node names (bare Prop fields)
    node_names: set[str] = set()
    for ln in body.splitlines():
        m = re.match(r"^  (\w+)\s*:\s*Prop\s*$", ln)
        if m:
            node_names.add(m.group(1))

    info.fields = parse_fields(body, node_names)

    # Theorem
    for tm in THM_RE.finditer(text):
        tname = tm.group(1)
        tgoal = " ".join(tm.group(3).split())
        info.theorem_name = tname
        info.theorem_goal = tgoal
        info.theorem_doc = extract_docstring_before(text, tm.start())
        lm = PAPER_LABEL_RE.search(info.theorem_doc)
        if lm:
            info.paper_label = lm.group(1)
        break

    # Classification
    kinds = {f.category for f in info.fields}
    has_concrete = any(f.category == "concrete" for f in info.fields)
    has_prop = any(f.category == "prop" for f in info.fields)
    if has_prop and not has_concrete:
        info.classification = "A"
    elif has_prop and has_concrete:
        info.classification = "B"
    else:
        info.classification = "skip"

    return info


# ---------------------------------------------------------------------------
# Report
# ---------------------------------------------------------------------------

def dag_markdown(info: FileInfo) -> str:
    nodes = [f.name for f in info.fields if f.category == "prop"]
    leaves = [f.name[:-2] for f in info.fields if f.category == "hyp"]
    edges: list[tuple[list[str], str]] = []
    for f in info.fields:
        if f.category != "derive":
            continue
        parts = [p.strip() for p in f.type_str.split("→")]
        if len(parts) >= 2:
            edges.append((parts[:-1], parts[-1]))
    derived = {tgt for _, tgt in edges}
    terminals = [n for n in nodes if n not in {*leaves}]  # non-leaf: either derived or goal
    lines = [
        f"# {info.module}",
        "",
        f"- File: `{info.path.relative_to(LEAN_ROOT)}`",
        f"- Struct: `{info.struct_name}`",
        f"- Paper label: `{info.paper_label or '?'}`",
        f"- Goal theorem: `{info.theorem_name or '?'}`",
        "",
        "## Structure docstring",
        "",
        info.doc or "(none)",
        "",
        "## Goal",
        "",
        f"`{info.theorem_goal or '?'}`",
        "",
        "## Theorem docstring",
        "",
        info.theorem_doc or "(none)",
        "",
        "## DAG",
        "",
        "Nodes (Prop fields):",
    ]
    for n in nodes:
        tag = []
        if n in leaves:
            tag.append("leaf")
        if n in derived:
            tag.append("derived")
        lines.append(f"- `{n}`" + (f" ({', '.join(tag)})" if tag else ""))
    lines += ["", "Edges:"]
    if not edges:
        lines.append("- (none)")
    for srcs, tgt in edges:
        lines.append(f"- {' + '.join(srcs)}  →  **{tgt}**")
    lines += ["", "## Imports"]
    try:
        for ln in info.path.read_text(encoding="utf-8").splitlines():
            if ln.startswith("import "):
                lines.append(f"- `{ln[len('import '):].strip()}`")
    except Exception:
        pass
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    files = sorted(OMEGA_ROOT.rglob("*.lean"))
    parsed: list[FileInfo] = [parse_file(p) for p in files]
    class_a = [i for i in parsed if i.classification == "A"]
    class_b = [i for i in parsed if i.classification == "B"]

    # Write per-file DAG for Class A
    for info in class_a:
        out = OUT_DIR / f"{info.module}.md"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(dag_markdown(info), encoding="utf-8")

    # Summary report
    lines = [
        "# Abstract-Prop shell salvage report",
        "",
        f"Scanned: {len(files)} files under `Omega/`",
        f"Class A (full shell, safe to delete after salvage): **{len(class_a)}**",
        f"Class B (partial shell, keep for review):            **{len(class_b)}**",
        "",
        "## Class A — to be deleted",
        "",
    ]
    for i in class_a:
        lines.append(f"- `{i.path.relative_to(LEAN_ROOT)}` — `{i.theorem_name}` (`{i.paper_label or '?'}`)")
    lines += ["", "## Class B — keep, inspect manually", ""]
    for i in class_b:
        concretes = [f"{f.name}:{f.type_str}" for f in i.fields if f.category == "concrete"]
        lines.append(
            f"- `{i.path.relative_to(LEAN_ROOT)}` — `{i.theorem_name}` "
            f"({len(concretes)} concrete field(s))"
        )

    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"Class A: {len(class_a)}")
    print(f"Class B: {len(class_b)}")
    print(f"Report:  {REPORT}")
    # Also emit JSON for downstream automation
    (OUT_DIR / "classification.json").write_text(
        json.dumps(
            {
                "classA": [str(i.path.relative_to(LEAN_ROOT)) for i in class_a],
                "classB": [str(i.path.relative_to(LEAN_ROOT)) for i in class_b],
                "classA_theorems": [i.theorem_name for i in class_a],
                "classA_labels": [i.paper_label for i in class_a],
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
