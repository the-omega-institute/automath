#!/usr/bin/env python3
"""Delete Class-A abstract-Prop shell files and remove their \\leanverified/\\leanpartial
annotations from the paper .tex files.

Inputs:  lean4/scripts/salvaged_dags/classification.json
Outputs:
  - Deletes listed .lean files under lean4/Omega/
  - Removes `import <module>` lines from aggregator / sibling .lean files
  - Strips matching lines from .tex files under theory/
  - Prints a summary

Dry-run: `--dry-run` prints what would change.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
LEAN_ROOT = SCRIPT_DIR.parent
REPO_ROOT = LEAN_ROOT.parent
CLASSIFICATION = SCRIPT_DIR / "salvaged_dags" / "classification.json"
THEORY_ROOT = REPO_ROOT / "theory"
OMEGA_ROOT = LEAN_ROOT / "Omega"


def module_of(lean_path: str) -> str:
    # lean_path is like "Omega/EA/Foo.lean" (relative to lean4/)
    return lean_path.replace("/", ".").replace(".lean", "")


def tex_escape_underscore(name: str) -> str:
    return name.replace("_", r"\_")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    data = json.loads(CLASSIFICATION.read_text(encoding="utf-8"))
    raw_lean_paths: list[str] = data["classA"]
    raw_theorem_names: list[str] = data["classA_theorems"]

    # Exclude files whose removal would break external (non-Class-A, non-aggregator)
    # dependents. These must be resolved as a separate cascade.
    SKIP = {
        "Omega/TypedAddressBiaxialCompletion/ComovingFourierClosed.lean",
    }
    lean_paths = [p for p in raw_lean_paths if p not in SKIP]
    theorem_names = [
        t for p, t in zip(raw_lean_paths, raw_theorem_names) if p not in SKIP
    ]

    modules = [module_of(p) for p in lean_paths]
    modules_set = set(modules)

    # Build escaped theorem names for .tex matching
    escaped_names = [tex_escape_underscore(t) for t in theorem_names if t]

    # --- .tex cleanup ---------------------------------------------------------
    tex_removed = 0
    tex_files_changed = 0

    # Pattern: ^\s*\\(leanverified|leanpartial)\{paper\_…\}(\{…\})?\s*$
    # Build a single regex from the escaped names
    name_alt = "|".join(re.escape(n) for n in escaped_names)
    if name_alt:
        line_re = re.compile(
            r"^\s*\\(leanverified|leanpartial)\{(" + name_alt + r")\}"
            r"(?:\{[^}]*\})?\s*$"
        )
    else:
        line_re = None

    if line_re:
        for tex in THEORY_ROOT.rglob("*.tex"):
            try:
                text = tex.read_text(encoding="utf-8")
            except Exception:
                continue
            new_lines = []
            changed = False
            n_removed = 0
            for ln in text.splitlines(keepends=True):
                if line_re.match(ln.rstrip("\n")):
                    n_removed += 1
                    changed = True
                    continue
                new_lines.append(ln)
            if changed:
                tex_removed += n_removed
                tex_files_changed += 1
                print(f"  tex: {tex.relative_to(REPO_ROOT)} (-{n_removed})")
                if not args.dry_run:
                    tex.write_text("".join(new_lines), encoding="utf-8")

    # --- .lean import cleanup ------------------------------------------------
    import_removed = 0
    lean_files_changed = 0
    for lean in OMEGA_ROOT.rglob("*.lean"):
        # Skip the files we're going to delete
        rel = str(lean.relative_to(LEAN_ROOT))
        if rel in lean_paths:
            continue
        try:
            text = lean.read_text(encoding="utf-8")
        except Exception:
            continue
        new_lines = []
        changed = False
        for ln in text.splitlines(keepends=True):
            stripped = ln.rstrip("\n").strip()
            if stripped.startswith("import "):
                target = stripped[len("import "):].strip()
                if target in modules_set:
                    import_removed += 1
                    changed = True
                    continue
            new_lines.append(ln)
        if changed:
            lean_files_changed += 1
            print(f"  lean-imp: {lean.relative_to(LEAN_ROOT)}")
            if not args.dry_run:
                lean.write_text("".join(new_lines), encoding="utf-8")

    # --- .lean file deletion -------------------------------------------------
    deleted = 0
    for lp in lean_paths:
        p = LEAN_ROOT / lp
        if p.exists():
            print(f"  delete: {lp}")
            if not args.dry_run:
                p.unlink()
            deleted += 1

    # --- Summary -------------------------------------------------------------
    print()
    print("Summary:")
    print(f"  .lean files deleted:          {deleted}")
    print(f"  .lean import lines removed:   {import_removed}  (in {lean_files_changed} file(s))")
    print(f"  .tex annotation lines removed: {tex_removed}  (in {tex_files_changed} file(s))")
    if args.dry_run:
        print("  (dry run — no changes written)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
