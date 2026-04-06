#!/usr/bin/env python3
"""Create standalone GitHub repositories for submitted papers.

For each submitted_2026_* paper directory, creates a public GitHub repo
under the-omega-institute org with:
- All paper source files (tex, bib, scripts, figures)
- Auto-generated README.md with title, abstract, theorem inventory
- .gitignore for LaTeX artifacts
- LICENSE (MIT)

Usage:
    python create_paper_repos.py --list                # List papers and proposed repo names
    python create_paper_repos.py --paper <dir>         # Create repo for one paper
    python create_paper_repos.py --all                 # Create repos for all submitted papers
    python create_paper_repos.py --all --dry-run       # Preview without creating
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

PUBLICATION_DIR = Path(__file__).resolve().parent
ORG = "the-omega-institute"

LATEX_GITIGNORE = """\
*.aux
*.bbl
*.bcf
*.blg
*.fdb_latexmk
*.fls
*.log
*.out
*.pdf
*.run.xml
*.synctex.gz
*.toc
*.pyc
__pycache__/
"""

MIT_LICENSE = """\
MIT License

Copyright (c) 2026 The Omega Institute

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"""


def extract_paper_metadata(paper_dir: Path) -> dict:
    """Extract title, authors, abstract from main.tex."""
    main_tex = paper_dir / "main.tex"
    if not main_tex.exists():
        return {"title": "", "authors": "", "abstract": "", "journal": ""}

    text = main_tex.read_text(encoding="utf-8", errors="replace")

    # Title
    title = ""
    m = re.search(r"\\title\{(.+?)\}", text, re.DOTALL)
    if m:
        raw_title = m.group(1)
        # \texorpdfstring{latex}{plain} -> plain
        raw_title = re.sub(r"\\texorpdfstring\{[^}]*\}\{([^}]*)\}", r"\1", raw_title)
        # \cmd{arg} -> arg for common commands
        raw_title = re.sub(r"\\(?:mathrm|mathbb|mathcal|operatorname|text|textbf|emph)\{([^}]*)\}", r"\1", raw_title)
        # Remove remaining \commands
        raw_title = re.sub(r"\\[a-zA-Z]+\*?", "", raw_title)
        # Clean up braces, dollars, tildes
        raw_title = re.sub(r"[~${}]", "", raw_title)
        title = re.sub(r"\s+", " ", raw_title).strip()

    # Authors
    authors = ""
    m = re.search(r"\\author\{(.+?)\}", text, re.DOTALL)
    if m:
        raw = m.group(1)
        # Extract names, skip affiliations
        names = re.findall(r"([A-Z][a-z]+(?:\s+[A-Z][a-z]+)+)", raw)
        authors = ", ".join(names)

    # Abstract
    abstract = ""
    m = re.search(r"\\begin\{abstract\}(.+?)\\end\{abstract\}", text, re.DOTALL)
    if m:
        abstract = m.group(1).strip()
        # Light cleanup
        abstract = re.sub(r"\s+", " ", abstract)

    # Journal from PIPELINE.md or directory name
    journal = ""
    pipeline = paper_dir / "PIPELINE.md"
    if pipeline.exists():
        ptxt = pipeline.read_text(encoding="utf-8", errors="replace")
        jm = re.search(r"target.*?journal[:\s]*(.+)", ptxt, re.IGNORECASE)
        if jm:
            journal = jm.group(1).strip()

    # Fallback: last part of dir name (e.g. _jnt, _etds, _rint)
    if not journal:
        parts = paper_dir.name.split("_")
        journal = parts[-1].upper() if parts else ""

    return {
        "title": title,
        "authors": authors,
        "abstract": abstract,
        "journal": journal,
    }


def extract_theorem_inventory(paper_dir: Path) -> list[dict]:
    """Extract theorem labels and types from all .tex files."""
    claim_re = re.compile(
        r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}"
        r"(?:\[([^\]]*)\])?\s*"
        r"\\label\{([^}]+)\}",
        re.DOTALL,
    )
    results = []
    for tex in sorted(paper_dir.glob("**/*.tex")):
        text = tex.read_text(encoding="utf-8", errors="replace")
        for m in claim_re.finditer(text):
            results.append({
                "type": m.group(1),
                "title": m.group(2) or "",
                "label": m.group(3),
            })
    return results


def dir_to_repo_name(paper_dir: Path) -> str:
    """Convert directory name to a short GitHub repo name."""
    name = paper_dir.name
    # Remove prefix
    name = re.sub(r"^submitted_2026_", "", name)
    # Remove journal suffix (last segment if it's short like jnt, etds, rint)
    parts = name.split("_")
    if len(parts) > 2 and len(parts[-1]) <= 5:
        parts = parts[:-1]
    return "-".join(parts)


def generate_readme(meta: dict, theorems: list[dict], repo_name: str) -> str:
    """Generate README.md for the paper repo."""
    title = meta["title"] or repo_name.replace("-", " ").title()
    lines = [f"# {title}", ""]

    if meta["authors"]:
        lines.append(f"**Authors:** {meta['authors']}")
        lines.append("")

    if meta["journal"]:
        lines.append(f"**Submitted to:** {meta['journal']}")
        lines.append("")

    if meta["abstract"]:
        lines.append("## Abstract")
        lines.append("")
        # Truncate for README but keep reasonable length
        abstract = meta["abstract"][:2000]
        lines.append(abstract)
        lines.append("")

    if theorems:
        lines.append(f"## Theorem Inventory ({len(theorems)} results)")
        lines.append("")
        lines.append("| Type | Label |")
        lines.append("|------|-------|")
        for t in theorems:
            lines.append(f"| {t['type']} | `{t['label']}` |")
        lines.append("")

    lines.extend([
        "## Building",
        "",
        "```bash",
        "# Compile with pdflatex or xelatex",
        "pdflatex main.tex",
        "bibtex main",
        "pdflatex main.tex",
        "pdflatex main.tex",
        "```",
        "",
        "## Related",
        "",
        f"This paper is part of the [Omega Project](https://github.com/{ORG}/automath) "
        "-- a formalization and discovery engine for mathematics.",
        "",
        "## License",
        "",
        "MIT",
        "",
    ])
    return "\n".join(lines)


def gh(*args, capture=True) -> subprocess.CompletedProcess:
    """Run gh CLI command."""
    cmd = ["gh"] + list(args)
    return subprocess.run(cmd, capture_output=capture, text=True, timeout=60)


def create_repo(paper_dir: Path, dry_run: bool = False) -> bool:
    """Create a GitHub repo for a submitted paper."""
    repo_name = dir_to_repo_name(paper_dir)
    meta = extract_paper_metadata(paper_dir)
    theorems = extract_theorem_inventory(paper_dir)
    title = meta["title"] or repo_name.replace("-", " ").title()

    print(f"\n{'='*60}")
    print(f"Paper: {paper_dir.name}")
    print(f"Repo:  {ORG}/{repo_name}")
    print(f"Title: {title}")
    print(f"Theorems: {len(theorems)}")

    if dry_run:
        print("  [DRY RUN] Would create repo and push files")
        return True

    # Check if repo already exists
    check = gh("repo", "view", f"{ORG}/{repo_name}", "--json", "name")
    if check.returncode == 0:
        print(f"  SKIP: Repo {ORG}/{repo_name} already exists")
        return True

    # Create temp directory, copy files, add README, init git, push
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)

        # Copy paper files (exclude PIPELINE.md, SUBMITTED marker)
        skip = {"PIPELINE.md", "SUBMITTED", "__pycache__"}
        for item in paper_dir.iterdir():
            if item.name in skip or item.name.startswith("."):
                continue
            dest = tmp_path / item.name
            if item.is_dir():
                shutil.copytree(item, dest)
            else:
                shutil.copy2(item, dest)

        # Generate README
        readme = generate_readme(meta, theorems, repo_name)
        (tmp_path / "README.md").write_text(readme, encoding="utf-8")

        # .gitignore
        (tmp_path / ".gitignore").write_text(LATEX_GITIGNORE, encoding="utf-8")

        # LICENSE
        (tmp_path / "LICENSE").write_text(MIT_LICENSE, encoding="utf-8")

        # Init git repo
        subprocess.run(["git", "init"], cwd=tmp, capture_output=True)
        subprocess.run(["git", "add", "-A"], cwd=tmp, capture_output=True)
        subprocess.run(
            ["git", "commit", "-m", f"Initial submission: {title}"],
            cwd=tmp, capture_output=True,
        )

        # Create GitHub repo
        description = title[:200]
        result = gh(
            "repo", "create", f"{ORG}/{repo_name}",
            "--public",
            "--description", description,
            "--source", tmp,
            "--push",
        )

        if result.returncode != 0:
            print(f"  ERROR: {result.stderr.strip()}")
            return False

        print(f"  CREATED: https://github.com/{ORG}/{repo_name}")
        return True


def list_papers():
    """List all submitted papers and their proposed repo names."""
    papers = sorted(PUBLICATION_DIR.glob("submitted_2026_*/"))
    print(f"{'Directory':<65} {'Repo name':<40} {'Theorems':>8}")
    print("-" * 115)
    for d in papers:
        repo_name = dir_to_repo_name(d)
        theorems = extract_theorem_inventory(d)
        print(f"{d.name:<65} {repo_name:<40} {len(theorems):>8}")


def main():
    parser = argparse.ArgumentParser(description="Create standalone repos for submitted papers")
    parser.add_argument("--paper", help="Create repo for a specific paper directory")
    parser.add_argument("--all", action="store_true", help="Create repos for all submitted papers")
    parser.add_argument("--list", action="store_true", help="List papers and proposed repo names")
    parser.add_argument("--dry-run", action="store_true", help="Preview without creating")
    args = parser.parse_args()

    if args.list:
        list_papers()
        return

    if args.paper:
        paper_dir = Path(args.paper).resolve()
        if not paper_dir.exists():
            print(f"ERROR: {paper_dir} not found")
            sys.exit(1)
        ok = create_repo(paper_dir, args.dry_run)
        sys.exit(0 if ok else 1)

    if args.all:
        papers = sorted(PUBLICATION_DIR.glob("submitted_2026_*/"))
        print(f"Creating repos for {len(papers)} submitted papers...")
        results = []
        for d in papers:
            ok = create_repo(d, args.dry_run)
            results.append((d.name, ok))

        print(f"\n{'='*60}")
        print(f"Results: {sum(1 for _,ok in results if ok)}/{len(results)} succeeded")
        for name, ok in results:
            status = "OK" if ok else "FAIL"
            print(f"  [{status}] {name}")
        return

    parser.print_help()


if __name__ == "__main__":
    main()
