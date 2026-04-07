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
import time
from pathlib import Path

PUBLICATION_DIR = Path(__file__).resolve().parent
ORG = "the-omega-institute"

ARTIFACTS_DIR = PUBLICATION_DIR / "notebooklm" / "artifacts"

LATEX_GITIGNORE = """\
*.aux
*.bbl
*.bcf
*.blg
*.fdb_latexmk
*.fls
*.log
*.out
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


def find_nlm_artifacts(paper_dir: Path) -> list[Path]:
    """Find NotebookLM artifacts (slides, audio) for a paper."""
    slug = paper_dir.name
    slug = re.sub(r"^submitted_2026_", "", slug)
    slug = re.sub(r"^2026_", "", slug)
    parts = slug.split("_")
    if len(parts) > 3 and len(parts[-1]) <= 5:
        parts = parts[:-1]
    slug = "_".join(parts[:4])

    artifacts = []
    # Exact match first
    artifact_dir = ARTIFACTS_DIR / slug
    if artifact_dir.exists():
        for f in sorted(artifact_dir.iterdir()):
            if f.suffix in (".pdf", ".wav", ".mp3", ".pptx"):
                artifacts.append(f)

    if artifacts:
        return artifacts

    # Fuzzy match: require first 3 keywords ALL present in dir name
    match_keys = parts[:3]
    for d in ARTIFACTS_DIR.glob("*"):
        if not d.is_dir():
            continue
        if all(k in d.name for k in match_keys):
            for f in sorted(d.iterdir()):
                if f.suffix in (".pdf", ".wav", ".mp3", ".pptx") and f not in artifacts:
                    artifacts.append(f)
    return artifacts


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


def generate_readme(meta: dict, theorems: list[dict], repo_name: str,
                     media_files: list[str] | None = None,
                     release_files: list[str] | None = None,
                     youtube_url: str | None = None) -> str:
    """Generate README.md for the paper repo."""
    title = meta["title"] or repo_name.replace("-", " ").title()

    # Header with badges
    lines = [f"# {title}", ""]
    badges = [
        f"![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)",
        f"![LaTeX](https://img.shields.io/badge/Built%20with-LaTeX-008080.svg)",
    ]
    if theorems:
        badges.append(f"![Theorems](https://img.shields.io/badge/Theorems-{len(theorems)}-blue.svg)")
    if youtube_url:
        badges.append(f"[![YouTube](https://img.shields.io/badge/YouTube-Video-red.svg)]({youtube_url})")
    lines.append(" ".join(badges))
    lines.append("")

    if meta["authors"]:
        lines.append(f"> **Authors:** {meta['authors']}")
        lines.append(">")
    if meta["journal"]:
        lines.append(f"> **Submitted to:** {meta['journal']}")
    if meta["authors"] or meta["journal"]:
        lines.append("")

    # Video embed (YouTube thumbnail)
    if youtube_url:
        # Extract video ID for thumbnail
        vid_id = ""
        if "watch?v=" in youtube_url:
            vid_id = youtube_url.split("watch?v=")[-1].split("&")[0]
        elif "youtu.be/" in youtube_url:
            vid_id = youtube_url.split("youtu.be/")[-1].split("?")[0]

        lines.append("## Video Presentation")
        lines.append("")
        if vid_id:
            lines.append(f"[![Watch on YouTube](https://img.youtube.com/vi/{vid_id}/maxresdefault.jpg)]({youtube_url})")
        else:
            lines.append(f"[Watch on YouTube]({youtube_url})")
        lines.append("")

    # Media section (slides, audio)
    release_names = set(release_files or [])
    all_media = media_files or []
    has_media = all_media or youtube_url
    if all_media:
        lines.append("## Resources")
        lines.append("")
        lines.append("| Type | Link |")
        lines.append("|------|------|")
        if youtube_url:
            lines.append(f"| Video Presentation | [YouTube]({youtube_url}) |")
        for mf in all_media:
            if mf in release_names:
                rel_url = f"https://github.com/{ORG}/{repo_name}/releases/download/media-v1/{mf}"
                if mf.endswith((".wav", ".mp3")):
                    lines.append(f"| Audio Podcast | [Download]({rel_url}) |")
                elif mf.endswith(".pdf"):
                    lines.append(f"| Slide Deck (PDF) | [Download]({rel_url}) |")
            else:
                if mf.endswith(".pdf"):
                    lines.append(f"| Slide Deck (PDF) | [View](media/{mf}) |")
                elif mf.endswith((".wav", ".mp3")):
                    lines.append(f"| Audio Podcast | [Download](media/{mf}) |")
        lines.append("")
        lines.append("*Generated by [NotebookLM](https://notebooklm.google.com)*")
        lines.append("")

    if meta["abstract"]:
        lines.append("## Abstract")
        lines.append("")
        abstract = meta["abstract"][:2000]
        lines.append(abstract)
        lines.append("")

    if theorems:
        lines.append(f"## Theorem Inventory ({len(theorems)} results)")
        lines.append("")
        lines.append("<details>")
        lines.append(f"<summary>Click to expand ({len(theorems)} theorems/lemmas/definitions)</summary>")
        lines.append("")
        lines.append("| Type | Label |")
        lines.append("|------|-------|")
        for t in theorems:
            lines.append(f"| {t['type']} | `{t['label']}` |")
        lines.append("")
        lines.append("</details>")
        lines.append("")

    lines.extend([
        "## Building",
        "",
        "```bash",
        "pdflatex main.tex && bibtex main && pdflatex main.tex && pdflatex main.tex",
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

        # Copy NotebookLM media artifacts if available
        # Skip large files (>25MB) from git — upload as GitHub Release later
        nlm_artifacts = find_nlm_artifacts(paper_dir)
        media_names = []
        release_files = []  # Large files for GitHub Release
        if nlm_artifacts:
            media_dir = tmp_path / "media"
            media_dir.mkdir(exist_ok=True)
            for artifact in nlm_artifacts:
                size_mb = artifact.stat().st_size / 1024 / 1024
                if size_mb > 25:
                    release_files.append(artifact)
                    media_names.append(artifact.name)
                    print(f"  Media (release): {artifact.name} ({size_mb:.1f} MB)")
                else:
                    shutil.copy2(artifact, media_dir / artifact.name)
                    media_names.append(artifact.name)
                    print(f"  Media: {artifact.name} ({size_mb:.1f} MB)")

        # Generate README
        release_names = [rf.name for rf in release_files] if release_files else None
        readme = generate_readme(meta, theorems, repo_name,
                                 media_names if media_names else None,
                                 release_names)
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

        # Create GitHub repo (create first, then push separately)
        description = title[:200]
        result = gh(
            "repo", "create", f"{ORG}/{repo_name}",
            "--public",
            "--description", description,
        )

        if result.returncode != 0:
            print(f"  ERROR creating repo: {result.stderr.strip()}")
            return False

        # Wait for GitHub to propagate the repo
        time.sleep(5)

        # Push to the new repo
        subprocess.run(
            ["git", "remote", "add", "origin",
             f"https://github.com/{ORG}/{repo_name}.git"],
            cwd=tmp, capture_output=True,
        )
        subprocess.run(
            ["git", "branch", "-M", "main"],
            cwd=tmp, capture_output=True,
        )

        # Retry push up to 3 times
        for attempt in range(3):
            push = subprocess.run(
                ["git", "push", "-u", "origin", "main"],
                cwd=tmp, capture_output=True, text=True, timeout=120,
            )
            if push.returncode == 0:
                break
            if attempt < 2:
                print(f"  Push attempt {attempt + 1} failed, retrying...")
                time.sleep(5)

        if push.returncode != 0:
            print(f"  ERROR pushing: {push.stderr.strip()[:300]}")
            return False

        print(f"  CREATED: https://github.com/{ORG}/{repo_name}")

        # Upload large media files as GitHub Release
        if release_files:
            print(f"  Creating release with {len(release_files)} media file(s)...")
            release_args = ["release", "create", "media-v1",
                            "--repo", f"{ORG}/{repo_name}",
                            "--title", "Media Assets (Slides & Audio)",
                            "--notes", "NotebookLM-generated presentation slides and audio podcast."]
            for rf in release_files:
                release_args.append(str(rf))
            rel_result = gh(*release_args)
            if rel_result.returncode == 0:
                print(f"  Release created with {len(release_files)} asset(s)")
            else:
                print(f"  Release WARN: {rel_result.stderr.strip()[:200]}")

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
