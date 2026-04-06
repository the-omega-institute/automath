#!/usr/bin/env python3
"""NotebookLM Dispatch v2.0 — Generate slide decks & audio podcasts for paper promotion.

Uses notebooklm-py RPC API. Requires: pip install notebooklm-py && notebooklm login

Workflow per paper:
  1. Create notebook + upload PDF
  2. Generate slide deck + audio podcast (parallel)
  3. Poll until artifacts complete
  4. Download artifacts to output directory

Usage:
    python notebooklm_dispatch.py --paper <dir>                    # Both slides + audio
    python notebooklm_dispatch.py --paper <dir> --type audio       # Audio only
    python notebooklm_dispatch.py --paper <dir> --type slides      # Slides only
    python notebooklm_dispatch.py --all                            # All submitted papers
    python notebooklm_dispatch.py --notebook <id> --status         # Check artifact status
    python notebooklm_dispatch.py --notebook <id> --download       # Download completed artifacts
    python notebooklm_dispatch.py --list                           # List notebooks
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

PUBLICATION_DIR = Path(__file__).resolve().parent.parent.parent / "papers" / "publication"
OUTPUT_DIR = PUBLICATION_DIR / "notebooklm" / "artifacts"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

POLL_INTERVAL = 15  # seconds between status checks
MAX_POLL_TIME = 600  # 10 minutes max wait


def find_pdf(paper_dir: Path) -> Path | None:
    """Find main.pdf or largest PDF in paper directory."""
    for c in paper_dir.glob("*.pdf"):
        if c.stem == "main":
            return c
    candidates = list(paper_dir.glob("**/*.pdf"))
    if candidates:
        candidates.sort(key=lambda f: f.stat().st_size, reverse=True)
        return candidates[0]
    return None


def paper_slug(paper_dir: Path) -> str:
    """Short slug from paper directory name."""
    name = paper_dir.name
    name = re.sub(r"^submitted_2026_", "", name)
    name = re.sub(r"^2026_", "", name)
    parts = name.split("_")
    if len(parts) > 3 and len(parts[-1]) <= 5:
        parts = parts[:-1]
    return "_".join(parts[:4])


def run_nlm(*args, timeout=120) -> str:
    """Run notebooklm CLI command, handle Windows encoding."""
    env = os.environ.copy()
    env["PYTHONIOENCODING"] = "utf-8"
    try:
        result = subprocess.run(
            ["notebooklm"] + list(args),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=timeout, env=env,
        )
    except subprocess.TimeoutExpired:
        print(f"[nlm] TIMEOUT: notebooklm {' '.join(str(a) for a in args)}")
        return ""
    stdout = result.stdout.decode("utf-8", errors="replace").strip()
    stderr = result.stderr.decode("utf-8", errors="replace").strip()
    if result.returncode != 0 and stderr:
        if "UnicodeEncodeError" not in stderr:
            print(f"[nlm] WARN: {stderr[:300]}")
    return stdout


def extract_uuid(text: str) -> str | None:
    """Extract first UUID from text."""
    m = re.search(r"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})", text)
    return m.group(1) if m else None


def setup_notebook(paper_dir: Path, pdf_path: Path, notebook_id: str | None = None) -> str | None:
    """Create notebook and upload PDF. Returns notebook ID or None on failure."""
    if notebook_id:
        print(f"[nlm] Reusing notebook: {notebook_id[:12]}...")
        run_nlm("use", notebook_id[:8])
        return notebook_id

    title = paper_dir.name.replace("submitted_2026_", "").replace("2026_", "").replace("_", " ").title()[:60]
    print(f"[nlm] Creating notebook: {title}")
    out = run_nlm("create", title)
    nb_id = extract_uuid(out)
    if not nb_id:
        print(f"[nlm] ERROR creating notebook: {out}")
        return None

    print(f"[nlm] Notebook: {nb_id[:12]}...")
    run_nlm("use", nb_id[:8])

    # Upload PDF
    print(f"[nlm] Uploading: {pdf_path.name} ({pdf_path.stat().st_size / 1024:.0f} KB)")
    out = run_nlm("source", "add", str(pdf_path), timeout=180)
    if "Added source" not in out and "added" not in out.lower():
        print(f"[nlm] ERROR uploading PDF: {out}")
        return None
    print(f"[nlm] Upload OK")
    return nb_id


def generate_artifacts(types: list[str], slug: str) -> dict:
    """Request artifact generation. Returns {type: generation_output}."""
    results = {}
    for t in types:
        if t == "audio":
            print("[nlm] Requesting audio podcast generation...")
            out = run_nlm("generate", "audio",
                          "A deep dive podcast discussing this paper's key results, "
                          "proof techniques, and significance for the field.",
                          timeout=60)
            results["audio"] = out
            print(f"[nlm] Audio generation queued")
        elif t == "slides":
            print("[nlm] Requesting slide deck generation...")
            out = run_nlm("generate", "slide-deck",
                          "A clear presentation covering: motivation, main theorems, "
                          "proof sketch, applications, and open questions.",
                          timeout=60)
            results["slides"] = out
            print(f"[nlm] Slide deck generation queued")
    return results


def poll_artifacts(timeout: int = MAX_POLL_TIME) -> dict:
    """Poll artifact status until all complete or timeout. Returns final status dict."""
    start = time.time()
    while time.time() - start < timeout:
        out = run_nlm("artifact", "list", timeout=30)
        # Parse status from table output
        in_progress = out.count("in_progress") + out.count("pending")
        completed = out.count("completed")
        failed = out.count("failed")

        elapsed = int(time.time() - start)
        print(f"[nlm] [{elapsed}s] Artifacts: {completed} completed, {in_progress} in progress, {failed} failed")

        if in_progress == 0:
            return {"completed": completed, "failed": failed, "output": out}

        time.sleep(POLL_INTERVAL)

    print(f"[nlm] TIMEOUT after {timeout}s — some artifacts still generating")
    return {"completed": 0, "failed": 0, "output": out, "timeout": True}


def download_artifacts(slug: str, output_dir: Path) -> list[Path]:
    """Download all completed artifacts. Returns list of downloaded file paths."""
    downloaded = []
    output_dir.mkdir(parents=True, exist_ok=True)

    # Try audio download
    audio_path = output_dir / f"{slug}_podcast.wav"
    out = run_nlm("download", "audio", str(audio_path), timeout=120)
    if audio_path.exists() and audio_path.stat().st_size > 1000:
        print(f"[nlm] Downloaded audio: {audio_path.name} ({audio_path.stat().st_size / 1024 / 1024:.1f} MB)")
        downloaded.append(audio_path)

    # Try slide deck download
    slides_path = output_dir / f"{slug}_slides.pdf"
    out = run_nlm("download", "slide-deck", str(slides_path), timeout=120)
    if slides_path.exists() and slides_path.stat().st_size > 1000:
        print(f"[nlm] Downloaded slides: {slides_path.name} ({slides_path.stat().st_size / 1024:.0f} KB)")
        downloaded.append(slides_path)

    return downloaded


def save_manifest(slug: str, paper_dir: Path, nb_id: str, artifacts: list[Path], output_dir: Path):
    """Save a manifest JSON for downstream tools (create_paper_repos.py)."""
    manifest = {
        "timestamp": datetime.now().isoformat(),
        "paper_dir": str(paper_dir),
        "paper_slug": slug,
        "notebook_id": nb_id,
        "artifacts": [
            {"path": str(p), "name": p.name, "size": p.stat().st_size, "type": p.suffix}
            for p in artifacts
        ],
    }
    manifest_path = output_dir / f"{slug}_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    print(f"[nlm] Manifest: {manifest_path}")


def process_paper(paper_dir: Path, types: list[str], notebook_id: str | None = None,
                  no_wait: bool = False, keep: bool = False) -> bool:
    """Full pipeline for one paper: upload -> generate -> poll -> download."""
    pdf_path = find_pdf(paper_dir)
    if not pdf_path:
        print(f"[nlm] ERROR: No PDF in {paper_dir}")
        return False

    slug = paper_slug(paper_dir)
    print(f"\n{'='*60}")
    print(f"[nlm] Paper: {paper_dir.name}")
    print(f"[nlm] PDF: {pdf_path.name} ({pdf_path.stat().st_size / 1024:.0f} KB)")
    print(f"[nlm] Types: {', '.join(types)}")

    # Step 1: Setup notebook + upload
    nb_id = setup_notebook(paper_dir, pdf_path, notebook_id)
    if not nb_id:
        return False

    # Step 2: Generate artifacts
    generate_artifacts(types, slug)

    if no_wait:
        print(f"[nlm] No-wait mode. Notebook: {nb_id[:8]}")
        print(f"[nlm] Check later: python notebooklm_dispatch.py --notebook {nb_id[:8]} --status")
        return True

    # Step 3: Poll until done
    print(f"[nlm] Waiting for artifacts (polling every {POLL_INTERVAL}s, max {MAX_POLL_TIME}s)...")
    status = poll_artifacts()

    # Step 4: Download
    out_dir = OUTPUT_DIR / slug
    artifacts = download_artifacts(slug, out_dir)

    if artifacts:
        save_manifest(slug, paper_dir, nb_id, artifacts, out_dir)
        print(f"[nlm] SUCCESS: {len(artifacts)} artifact(s) downloaded to {out_dir}")
    else:
        print(f"[nlm] WARNING: No artifacts downloaded")

    if not keep and not notebook_id:
        print(f"[nlm] Notebook {nb_id[:8]} preserved. Delete manually or reuse with --notebook {nb_id[:8]}")

    return len(artifacts) > 0


def main():
    parser = argparse.ArgumentParser(description="NotebookLM Dispatch v2.0 — Slide deck & audio podcast generation")
    parser.add_argument("--paper", help="Paper directory path")
    parser.add_argument("--all", action="store_true", help="Process all submitted_2026_* papers")
    parser.add_argument("--type", default="both", choices=["audio", "slides", "both"],
                        help="What to generate (default: both)")
    parser.add_argument("--notebook", help="Reuse existing notebook ID (prefix ok)")
    parser.add_argument("--status", action="store_true", help="Check artifact status for --notebook")
    parser.add_argument("--download", action="store_true", help="Download artifacts for --notebook")
    parser.add_argument("--list", action="store_true", help="List all notebooks")
    parser.add_argument("--no-wait", action="store_true", help="Queue generation without waiting")
    parser.add_argument("--keep", action="store_true", help="Keep notebook after completion")
    args = parser.parse_args()

    # Resolve types
    if args.type == "both":
        types = ["slides", "audio"]
    else:
        types = [args.type]

    if args.list:
        print(run_nlm("list"))
        return

    if args.status:
        if args.notebook:
            run_nlm("use", args.notebook[:8])
        out = run_nlm("artifact", "list", timeout=30)
        print(out)
        return

    if args.download:
        slug = args.notebook or "manual"
        out_dir = OUTPUT_DIR / slug
        artifacts = download_artifacts(slug, out_dir)
        if artifacts:
            print(f"Downloaded {len(artifacts)} artifact(s)")
        else:
            print("No artifacts to download")
        return

    if args.paper:
        paper_dir = Path(args.paper).resolve()
        if not paper_dir.exists():
            print(f"[nlm] ERROR: {paper_dir} not found")
            sys.exit(1)
        ok = process_paper(paper_dir, types, args.notebook, args.no_wait, args.keep)
        sys.exit(0 if ok else 1)

    if args.all:
        papers = sorted(PUBLICATION_DIR.glob("submitted_2026_*/"))
        print(f"[nlm] Processing {len(papers)} submitted papers...")
        results = []
        for d in papers:
            if not find_pdf(d):
                print(f"[nlm] SKIP (no PDF): {d.name}")
                continue
            ok = process_paper(d, types, no_wait=args.no_wait)
            results.append((d.name, ok))

        print(f"\n{'='*60}")
        print(f"Results: {sum(1 for _,ok in results if ok)}/{len(results)} succeeded")
        for name, ok in results:
            print(f"  [{'OK' if ok else 'FAIL'}] {name}")
        return

    parser.print_help()


if __name__ == "__main__":
    main()
