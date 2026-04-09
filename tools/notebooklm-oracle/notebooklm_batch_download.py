#!/usr/bin/env python3
"""Batch download NotebookLM artifacts for all submitted papers.

Polls all notebooks until artifacts complete, then downloads to artifacts/<slug>/.

Usage:
    python notebooklm_batch_download.py              # Poll + download all
    python notebooklm_batch_download.py --status      # Status only
"""

import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

PUBLICATION_DIR = Path(__file__).resolve().parent.parent.parent / "papers" / "publication"
ARTIFACTS_DIR = PUBLICATION_DIR / "notebooklm" / "artifacts"
ARTIFACTS_DIR.mkdir(parents=True, exist_ok=True)

POLL_INTERVAL = 30
MAX_POLL_TIME = 900  # 15 min


def run_nlm(*args, timeout=120) -> str:
    env = os.environ.copy()
    env["PYTHONIOENCODING"] = "utf-8"
    try:
        result = subprocess.run(
            ["notebooklm"] + list(args),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=timeout, env=env,
        )
    except subprocess.TimeoutExpired:
        return ""
    return result.stdout.decode("utf-8", errors="replace").strip()


def list_notebooks() -> list[dict]:
    """Parse notebook list into structured data."""
    out = run_nlm("list")
    notebooks = []
    for m in re.finditer(r"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})", out):
        notebooks.append({"id": m.group(1)})
    return notebooks


def paper_slug_from_dir(name: str) -> str:
    name = re.sub(r"^submitted_2026_", "", name)
    name = re.sub(r"^2026_", "", name)
    parts = name.split("_")
    if len(parts) > 3 and len(parts[-1]) <= 5:
        parts = parts[:-1]
    return "_".join(parts[:4])


def check_artifacts(nb_id: str) -> dict:
    """Check artifact status for a notebook."""
    run_nlm("use", nb_id[:8])
    out = run_nlm("artifact", "list", timeout=30)
    completed = out.count("completed")
    in_progress = out.count("in_progress") + out.count("pending")
    failed = out.count("failed")
    has_audio = "Audio" in out
    has_slides = "Slide" in out
    return {
        "completed": completed,
        "in_progress": in_progress,
        "failed": failed,
        "has_audio": has_audio,
        "has_slides": has_slides,
        "raw": out,
    }


def download_for_notebook(nb_id: str, slug: str) -> list[Path]:
    """Download artifacts for a specific notebook."""
    run_nlm("use", nb_id[:8])
    out_dir = ARTIFACTS_DIR / slug
    out_dir.mkdir(parents=True, exist_ok=True)
    downloaded = []

    # Audio
    audio_path = out_dir / f"{slug}_podcast.wav"
    if not audio_path.exists():
        run_nlm("download", "audio", str(audio_path), timeout=120)
        if audio_path.exists() and audio_path.stat().st_size > 1000:
            print(f"  Audio: {audio_path.name} ({audio_path.stat().st_size / 1024 / 1024:.1f} MB)")
            downloaded.append(audio_path)

    # Slides
    slides_path = out_dir / f"{slug}_slides.pdf"
    if not slides_path.exists():
        run_nlm("download", "slide-deck", str(slides_path), timeout=120)
        if slides_path.exists() and slides_path.stat().st_size > 1000:
            print(f"  Slides: {slides_path.name} ({slides_path.stat().st_size / 1024:.0f} KB)")
            downloaded.append(slides_path)

    return downloaded


def main():
    status_only = "--status" in sys.argv

    # Map notebooks to paper slugs by listing paper dirs + notebooks
    papers = sorted(PUBLICATION_DIR.glob("submitted_2026_*/"))
    notebooks = run_nlm("list")

    # Build notebook -> slug mapping from notebook titles
    nb_map = {}  # nb_id -> slug
    for paper_dir in papers:
        slug = paper_slug_from_dir(paper_dir.name)
        # Match by title keywords in notebook list
        keywords = paper_dir.name.replace("submitted_2026_", "").split("_")[:3]
        for m in re.finditer(r"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})", notebooks):
            nb_id = m.group(1)
            if nb_id not in nb_map:
                # Simple heuristic: check surrounding text
                start = max(0, m.start() - 200)
                context = notebooks[start:m.end() + 200].lower()
                if any(kw.lower() in context for kw in keywords[:2]):
                    nb_map[nb_id] = slug

    if not nb_map:
        print("No notebooks found matching submitted papers.")
        print("Raw notebook list:")
        print(notebooks)
        return

    print(f"Found {len(nb_map)} notebooks for {len(papers)} papers\n")

    if status_only:
        for nb_id, slug in sorted(nb_map.items(), key=lambda x: x[1]):
            status = check_artifacts(nb_id)
            c, ip, f = status["completed"], status["in_progress"], status["failed"]
            print(f"  {slug:<50} {nb_id[:8]}  {c}ok {ip}wip {f}fail")
        return

    # Poll loop
    start = time.time()
    while time.time() - start < MAX_POLL_TIME:
        all_done = True
        for nb_id, slug in sorted(nb_map.items(), key=lambda x: x[1]):
            status = check_artifacts(nb_id)
            if status["in_progress"] > 0:
                all_done = False

        elapsed = int(time.time() - start)
        total_ip = sum(check_artifacts(nb)["in_progress"] for nb in nb_map)
        if all_done or total_ip == 0:
            print(f"\nAll artifacts ready after {elapsed}s. Downloading...")
            break

        print(f"[{elapsed}s] {total_ip} artifacts still generating... waiting {POLL_INTERVAL}s")
        time.sleep(POLL_INTERVAL)

    # Download all
    total_downloaded = 0
    for nb_id, slug in sorted(nb_map.items(), key=lambda x: x[1]):
        print(f"\n{slug}:")
        files = download_for_notebook(nb_id, slug)
        total_downloaded += len(files)
        if not files:
            # Check what's there
            out_dir = ARTIFACTS_DIR / slug
            existing = list(out_dir.glob("*")) if out_dir.exists() else []
            if existing:
                print(f"  Already downloaded: {[f.name for f in existing]}")
            else:
                print(f"  No artifacts available")

    print(f"\nTotal: {total_downloaded} new artifacts downloaded to {ARTIFACTS_DIR}")


if __name__ == "__main__":
    main()
