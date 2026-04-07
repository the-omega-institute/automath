#!/usr/bin/env python3
"""Upload NotebookLM videos to YouTube for paper promotion.

Requires:
  pip install google-api-python-client google-auth-oauthlib
  YouTube Data API v3 OAuth credentials (client_secrets.json)

Setup:
  1. Go to https://console.cloud.google.com/apis/credentials
  2. Create OAuth 2.0 Client ID (Desktop app)
  3. Download JSON -> save as client_secrets.json next to this script
  4. Enable YouTube Data API v3 in the console

Usage:
  python youtube_upload.py --video <path.mp4> --title "Paper Title" --description "..."
  python youtube_upload.py --all                    # Upload all videos from artifacts/
  python youtube_upload.py --list                   # List uploaded videos
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path

from google.auth.transport.requests import Request
from google.oauth2.credentials import Credentials
from google_auth_oauthlib.flow import InstalledAppFlow
from googleapiclient.discovery import build
from googleapiclient.http import MediaFileUpload

SCRIPT_DIR = Path(__file__).resolve().parent
PUBLICATION_DIR = SCRIPT_DIR.parent.parent / "papers" / "publication"
ARTIFACTS_DIR = PUBLICATION_DIR / "notebooklm" / "artifacts"
SECRETS_FILE = SCRIPT_DIR / "client_secrets.json"
TOKEN_FILE = SCRIPT_DIR / ".youtube_token.json"

SCOPES = ["https://www.googleapis.com/auth/youtube.upload",
          "https://www.googleapis.com/auth/youtube.readonly"]

CHANNEL_DESCRIPTION = (
    "The Omega Institute — Formalization and discovery engine for mathematics.\n"
    "https://github.com/the-omega-institute/automath"
)

# Map paper slugs to repo names for description links
REPO_MAP = {
    "branch_cubic_regular_s4": "branch-cubic-regular-s4-closure-prym-ray-class",
    "fibonacci_moduli_cross_resolution": "fibonacci-moduli-cross-resolution-arithmetic",
    "fibonacci_stabilization_sharp_threshold": "fibonacci-stabilization-sharp-threshold-conjugacy-nonlinearity",
    "folded_rotation_histogram_certificates": "folded-rotation-histogram-certificates",
    "folded_rotation_histogram": "folded-rotation-histogram",
    "grg_shell_geometry_from": "grg-shell-geometry-from-stationary-detector-thermality",
    "resolution_folding_core_symbolic": "resolution-folding-core-symbolic-dynamics",
    "zeckendorf_streaming_normalization_automata": "zeckendorf-streaming-normalization-automata-rairo",
    "zero_jitter_information_clocks": "zero-jitter-information-clocks-parry-gibbs-rigidity",
    "dynamical_zeta": "automath",
}


def get_youtube_service():
    """Authenticate and return YouTube API service."""
    creds = None
    if TOKEN_FILE.exists():
        creds = Credentials.from_authorized_user_file(str(TOKEN_FILE), SCOPES)

    if not creds or not creds.valid:
        if creds and creds.expired and creds.refresh_token:
            creds.refresh(Request())
        else:
            if not SECRETS_FILE.exists():
                print(f"ERROR: {SECRETS_FILE} not found.")
                print("Download OAuth credentials from Google Cloud Console.")
                print("See: https://console.cloud.google.com/apis/credentials")
                sys.exit(1)
            flow = InstalledAppFlow.from_client_secrets_file(str(SECRETS_FILE), SCOPES)
            creds = flow.run_local_server(port=0)

        TOKEN_FILE.write_text(creds.to_json())
        print("[yt] Credentials saved.")

    return build("youtube", "v3", credentials=creds)


def extract_paper_title(slug: str) -> str:
    """Try to extract paper title from the paper directory."""
    for prefix in ("submitted_2026_", "2026_"):
        for d in PUBLICATION_DIR.glob(f"{prefix}*"):
            dir_slug = d.name.replace(prefix, "")
            parts = dir_slug.split("_")
            if len(parts) > 3 and len(parts[-1]) <= 5:
                parts = parts[:-1]
            test_slug = "_".join(parts[:4])
            if test_slug == slug or slug in dir_slug:
                main_tex = d / "main.tex"
                if main_tex.exists():
                    text = main_tex.read_text(encoding="utf-8", errors="replace")
                    m = re.search(r"\\title\{(.+?)\}", text, re.DOTALL)
                    if m:
                        raw = m.group(1)
                        raw = re.sub(r"\\texorpdfstring\{[^}]*\}\{([^}]*)\}", r"\1", raw)
                        raw = re.sub(r"\\(?:mathrm|mathbb|mathcal|operatorname|text|textbf|emph)\{([^}]*)\}", r"\1", raw)
                        raw = re.sub(r"\\[a-zA-Z]+\*?", "", raw)
                        raw = re.sub(r"[~${}]", "", raw)
                        return re.sub(r"\s+", " ", raw).strip()
    return slug.replace("_", " ").title()


def make_description(slug: str, title: str) -> str:
    """Generate YouTube video description."""
    repo = REPO_MAP.get(slug, "automath")
    repo_url = f"https://github.com/the-omega-institute/{repo}"

    lines = [
        title,
        "",
        f"Paper repository: {repo_url}",
        f"Slide deck & audio: {repo_url}/releases",
        "",
        "Part of the Omega Project — a formalization and discovery engine for mathematics.",
        "https://github.com/the-omega-institute/automath",
        "",
        "Generated by NotebookLM (https://notebooklm.google.com)",
        "",
        "#mathematics #research #formalization #omega #notebooklm",
    ]
    return "\n".join(lines)


def make_tags(slug: str) -> list[str]:
    """Generate tags from slug."""
    base_tags = ["mathematics", "research", "theorem", "proof",
                 "formalization", "omega project", "notebooklm"]
    slug_tags = [w for w in slug.split("_") if len(w) > 2]
    return base_tags + slug_tags[:5]


def upload_video(youtube, video_path: Path, title: str, description: str,
                 tags: list[str], category: str = "27",
                 privacy: str = "public") -> dict:
    """Upload a video to YouTube. Category 27 = Education."""
    body = {
        "snippet": {
            "title": title[:100],
            "description": description[:5000],
            "tags": tags[:30],
            "categoryId": category,
            "defaultLanguage": "en",
        },
        "status": {
            "privacyStatus": privacy,
            "selfDeclaredMadeForKids": False,
        },
    }

    media = MediaFileUpload(
        str(video_path),
        mimetype="video/mp4",
        resumable=True,
        chunksize=10 * 1024 * 1024,  # 10MB chunks
    )

    request = youtube.videos().insert(
        part="snippet,status",
        body=body,
        media_body=media,
    )

    print(f"[yt] Uploading: {video_path.name} ({video_path.stat().st_size / 1024 / 1024:.1f} MB)")
    response = None
    while response is None:
        status, response = request.next_chunk()
        if status:
            pct = int(status.progress() * 100)
            print(f"[yt]   {pct}% uploaded")

    video_id = response["id"]
    url = f"https://www.youtube.com/watch?v={video_id}"
    print(f"[yt] UPLOADED: {url}")
    return {"video_id": video_id, "url": url, "title": title}


def find_videos() -> list[tuple[str, Path]]:
    """Find all video files in artifacts directories."""
    videos = []
    if not ARTIFACTS_DIR.exists():
        return videos
    for d in sorted(ARTIFACTS_DIR.iterdir()):
        if not d.is_dir():
            continue
        for f in d.glob("*.mp4"):
            videos.append((d.name, f))
    return videos


def main():
    parser = argparse.ArgumentParser(description="Upload NotebookLM videos to YouTube")
    parser.add_argument("--video", help="Path to a specific video file")
    parser.add_argument("--title", help="Video title (auto-detected if omitted)")
    parser.add_argument("--description", help="Video description")
    parser.add_argument("--all", action="store_true", help="Upload all videos from artifacts/")
    parser.add_argument("--list", action="store_true", help="List videos found in artifacts/")
    parser.add_argument("--privacy", default="public", choices=["public", "unlisted", "private"])
    parser.add_argument("--dry-run", action="store_true", help="Preview without uploading")
    args = parser.parse_args()

    if args.list:
        videos = find_videos()
        if not videos:
            print("No videos found in artifacts/")
            return
        print(f"Found {len(videos)} video(s):")
        for slug, path in videos:
            title = extract_paper_title(slug)
            print(f"  {slug}: {path.name} ({path.stat().st_size / 1024 / 1024:.1f} MB)")
            print(f"    Title: {title}")
        return

    if args.video:
        video_path = Path(args.video).resolve()
        if not video_path.exists():
            print(f"ERROR: {video_path} not found")
            sys.exit(1)
        slug = video_path.parent.name
        title = args.title or extract_paper_title(slug)
        description = args.description or make_description(slug, title)
        tags = make_tags(slug)

        if args.dry_run:
            print(f"[DRY RUN] Would upload: {video_path.name}")
            print(f"  Title: {title}")
            print(f"  Tags: {tags}")
            return

        youtube = get_youtube_service()
        upload_video(youtube, video_path, title, description, tags, privacy=args.privacy)
        return

    if args.all:
        videos = find_videos()
        if not videos:
            print("No videos found in artifacts/")
            return

        results = []
        youtube = None if args.dry_run else get_youtube_service()

        for slug, path in videos:
            title = extract_paper_title(slug)
            description = make_description(slug, title)
            tags = make_tags(slug)

            if args.dry_run:
                print(f"[DRY RUN] {slug}: {title}")
                results.append({"slug": slug, "title": title, "status": "dry_run"})
                continue

            try:
                result = upload_video(youtube, path, title, description, tags, privacy=args.privacy)
                results.append({**result, "slug": slug, "status": "ok"})
            except Exception as e:
                print(f"[yt] ERROR uploading {slug}: {e}")
                results.append({"slug": slug, "title": title, "status": "error", "error": str(e)})

        # Save manifest
        manifest_path = ARTIFACTS_DIR / "youtube_manifest.json"
        manifest_path.write_text(json.dumps(results, indent=2), encoding="utf-8")
        print(f"\n{'='*60}")
        ok = sum(1 for r in results if r["status"] == "ok")
        print(f"Results: {ok}/{len(results)} uploaded")
        for r in results:
            status = r.get("url", r["status"])
            print(f"  [{r['status']}] {r.get('slug', '?')}: {status}")
        return

    parser.print_help()


if __name__ == "__main__":
    main()
