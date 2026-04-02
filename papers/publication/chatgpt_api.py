#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ChatGPT Pro direct API integration — fully automated, no browser needed.

Uses ChatGPT's internal backend API with an access token extracted from
the user's existing browser session. Supports file upload (PDF) and
streaming responses.

Setup (one-time per session):
    1. Open Chrome, go to https://chatgpt.com
    2. Open DevTools (F12) -> Console
    3. Run: copy(document.cookie.match(/(?:^|;\\s*)__Secure-next-auth.session-token=([^;]+)/)?.[1] || 'not found')
    4. Or simpler: visit https://chatgpt.com/api/auth/session and copy the accessToken value
    5. Save token: python chatgpt_api.py --setup

Usage:
    # Review a paper (PDF upload + prompt):
    python chatgpt_api.py --pdf paper.pdf --prompt "Review this paper as a JST referee."

    # Text-only query:
    python chatgpt_api.py --prompt "Prove that every continuous additive function is linear."

    # Batch mode for pipeline:
    python chatgpt_api.py --pdf paper.pdf --prompt-file prompts/editorial_review.md --output result.md

    # With specific model:
    python chatgpt_api.py --pdf paper.pdf --prompt "..." --model o3-mini-high
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
import uuid
from pathlib import Path
from datetime import datetime

try:
    import httpx
except ImportError:
    import subprocess
    subprocess.check_call([sys.executable, "-m", "pip", "install", "httpx"])
    import httpx

TOKEN_FILE = Path(__file__).parent / ".chatgpt_token"
BASE_URL = "https://chatgpt.com"
BACKEND = f"{BASE_URL}/backend-api"
DEFAULT_MODEL = "o3-mini-high"

# Model mapping: friendly name -> ChatGPT internal model slug
MODEL_MAP = {
    "o3-mini-high": "o3-mini-high",
    "o3-mini": "o3-mini",
    "o3": "o3",
    "o1": "o1",
    "gpt-4o": "gpt-4o",
    "gpt-4": "gpt-4",
}


def get_token() -> str:
    """Read stored access token."""
    if not TOKEN_FILE.exists():
        print("[chatgpt] No token found. Run: python chatgpt_api.py --setup", file=sys.stderr)
        sys.exit(1)
    data = json.loads(TOKEN_FILE.read_text(encoding="utf-8"))
    return data["access_token"]


def save_token(token: str):
    """Save access token to local file."""
    TOKEN_FILE.write_text(json.dumps({
        "access_token": token,
        "saved_at": datetime.now().isoformat(),
    }), encoding="utf-8")
    print(f"[chatgpt] Token saved to {TOKEN_FILE}")


def refresh_token(session_token: str) -> str:
    """Get access token from session token."""
    client = httpx.Client(timeout=30)
    resp = client.get(
        f"{BASE_URL}/api/auth/session",
        cookies={"__Secure-next-auth.session-token": session_token},
        headers={"User-Agent": "Mozilla/5.0"},
    )
    resp.raise_for_status()
    data = resp.json()
    if "accessToken" in data:
        return data["accessToken"]
    raise ValueError(f"No accessToken in response: {list(data.keys())}")


def make_headers(token: str) -> dict:
    """Build request headers."""
    return {
        "Authorization": f"Bearer {token}",
        "Content-Type": "application/json",
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
        "Accept": "text/event-stream",
    }


def upload_file(token: str, file_path: Path) -> dict:
    """Upload a file to ChatGPT and return the file metadata."""
    headers = {
        "Authorization": f"Bearer {token}",
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
    }

    file_size = file_path.stat().st_size
    file_name = file_path.name
    mime = "application/pdf" if file_name.endswith(".pdf") else "application/octet-stream"

    # Step 1: Create upload
    resp = httpx.post(
        f"{BACKEND}/files",
        headers={**headers, "Content-Type": "application/json"},
        json={
            "file_name": file_name,
            "file_size": file_size,
            "use_case": "ace_upload",
        },
        timeout=30,
    )
    resp.raise_for_status()
    upload_info = resp.json()
    file_id = upload_info["file_id"]
    upload_url = upload_info["upload_url"]

    print(f"[chatgpt] Uploading {file_name} ({file_size // 1024} KB)...")

    # Step 2: Upload file content
    with open(file_path, "rb") as f:
        put_resp = httpx.put(
            upload_url,
            content=f.read(),
            headers={
                "Content-Type": mime,
                "x-ms-blob-type": "BlockBlob",
            },
            timeout=120,
        )
        put_resp.raise_for_status()

    # Step 3: Mark upload complete
    complete_resp = httpx.post(
        f"{BACKEND}/files/{file_id}/uploaded",
        headers={**headers, "Content-Type": "application/json"},
        json={},
        timeout=30,
    )
    complete_resp.raise_for_status()

    print(f"[chatgpt] File uploaded: {file_id}")
    return {
        "file_id": file_id,
        "file_name": file_name,
        "size": file_size,
        "mime": mime,
    }


def send_message(token: str, prompt: str, model: str = DEFAULT_MODEL,
                 file_info: dict | None = None,
                 conversation_id: str | None = None) -> str:
    """Send a message to ChatGPT and return the full response text.

    Streams the server-sent events and assembles the final response.
    """
    headers = make_headers(token)
    msg_id = str(uuid.uuid4())
    parent_id = str(uuid.uuid4())

    # Build message content
    content_parts = []
    if file_info:
        content_parts.append({
            "asset_pointer": f"file-service://{file_info['file_id']}",
            "content_type": "image_asset_pointer" if file_info["mime"].startswith("image") else "file",
            "size_bytes": file_info["size"],
        })
    content_parts.append({"content_type": "text", "parts": [prompt]})

    # Build request body
    body = {
        "action": "next",
        "messages": [{
            "id": msg_id,
            "author": {"role": "user"},
            "content": {
                "content_type": "multimodal_text" if file_info else "text",
                "parts": [prompt] if not file_info else content_parts,
            },
            "metadata": {},
        }],
        "parent_message_id": parent_id,
        "model": MODEL_MAP.get(model, model),
        "timezone_offset_min": -480,
        "history_and_training_disabled": False,
        "conversation_mode": {"kind": "primary_assistant"},
        "force_paragen": False,
        "force_rate_limit": False,
    }

    if conversation_id:
        body["conversation_id"] = conversation_id

    if file_info:
        body["messages"][0]["content"] = {
            "content_type": "multimodal_text",
            "parts": [
                {
                    "asset_pointer": f"file-service://{file_info['file_id']}",
                    "content_type": "file",
                    "size_bytes": file_info["size"],
                },
                prompt,
            ],
        }
        body["messages"][0]["metadata"] = {
            "attachments": [{
                "id": file_info["file_id"],
                "name": file_info["file_name"],
                "size": file_info["size"],
                "mimeType": file_info["mime"],
            }],
        }

    print(f"[chatgpt] Sending prompt ({len(prompt)} chars, model={model})...")
    if file_info:
        print(f"[chatgpt] With attachment: {file_info['file_name']}")

    # Stream response
    response_text = ""
    start_time = time.time()

    with httpx.Client(timeout=httpx.Timeout(600.0, connect=30.0)) as client:
        with client.stream(
            "POST",
            f"{BACKEND}/conversation",
            headers=headers,
            json=body,
        ) as resp:
            if resp.status_code == 401:
                print("[chatgpt] ERROR: Token expired. Run: python chatgpt_api.py --setup", file=sys.stderr)
                sys.exit(1)
            if resp.status_code == 403:
                print("[chatgpt] ERROR: Forbidden (403). Token may be invalid or rate-limited.", file=sys.stderr)
                sys.exit(1)
            resp.raise_for_status()

            for line in resp.iter_lines():
                if not line.startswith("data: "):
                    continue
                data_str = line[6:]
                if data_str == "[DONE]":
                    break

                try:
                    data = json.loads(data_str)
                except json.JSONDecodeError:
                    continue

                msg = data.get("message", {})
                if msg.get("author", {}).get("role") == "assistant":
                    parts = msg.get("content", {}).get("parts", [])
                    if parts and isinstance(parts[0], str):
                        response_text = parts[0]

                # Progress indicator
                elapsed = int(time.time() - start_time)
                if elapsed > 0 and elapsed % 30 == 0 and len(response_text) > 0:
                    print(f"[chatgpt] Receiving... ({len(response_text)} chars, {elapsed}s)")

    elapsed = int(time.time() - start_time)
    print(f"[chatgpt] Response received: {len(response_text)} chars in {elapsed}s")
    return response_text


def setup_interactive():
    """Interactive setup to save access token."""
    print("=" * 60)
    print("  ChatGPT Pro API Setup")
    print("=" * 60)
    print()
    print("  Option A (recommended):")
    print("  1. Open Chrome, go to https://chatgpt.com")
    print("  2. Open DevTools (F12) -> Network tab")
    print("  3. Refresh the page")
    print("  4. Find any request to chatgpt.com")
    print("  5. Look for Authorization header: Bearer <token>")
    print("  6. Copy the <token> part")
    print()
    print("  Option B:")
    print("  1. Open Chrome, go to https://chatgpt.com/api/auth/session")
    print("  2. Copy the accessToken value from the JSON")
    print()

    token = input("  Paste your access token: ").strip()
    if not token:
        print("  No token provided.", file=sys.stderr)
        sys.exit(1)

    # Verify token
    print("  Verifying token...")
    headers = make_headers(token)
    try:
        resp = httpx.get(
            f"{BACKEND}/models",
            headers=headers,
            timeout=15,
        )
        if resp.status_code == 200:
            models = resp.json().get("models", [])
            model_names = [m.get("slug", "?") for m in models]
            print(f"  Token valid! Available models: {', '.join(model_names[:5])}")
            save_token(token)
            print("\n  Setup complete. You can now use the API.")
        elif resp.status_code == 401:
            print("  Token invalid or expired.", file=sys.stderr)
            sys.exit(1)
        else:
            print(f"  Unexpected status: {resp.status_code}. Saving anyway.", file=sys.stderr)
            save_token(token)
    except Exception as e:
        print(f"  Verification failed: {e}. Saving anyway.", file=sys.stderr)
        save_token(token)


def main():
    parser = argparse.ArgumentParser(
        description="ChatGPT Pro direct API (fully automated)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python chatgpt_api.py --setup
  python chatgpt_api.py --prompt "Prove X" --output result.md
  python chatgpt_api.py --pdf paper.pdf --prompt "Review this" --output result.md
  python chatgpt_api.py --pdf paper.pdf --prompt-file prompts/review.md --output result.md
""",
    )
    parser.add_argument("--setup", action="store_true",
                        help="Interactive setup: save access token")
    parser.add_argument("--pdf", type=Path,
                        help="PDF file to upload")
    parser.add_argument("--prompt", type=str,
                        help="Prompt text")
    parser.add_argument("--prompt-file", type=Path,
                        help="Read prompt from file")
    parser.add_argument("--output", type=Path,
                        help="Save response to file (with metadata)")
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL,
                        help=f"Model to use (default: {DEFAULT_MODEL})")
    args = parser.parse_args()

    if args.setup:
        setup_interactive()
        return

    # Get prompt
    if args.prompt:
        prompt = args.prompt
    elif args.prompt_file:
        prompt = args.prompt_file.read_text(encoding="utf-8")
    else:
        print("Error: need --prompt or --prompt-file", file=sys.stderr)
        parser.print_help()
        sys.exit(1)

    token = get_token()

    # Upload file if provided
    file_info = None
    if args.pdf:
        if not args.pdf.exists():
            print(f"Error: {args.pdf} not found", file=sys.stderr)
            sys.exit(1)
        file_info = upload_file(token, args.pdf)

    # Send message and get response
    response = send_message(token, prompt, model=args.model, file_info=file_info)

    if not response:
        print("[chatgpt] ERROR: Empty response", file=sys.stderr)
        sys.exit(1)

    # Save or print response
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        metadata = {
            "timestamp": datetime.now().isoformat(),
            "model": args.model,
            "prompt_length": len(prompt),
            "response_length": len(response),
        }
        if args.pdf:
            metadata["pdf"] = str(args.pdf)
        args.output.write_text(
            f"<!-- oracle metadata: {json.dumps(metadata)} -->\n\n{response}",
            encoding="utf-8",
        )
        print(f"[chatgpt] Saved to {args.output}")
    else:
        print("\n" + response)


if __name__ == "__main__":
    main()
