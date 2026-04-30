#!/usr/bin/env python3
"""x_broadcast.py — Round 6.5 X (Twitter) broadcast for solved targets.

Routes POST /tweets through NyxID `api-twitter` proxy (free tier, 17/day).
HARD RULE: never posts without --confirm-post. The pipeline can call --draft
to generate a thread; only the user (or an explicit --confirm-post run) ever
publishes anything.

Workflow:
    1. `python x_broadcast.py draft T-21`
       → reads pipeline_state/<slug>.json, builds 1-3 tweet thread, prints to stdout
    2. user reads it, edits if needed, saves to drafts/<slug>_tweet.txt
    3. `python x_broadcast.py post T-21 --confirm-post`
       → reads drafts/<slug>_tweet.txt, posts via NyxID, returns tweet URL

Per `feedback_never_post_without_approval` memory: the gate is mandatory.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import textwrap
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

REPO_ROOT = Path(__file__).resolve().parents[2]
DRAFTS_DIR = REPO_ROOT / "tools/community-outreach/drafts"
STATE_DIR = REPO_ROOT / "tools/community-outreach/outreach_state"
TWITTER_CHAR_LIMIT = 280


@dataclass
class TweetThread:
    target_slug: str
    target_id: str
    tweets: list[str]
    paper_url: Optional[str] = None
    github_url: Optional[str] = None

    def render_text(self) -> str:
        out = [f"# Draft tweet thread — {self.target_id} ({self.target_slug})"]
        for i, t in enumerate(self.tweets, 1):
            out.append(f"\n## Tweet {i}/{len(self.tweets)} ({len(t)} chars)")
            out.append(t)
        out.append("")
        out.append("# Edit above as needed, then run: x_broadcast.py post <id> --confirm-post")
        return "\n".join(out)


def _nyxid_bin() -> str:
    path = shutil.which("nyxid")
    if path:
        return path
    fallback = Path.home() / ".cargo/bin/nyxid"
    if fallback.exists():
        return str(fallback)
    raise SystemExit("nyxid CLI not found; install via NyxID install script")


def _run_nyxid(args: list[str], *, timeout: int = 30) -> dict:
    """Run nyxid command, return parsed JSON. Raises on non-zero or non-JSON."""
    cmd = [_nyxid_bin(), *args, "--output", "json"]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    if proc.returncode != 0:
        raise SystemExit(f"nyxid failed (exit {proc.returncode}): {proc.stderr.strip() or proc.stdout.strip()}")
    out = (proc.stdout or "").strip()
    if not out:
        return {}
    try:
        return json.loads(out)
    except json.JSONDecodeError as exc:
        raise SystemExit(f"nyxid output not JSON: {exc}\n{out[:500]}")


def verify_x_service() -> dict:
    """Confirm api-twitter is active. Returns the service record."""
    payload = _run_nyxid(["service", "list"])
    keys = payload.get("keys", []) if isinstance(payload, dict) else []
    twitters = [k for k in keys if k.get("slug") == "api-twitter"]
    if not twitters:
        raise SystemExit("No api-twitter service found. Run: nyxid service add api-twitter --oauth")
    svc = twitters[0]
    if svc.get("status") != "active":
        raise SystemExit(
            f"api-twitter status is {svc.get('status')!r}, expected 'active'. "
            "Re-run OAuth: delete and add api-twitter --oauth"
        )
    return svc


def build_default_thread(target_id: str, target_slug: str, state: dict) -> TweetThread:
    """Compose a 1-3 tweet thread from pipeline state.

    State shape (best effort, fields optional):
        - title: TODO title
        - oracle_score: 0-10
        - paper_url: arxiv / github URL
        - claim: one-line claim string
        - github_pr: PR URL if shipped
    """
    title = state.get("title") or state.get("todo", {}).get("title") or target_id
    claim = state.get("claim") or state.get("oracle_summary") or ""
    paper_url = state.get("paper_url") or state.get("arxiv_url")
    pr_url = state.get("github_pr") or state.get("pr_url")

    # Tweet 1 — hook + claim
    t1_lines = [
        f"New result on {title} ({target_id}):",
        "",
    ]
    if claim:
        # Trim claim to fit
        budget = TWITTER_CHAR_LIMIT - sum(len(l) for l in t1_lines) - 4
        if len(claim) > budget:
            claim = claim[: budget - 1] + "…"
        t1_lines.append(claim)
    t1 = "\n".join(t1_lines).strip()

    tweets = [t1]

    # Tweet 2 — proof / verification artefact
    if state.get("certificate_summary") or state.get("verification_notes"):
        t2 = textwrap.shorten(
            (state.get("certificate_summary") or state.get("verification_notes") or ""),
            width=TWITTER_CHAR_LIMIT,
            placeholder="…",
        )
        if t2:
            tweets.append(t2)

    # Tweet 3 — links
    link_lines = []
    if paper_url:
        link_lines.append(f"Paper: {paper_url}")
    if pr_url:
        link_lines.append(f"Code/PR: {pr_url}")
    link_lines.append(f"Pipeline: github.com/the-omega-institute/automath ({target_slug})")
    t3 = "\n".join(link_lines)
    if len(t3) <= TWITTER_CHAR_LIMIT:
        tweets.append(t3)

    return TweetThread(
        target_slug=target_slug,
        target_id=target_id,
        tweets=tweets,
        paper_url=paper_url,
        github_url=pr_url,
    )


def cmd_draft(args: argparse.Namespace) -> int:
    target_id = args.target_id
    state_files = list(STATE_DIR.glob(f"{target_id}*.json")) + list(STATE_DIR.glob(f"*{target_id.lower()}*.json"))
    if not state_files:
        # Allow drafting from minimal stub
        print(f"# No pipeline state found for {target_id} in {STATE_DIR}", file=sys.stderr)
        print(f"# Drafting minimal thread; edit before posting.", file=sys.stderr)
        state = {"title": target_id}
        target_slug = target_id.lower()
    else:
        state_path = state_files[0]
        state = json.loads(state_path.read_text())
        target_slug = state_path.stem

    thread = build_default_thread(target_id, target_slug, state)

    # Validate per-tweet length
    for i, t in enumerate(thread.tweets, 1):
        if len(t) > TWITTER_CHAR_LIMIT:
            print(f"WARN: tweet {i} is {len(t)} chars (>{TWITTER_CHAR_LIMIT}); will be rejected by X", file=sys.stderr)

    DRAFTS_DIR.mkdir(parents=True, exist_ok=True)
    out_path = DRAFTS_DIR / f"{target_id}_tweet.txt"
    out_path.write_text(thread.render_text())
    print(thread.render_text())
    print(f"\n# Saved to {out_path.relative_to(REPO_ROOT)}", file=sys.stderr)
    return 0


def _parse_draft_file(path: Path) -> list[str]:
    """Parse drafts/<id>_tweet.txt, return list of tweet bodies (skipping headers)."""
    tweets: list[str] = []
    current: list[str] = []
    in_tweet = False
    for raw in path.read_text().splitlines():
        line = raw.rstrip()
        if line.startswith("## Tweet "):
            if in_tweet and current:
                tweets.append("\n".join(current).rstrip())
                current = []
            in_tweet = True
            continue
        if line.startswith("# "):
            if in_tweet and current:
                tweets.append("\n".join(current).rstrip())
                current = []
            in_tweet = False
            continue
        if in_tweet:
            current.append(line)
    if in_tweet and current:
        tweets.append("\n".join(current).rstrip())
    # Strip leading/trailing blank lines from each
    return [t.strip() for t in tweets if t.strip()]


def post_tweet(text: str, *, reply_to: Optional[str] = None) -> dict:
    """Post a single tweet via NyxID. Returns parsed response dict (must contain data.id)."""
    body: dict = {"text": text}
    if reply_to:
        body["reply"] = {"in_reply_to_tweet_id": reply_to}
    cmd = [
        _nyxid_bin(),
        "proxy", "request", "api-twitter", "/tweets",
        "-m", "POST",
        "-d", json.dumps(body),
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
    if proc.returncode != 0:
        raise SystemExit(
            f"NyxID proxy failed (exit {proc.returncode}): {proc.stderr or proc.stdout}"
        )
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise SystemExit(f"X response not JSON: {exc}\n{proc.stdout[:500]}")


def cmd_post(args: argparse.Namespace) -> int:
    if not args.confirm_post:
        print("ERROR: --confirm-post required to actually post (this gate is intentional).", file=sys.stderr)
        return 2
    verify_x_service()

    target_id = args.target_id
    draft_path = DRAFTS_DIR / f"{target_id}_tweet.txt"
    if not draft_path.exists():
        print(f"No draft at {draft_path}. Run: x_broadcast.py draft {target_id}", file=sys.stderr)
        return 1
    tweets = _parse_draft_file(draft_path)
    if not tweets:
        print(f"Draft {draft_path} contains no parseable tweets.", file=sys.stderr)
        return 1

    print(f"Posting {len(tweets)} tweet(s) for {target_id}...", file=sys.stderr)
    posted: list[dict] = []
    reply_to: Optional[str] = None
    for i, body in enumerate(tweets, 1):
        if len(body) > TWITTER_CHAR_LIMIT:
            print(f"REFUSING: tweet {i} is {len(body)} chars (>{TWITTER_CHAR_LIMIT})", file=sys.stderr)
            return 1
        print(f"  [{i}/{len(tweets)}] {body[:60].replace(chr(10), ' ')}…", file=sys.stderr)
        resp = post_tweet(body, reply_to=reply_to)
        data = resp.get("data") or {}
        tid = data.get("id")
        if not tid:
            print(f"FAILED: no tweet id in response: {resp}", file=sys.stderr)
            return 1
        posted.append({"id": tid, "text": body})
        reply_to = tid

    # Print final URLs (assuming user is @DayShuai — actual handle resolved by X)
    print("\nPosted:", file=sys.stderr)
    receipt = {"target_id": target_id, "tweets": posted}
    receipt_path = DRAFTS_DIR / f"{target_id}_tweet_posted.json"
    receipt_path.write_text(json.dumps(receipt, indent=2))
    for p in posted:
        print(f"  https://x.com/i/web/status/{p['id']}", file=sys.stderr)
    print(f"\n# Receipt: {receipt_path.relative_to(REPO_ROOT)}", file=sys.stderr)
    print(json.dumps(receipt, indent=2))
    return 0


def cmd_verify(args: argparse.Namespace) -> int:
    svc = verify_x_service()
    print(json.dumps({"slug": svc.get("slug"), "status": svc.get("status"), "id": svc.get("id")}, indent=2))
    return 0


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="X (Twitter) broadcast via NyxID — Round 6.5")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_draft = sub.add_parser("draft", help="Generate a tweet thread draft from pipeline state")
    p_draft.add_argument("target_id", help="TODO id (e.g. T-21) or slug")
    p_draft.set_defaults(func=cmd_draft)

    p_post = sub.add_parser("post", help="Actually post the draft (requires --confirm-post)")
    p_post.add_argument("target_id")
    p_post.add_argument("--confirm-post", action="store_true",
                        help="Required gate. Without this, post refuses to fire.")
    p_post.set_defaults(func=cmd_post)

    p_verify = sub.add_parser("verify", help="Check api-twitter NyxID service is active")
    p_verify.set_defaults(func=cmd_verify)

    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
