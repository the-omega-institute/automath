#!/usr/bin/env python3
"""Budget-limited X signal collector for open-problem discovery.

This is a discovery input, not an outreach channel. It never posts. It queries
NyxID's configured X/Twitter service for recent high-visibility open-problem
chatter, writes a local JSON snapshot, and enforces a once-per-day / max-budget
gate before making network calls.

The downstream board_refill Oracle decides whether any signal is a real
open-problem candidate. Existing email/GitHub collaborations are not added to
the board from this feed.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import time
import urllib.parse
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_DIR = SCRIPT_DIR / "outreach_state"
STATUS_PATH = STATE_DIR / "x_openproblem_watch.status.json"
OUT_PATH = STATE_DIR / "x_openproblem_recent.json"

DEFAULT_BUDGET_USD = 1.0
DEFAULT_COOLDOWN_HOURS = 24
DEFAULT_MAX_RESULTS_PER_QUERY = 10
DEFAULT_SERVICE_SLUG = "api-twitter"

QUERIES = [
    '"open problem" math lang:en -is:retweet',
    '"open conjecture" math lang:en -is:retweet',
    '"unsolved problem" mathematics lang:en -is:retweet',
    '"Lean" "open problem" math lang:en -is:retweet',
    '"arXiv" "open problem" mathematics lang:en -is:retweet',
]


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _nyxid_bin() -> str:
    p = shutil.which("nyxid")
    if p:
        return p
    fallback = Path.home() / ".cargo/bin/nyxid"
    return str(fallback)


def _load_status() -> dict:
    try:
        return json.loads(STATUS_PATH.read_text(encoding="utf-8"))
    except Exception:
        return {}


def _write_status(d: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    STATUS_PATH.write_text(json.dumps(d, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _cooldown_ok(hours: float) -> tuple[bool, str]:
    status = _load_status()
    last = status.get("last_success_epoch")
    if not last:
        return True, "no prior success"
    age_h = (time.time() - float(last)) / 3600.0
    if age_h >= hours:
        return True, f"last success {age_h:.1f}h ago"
    return False, f"cooldown active: last success {age_h:.1f}h ago < {hours}h"


def _estimate_cost_usd(num_queries: int, max_results: int) -> float:
    # Conservative placeholder. Replace with NyxID metering if/when available.
    # The important gate is that callers cannot silently expand query volume.
    return 0.01 * num_queries * max(1, max_results / 10)


def _run_nyxid_search(query: str, *, service_slug: str, max_results: int, timeout: int = 30) -> dict:
    params = urllib.parse.urlencode({
        "query": query,
        "max_results": str(max_results),
        "tweet.fields": "created_at,public_metrics,author_id,entities",
    })
    endpoint = f"/2/tweets/search/recent?{params}"
    cmd = [
        _nyxid_bin(),
        "proxy", "request", service_slug, endpoint,
        "-m", "GET",
    ]
    proc = subprocess.run(cmd, cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=timeout)
    if proc.returncode != 0:
        return {"ok": False, "error": (proc.stderr or proc.stdout)[:800], "query": query}
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError:
        return {"ok": False, "error": f"non-json response: {proc.stdout[:500]}", "query": query}
    return {"ok": True, "query": query, "payload": payload}


def _rank_rows(raw_rows: list[dict]) -> list[dict]:
    rows: list[dict] = []
    seen: set[str] = set()
    for raw in raw_rows:
        if not raw.get("ok"):
            rows.append({"query": raw.get("query"), "status": "error", "error": raw.get("error", "")})
            continue
        for tweet in ((raw.get("payload") or {}).get("data") or []):
            tid = str(tweet.get("id") or "")
            if not tid or tid in seen:
                continue
            seen.add(tid)
            metrics = tweet.get("public_metrics") or {}
            score = (
                int(metrics.get("like_count") or 0)
                + 2 * int(metrics.get("retweet_count") or 0)
                + 2 * int(metrics.get("reply_count") or 0)
                + int(metrics.get("quote_count") or 0)
            )
            rows.append({
                "status": "ok",
                "query": raw.get("query"),
                "id": tid,
                "url": f"https://x.com/i/web/status/{tid}",
                "created_at": tweet.get("created_at"),
                "text": tweet.get("text"),
                "metrics": metrics,
                "visibility_score": score,
            })
    rows.sort(key=lambda r: int(r.get("visibility_score") or 0), reverse=True)
    return rows


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--dry-run", action="store_true", help="show planned queries and budget only")
    p.add_argument("--force", action="store_true", help="ignore daily cooldown")
    p.add_argument("--budget-usd", type=float, default=DEFAULT_BUDGET_USD)
    p.add_argument("--cooldown-hours", type=float, default=DEFAULT_COOLDOWN_HOURS)
    p.add_argument("--max-results", type=int, default=DEFAULT_MAX_RESULTS_PER_QUERY)
    p.add_argument("--service-slug", default=DEFAULT_SERVICE_SLUG)
    p.add_argument("--write", action="store_true", help="write x_openproblem_recent.json")
    args = p.parse_args(argv)

    estimate = _estimate_cost_usd(len(QUERIES), args.max_results)
    cooldown_ok, cooldown_reason = _cooldown_ok(args.cooldown_hours)
    plan = {
        "generated_at": _now_iso(),
        "dry_run": args.dry_run,
        "service_slug": args.service_slug,
        "queries": QUERIES,
        "max_results": args.max_results,
        "estimated_cost_usd": round(estimate, 4),
        "budget_usd": args.budget_usd,
        "cooldown_ok": cooldown_ok,
        "cooldown_reason": cooldown_reason,
    }
    if estimate > args.budget_usd:
        plan["verdict"] = "blocked_budget"
        print(json.dumps(plan, ensure_ascii=False, indent=2))
        _write_status({**plan, "last_run_epoch": time.time()})
        return 2
    if not args.force and not cooldown_ok:
        plan["verdict"] = "blocked_cooldown"
        print(json.dumps(plan, ensure_ascii=False, indent=2))
        _write_status({**plan, "last_run_epoch": time.time()})
        return 0
    if args.dry_run:
        plan["verdict"] = "dry_run"
        print(json.dumps(plan, ensure_ascii=False, indent=2))
        return 0

    raw = [
        _run_nyxid_search(q, service_slug=args.service_slug, max_results=args.max_results)
        for q in QUERIES
    ]
    rows = _rank_rows(raw)
    payload = {
        **plan,
        "verdict": "ok",
        "results": rows[:50],
        "errors": [r for r in raw if not r.get("ok")],
    }
    if args.write:
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        OUT_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    _write_status({**plan, "verdict": "ok", "last_run_epoch": time.time(), "last_success_epoch": time.time()})
    print(json.dumps(payload, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
