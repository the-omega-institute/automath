#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Backlog refill — propose new paper-split candidates from the main paper context.

This is the "fallback" producer: it only fires when there is nothing else to
work on. The supervisor calls it after `discover_runnable_papers()` returns
empty, and only after a long cooldown (default 7 days). Output is a JSON
queue of candidates that the operator inspects and manually promotes via
`oracle_pipeline.py --new --topic ...`.

Pattern adapted from:
  * tools/bedc-deep/oracle_board_refill.py (newmath@bedc-claim-packet-pipeline)
  * tools/community-outreach/outreach_board_refill.py (origin/openproblem-target)

Difference vs those: there is no auto-promotion gate. The operator stays in
the loop because (a) we never want to drown ongoing work in speculative new
papers and (b) the publication pipeline already has a `--new --topic`
human-in-the-loop entry point that handles the actual writing.

Usage:
    # Run once, write candidates to papers/publication/_refill_queue.json
    python tools/chatgpt-oracle/paper_refill.py \\
        --project-url "https://chatgpt.com/g/g-p-xxxxxxxx-omega/project" \\
        --limit 5 --timeout 1800

    # Smoke test (no Oracle call, just shape the prompt + print it)
    python tools/chatgpt-oracle/paper_refill.py --dry-run --limit 5
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
PUBLICATION_DIR = REPO_ROOT / "papers" / "publication"
QUEUE_PATH = PUBLICATION_DIR / "_refill_queue.json"
REFILL_LOG_DIR = SCRIPT_DIR / "supervisor_logs"

DEFAULT_LIMIT = 5
DEFAULT_TIMEOUT = 1800
DEFAULT_MODEL = "chatgpt-5.4-pro"
QUEUE_VERSION = 1

sys.path.insert(0, str(SCRIPT_DIR))
import oracle_dispatch  # noqa: E402


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _existing_paper_names() -> list[str]:
    if not PUBLICATION_DIR.exists():
        return []
    return sorted(
        child.name
        for child in PUBLICATION_DIR.iterdir()
        if child.is_dir() and not child.name.startswith((".", "_")) and (child / "main.tex").exists()
    )


def _load_existing_queue() -> dict[str, Any]:
    if not QUEUE_PATH.exists():
        return {"version": QUEUE_VERSION, "updated_at": "", "candidates": []}
    try:
        return json.loads(QUEUE_PATH.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return {"version": QUEUE_VERSION, "updated_at": "", "candidates": []}


def _existing_proposed_titles(queue: dict[str, Any]) -> list[str]:
    out = []
    for item in queue.get("candidates", []):
        if isinstance(item, dict) and item.get("proposed_title"):
            out.append(item["proposed_title"])
    return out


def build_refill_prompt(limit: int, existing_papers: list[str],
                        existing_proposals: list[str]) -> str:
    schema = {
        "candidates": [
            {
                "proposed_title": "concise paper title in English",
                "topic": "one-paragraph topic statement (suitable as --topic argument)",
                "outline": [
                    "section 1 statement",
                    "section 2 statement",
                    "section 3 statement",
                ],
                "anchor_theorems": [
                    "theorem-shaped statement the paper will prove",
                ],
                "target_journal": "best-fit journal name + tier",
                "fit_score": 0,
                "novelty_score": 0,
                "rationale": "why this is a good next split",
                "risks": ["overlap or scope risk"],
            }
        ]
    }
    return (
        "You are the Oracle backlog producer for the Omega publication pipeline.\n"
        "The main theory paper (already attached to this Project) is the source of truth. "
        "We split it into journal-targeted papers; each split must be a coherent, "
        "publishable result, not a fragment.\n\n"
        "Existing publication directories (do NOT propose duplicates of these):\n"
        f"{json.dumps(existing_papers, ensure_ascii=False, indent=2)}\n\n"
        "Existing refill candidates already on the queue (do NOT propose duplicates):\n"
        f"{json.dumps(existing_proposals, ensure_ascii=False, indent=2)}\n\n"
        f"Propose at most {limit} new high-quality paper splits. "
        "Hard rules:\n"
        "- Each candidate must have fit_score >= 7 and novelty_score >= 7.\n"
        "- target_journal must be a real journal that publishes the kind of result described.\n"
        "- anchor_theorems must be theorem-shaped (formal statement, not a marketing line).\n"
        "- Quality > quantity: returning fewer than the limit is fine, padding the quota is not.\n"
        "- Avoid ideas that the existing list already covers.\n\n"
        "Output JSON only with this schema (no markdown fences):\n"
        f"{json.dumps(schema, ensure_ascii=False, indent=2)}"
    )


def _extract_json(text: str) -> dict[str, Any] | None:
    """Tolerantly extract a JSON object from a possibly-fenced response."""
    if not text:
        return None
    s = text.strip()
    if s.startswith("```"):
        # strip ```json ... ``` or ``` ... ```
        s = s.split("```", 2)[1] if s.count("```") >= 2 else s
        if s.startswith("json"):
            s = s[4:]
        s = s.strip("` \n\r\t")
    # If there is preamble before the JSON, find the first {.
    first = s.find("{")
    last = s.rfind("}")
    if first == -1 or last == -1 or last < first:
        return None
    try:
        return json.loads(s[first: last + 1])
    except json.JSONDecodeError:
        return None


def normalize_candidates(raw: list[dict[str, Any]]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for item in raw:
        if not isinstance(item, dict):
            continue
        title = str(item.get("proposed_title", "")).strip()
        topic = str(item.get("topic", "")).strip()
        if not title or not topic:
            continue
        try:
            fit = int(item.get("fit_score", 0) or 0)
            novelty = int(item.get("novelty_score", 0) or 0)
        except (TypeError, ValueError):
            continue
        if fit < 7 or novelty < 7:
            continue
        outline = [str(s).strip() for s in item.get("outline", []) if str(s).strip()]
        anchors = [str(s).strip() for s in item.get("anchor_theorems", []) if str(s).strip()]
        risks = [str(s).strip() for s in item.get("risks", []) if str(s).strip()]
        out.append({
            "id": f"refill_{int(time.time() * 1000)}_{len(out):02d}",
            "status": "open",
            "proposed_title": title,
            "topic": topic,
            "outline": outline,
            "anchor_theorems": anchors,
            "target_journal": str(item.get("target_journal", "")).strip(),
            "fit_score": fit,
            "novelty_score": novelty,
            "rationale": str(item.get("rationale", "")).strip(),
            "risks": risks,
            "discovered_at": _now_iso(),
        })
    return out


def write_queue(candidates: list[dict[str, Any]], *, conversation_id: str) -> Path:
    queue = _load_existing_queue()
    existing_titles = {c.get("proposed_title") for c in queue.get("candidates", []) if isinstance(c, dict)}
    new_items = [c for c in candidates if c["proposed_title"] not in existing_titles]
    queue["version"] = QUEUE_VERSION
    queue["updated_at"] = _now_iso()
    queue["last_oracle_conversation_id"] = conversation_id
    queue["candidates"] = list(queue.get("candidates", [])) + new_items
    PUBLICATION_DIR.mkdir(parents=True, exist_ok=True)
    QUEUE_PATH.write_text(
        json.dumps(queue, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    return QUEUE_PATH


def run_refill(*, project_url: str, limit: int, timeout: int, model: str,
               dry_run: bool) -> dict[str, Any]:
    REFILL_LOG_DIR.mkdir(parents=True, exist_ok=True)
    existing_papers = _existing_paper_names()
    queue = _load_existing_queue()
    existing_proposals = _existing_proposed_titles(queue)
    prompt = build_refill_prompt(limit, existing_papers, existing_proposals)

    if dry_run:
        print("=== DRY RUN — prompt that would be sent ===")
        print(prompt)
        print(f"\n=== existing_papers: {len(existing_papers)} ===")
        print(f"=== existing_proposals: {len(existing_proposals)} ===")
        return {"status": "dry_run", "candidates": [], "prompt_chars": len(prompt)}

    task_name = f"paper_refill_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    record = oracle_dispatch.dispatch_direct_record(
        task_name=task_name,
        prompt_text=prompt,
        pdf_path=None,
        model=model,
        conversation_id="",
        project_url=project_url,
        tag="paper_refill",
        timeout=timeout,
    )
    response = record.get("response", "")
    conv_id = record.get("conversation_id", "")
    if not response:
        return {
            "status": record.get("status", "no_response"),
            "candidates": [],
            "conversation_id": conv_id,
        }

    parsed = _extract_json(response)
    if not parsed:
        return {
            "status": "parse_failed",
            "candidates": [],
            "conversation_id": conv_id,
            "raw_excerpt": response[:400],
        }
    raw = parsed.get("candidates") if isinstance(parsed, dict) else None
    if not isinstance(raw, list):
        return {
            "status": "schema_failed",
            "candidates": [],
            "conversation_id": conv_id,
        }
    normalized = normalize_candidates(raw)
    queue_path = write_queue(normalized, conversation_id=conv_id)
    return {
        "status": "ok",
        "accepted": len(normalized),
        "queue_path": str(queue_path),
        "conversation_id": conv_id,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Paper backlog refill (low-frequency producer)")
    parser.add_argument("--project-url", default="",
                        help="ChatGPT Project URL with main paper attached. "
                             "Required unless --dry-run.")
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)
    parser.add_argument("--model", default=DEFAULT_MODEL)
    parser.add_argument("--dry-run", action="store_true",
                        help="Skip Oracle call; just shape and print the prompt.")
    args = parser.parse_args(argv)

    if not args.dry_run and not args.project_url:
        print("[refill] --project-url required (or pass --dry-run)", file=sys.stderr)
        return 2

    result = run_refill(
        project_url=args.project_url,
        limit=args.limit,
        timeout=args.timeout,
        model=args.model,
        dry_run=args.dry_run,
    )
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result.get("status") in {"ok", "dry_run"} else 1


if __name__ == "__main__":
    sys.exit(main())
