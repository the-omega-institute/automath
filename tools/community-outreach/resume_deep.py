#!/usr/bin/env python3
"""Resume an in-flight oracle deep-reasoning run from turn N+1.

Use case: deep_reasoning() always starts at turn 0; if a previous --supervise
run captured turns 1-2 in session JSON and you want to push turns 3+ without
re-doing the BREAKTHROUGH-grade earlier work, this driver picks up where the
session left off, generates the next codex follow-up from the last response,
and dispatches via the same conversation_id so ChatGPT keeps full context.

Usage:
    python3 resume_deep.py --conv conv_4b15545d611f46c5 --target T-20 \
        --max-turns 8 --per-turn-timeout 7200
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).parent))

import oracle_consultant as oc  # noqa: E402
from dispatch_worktree import parse_board  # noqa: E402

SESS_DIR = REPO_ROOT / "tools/community-outreach/outreach_oracle/sessions"

STOP_BREAKTHROUGH = re.compile(r"(?:BREAKTHROUGH|PROVED|Q\.E\.D\.?)\b")
STOP_STUCK = re.compile(r"\bSTUCK\b|\bdead end\b|\bcannot proceed\b")


def submit_followup(prompt: str, conv_id: str, tag: str) -> dict:
    task_id = f"deep_resume_{conv_id[:12]}_{int(time.time())}"
    body = {
        "task_id": task_id,
        "prompt": prompt,
        "conversation_id": conv_id,
        "is_followup": True,
        "tag": tag,
    }
    return oc.http_post(f"{oc.ORACLE_SERVER}/submit", body, timeout=10)


def fresh_response_from_server(task_id: str, fallback: str = "") -> str:
    """Pull the latest extracted response for `task_id` from server's result
    store. Server's /result is more authoritative than the local session JSON,
    which can lag behind because the userscript may re-extract a previously
    truncated response after Pro-thinking false-stable triggered an early
    capture. Use this whenever feeding context to codex.
    """
    try:
        r = oc.http_get(f"{oc.ORACLE_SERVER}/result/{task_id}", timeout=10)
        if r.get("status") == "completed":
            text = r.get("response") or ""
            if text:
                return text
    except Exception:
        pass
    return fallback


def enrich_turns_with_fresh(turns: list[dict]) -> list[dict]:
    """Return a copy of `turns` with each turn's response replaced by the
    fresh server-side version (when newer / longer). Does not mutate input.
    """
    out = []
    for t in turns:
        t2 = dict(t)
        old = t2.get("response") or ""
        tid = t2.get("task_id") or ""
        if tid:
            fresh = fresh_response_from_server(tid, fallback=old)
            if len(fresh) > len(old):
                t2["response"] = fresh
                t2["response_chars"] = len(fresh)
        out.append(t2)
    return out


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--conv", required=True, help="conversation_id of the deep run to resume")
    p.add_argument("--target", required=True, help="TODO id (e.g. T-20)")
    p.add_argument("--max-turns", type=int, default=8)
    p.add_argument("--per-turn-timeout", type=int, default=7200)
    p.add_argument("--board", default=str(REPO_ROOT / "tools/community-outreach/RESEARCH_BOARD.md"))
    args = p.parse_args()

    sess_path = SESS_DIR / f"{args.conv}.json"
    if not sess_path.exists():
        print(f"ERR: session {sess_path} not found", file=sys.stderr)
        return 1
    sess = json.loads(sess_path.read_text())
    turns = sess.get("turns", []) or []
    print(f"[resume] loaded {len(turns)} prior turns from {sess_path.name}")

    todos = parse_board(Path(args.board))
    todo = todos.get(args.target)
    if not todo:
        print(f"ERR: {args.target} not in board", file=sys.stderr)
        return 1

    consultant = oc.OracleConsultant()
    if not consultant.is_alive():
        print(f"ERR: oracle server down at {oc.ORACLE_SERVER}", file=sys.stderr)
        return 2

    # Enrich session turns with fresh server-side response text. Bypasses any
    # stale truncated-response captures that the userscript may have written
    # before the Pro-thinking re-extract completed.
    turns = enrich_turns_with_fresh(turns)
    for i, t in enumerate(turns, 1):
        print(f"[resume] turn {i}: {t.get('response_chars',0)} chars (post-enrich)")

    last_response = (turns[-1].get("response") or "") if turns else ""
    starting_turn = len(turns) + 1
    print(f"[resume] starting at turn {starting_turn}, max_turns={args.max_turns}")

    stuck_streak = 0
    for turn_no in range(starting_turn, args.max_turns + 1):
        # Codex generates next follow-up from the last response
        print(f"\n[turn {turn_no}] generating follow-up via codex...")
        followup = oc.codex_driven_prompt_generator(
            turn_no - 1,  # codex sees "turn N done, generate prompt for turn N+1"
            last_response,
            turns,
            todo,
            timeout_s=300,
        )
        print(f"[turn {turn_no}] follow-up ({len(followup)} chars):")
        print(f"  {followup[:240]}{'...' if len(followup) > 240 else ''}")

        # Submit as follow-up to existing conversation
        submit_resp = submit_followup(followup, args.conv, tag=f"{args.target}:deep_resume:t{turn_no}")
        if "error" in submit_resp:
            print(f"[turn {turn_no}] submit failed: {submit_resp.get('error')}", file=sys.stderr)
            break
        task_id = submit_resp.get("task_id", "")
        print(f"[turn {turn_no}] submitted task={task_id} (conv={args.conv[:12]})")

        # Poll for response
        response = oc.oracle_poll(task_id, timeout=args.per_turn_timeout)
        if not response:
            print(f"[turn {turn_no}] empty response (timeout/extraction failure)", file=sys.stderr)
            break
        print(f"[turn {turn_no}] {len(response)} chars received")

        # Append to session — reload from disk to pick up any concurrent
        # server writes (e.g. /done landing for our task), then append our
        # turn record on top of the fresh disk view. Avoids overwriting
        # server-side updates we made in parallel.
        turn_record = {
            "turn": turn_no,
            "task_id": task_id,
            "prompt": followup,
            "prompt_source": "codex_resume",
            "response": response,
            "response_chars": len(response),
            "completed_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        }
        try:
            disk_sess = json.loads(sess_path.read_text())
        except Exception:
            disk_sess = sess  # fallback to in-memory
        # Dedupe: if disk already has a turn with this task_id, replace; else append.
        disk_turns = disk_sess.get("turns", []) or []
        existing_idx = next((i for i, t in enumerate(disk_turns)
                             if t.get("task_id") == task_id), None)
        if existing_idx is not None:
            disk_turns[existing_idx] = turn_record
        else:
            disk_turns.append(turn_record)
        disk_sess["turns"] = disk_turns
        sess_path.write_text(json.dumps(disk_sess, indent=2, ensure_ascii=False))
        # Sync our in-memory view from the freshly-written disk state
        turns = list(disk_turns)
        sess = disk_sess
        print(f"[turn {turn_no}] session updated → {sess_path.name} ({len(turns)} turns total)")

        # Stop conditions
        if STOP_BREAKTHROUGH.search(response):
            print(f"[turn {turn_no}] BREAKTHROUGH detected, stopping")
            break
        if STOP_STUCK.search(response):
            stuck_streak += 1
            print(f"[turn {turn_no}] STUCK marker (streak={stuck_streak})")
            if stuck_streak >= 2:
                print(f"[turn {turn_no}] STUCK streak ≥ 2, stopping")
                break
        else:
            stuck_streak = 0

        last_response = response

    print(f"\n[resume] done. Final turn count: {len(turns)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
