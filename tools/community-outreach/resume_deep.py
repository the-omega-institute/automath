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
    p.add_argument("--max-turns", type=int, default=50,
                   help="Hard safety cap to prevent runaway loops (default: 50). "
                        "In codex-evaluator mode this is rarely reached — codex "
                        "decides when the original objective has been met.")
    p.add_argument("--per-turn-timeout", type=int, default=7200)
    p.add_argument("--board", default=str(REPO_ROOT / "tools/community-outreach/RESEARCH_BOARD.md"))
    p.add_argument("--objective", default=None,
                   help="Original objective to drive codex evaluator. If omitted, "
                        "uses the prompt of the first turn from the session.")
    p.add_argument("--no-evaluator", action="store_true",
                   help="Bypass the codex evaluator and use the legacy regex-based "
                        "BREAKTHROUGH/STUCK detection (only kept for backwards "
                        "compatibility — not recommended).")
    p.add_argument("--write-latex", action="store_true",
                   help="On 'complete' verdict (or any prior BREAKTHROUGH), send the "
                        "WRITE_PAPER_LATEX terminal turn. Saves the result to "
                        "theory/2026_outreach_<slug>/main.tex.")
    p.add_argument("--polish", action="store_true",
                   help="With --write-latex, also run codex polish (generate_outreach_paper) "
                        "after saving the oracle LaTeX.")
    p.add_argument("--ship-paper", action="store_true",
                   help="With --write-latex --polish, also drive the polished paper "
                        "through the full P0-P7 publication pipeline.")
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
    # Derive objective: explicit --objective wins; otherwise use the prompt of
    # the first turn (it contains the sub-goal block). Codex evaluator uses
    # this as the "did we get there?" anchor.
    if args.objective:
        objective = args.objective
    elif turns:
        objective = turns[0].get("prompt") or todo.statement or todo.title
    else:
        objective = todo.statement or todo.title or ""
    print(f"[resume] starting at turn {starting_turn}, safety_cap={args.max_turns}, "
          f"evaluator={'on' if not args.no_evaluator else 'off (legacy regex mode)'}")
    if objective:
        print(f"[resume] objective[:200]: {objective[:200]}{'...' if len(objective) > 200 else ''}")

    stuck_streak = 0
    next_followup = None  # populated by evaluator on the next iteration

    for turn_no in range(starting_turn, args.max_turns + 1):
        # 1. Generate next follow-up. First iteration: legacy codex generator.
        # Subsequent: evaluator output from the previous turn.
        if next_followup is not None:
            followup = next_followup
            print(f"\n[turn {turn_no}] follow-up from evaluator ({len(followup)} chars):")
        else:
            print(f"\n[turn {turn_no}] generating follow-up via codex (initial)...")
            followup = oc.codex_driven_prompt_generator(
                turn_no - 1, last_response, turns, todo, timeout_s=300,
            )
            print(f"[turn {turn_no}] follow-up ({len(followup)} chars):")
        print(f"  {followup[:240]}{'...' if len(followup) > 240 else ''}")

        # 2. Submit as follow-up to existing conversation
        submit_resp = submit_followup(followup, args.conv,
                                      tag=f"{args.target}:deep_resume:t{turn_no}")
        if "error" in submit_resp:
            print(f"[turn {turn_no}] submit failed: {submit_resp.get('error')}", file=sys.stderr)
            break
        task_id = submit_resp.get("task_id", "")
        print(f"[turn {turn_no}] submitted task={task_id} (conv={args.conv[:12]})")

        # 3. Poll for response
        response = oc.oracle_poll(task_id, timeout=args.per_turn_timeout)
        if not response:
            print(f"[turn {turn_no}] empty response (timeout/extraction failure)", file=sys.stderr)
            break
        print(f"[turn {turn_no}] {len(response)} chars received")

        # 4. Codex evaluator: contribution + verdict + next_question
        eval_result = None
        if not args.no_evaluator:
            print(f"[turn {turn_no}] running codex evaluator...")
            eval_result = oc.codex_evaluate_progress(
                turn_no, response, turns, objective, timeout_s=300,
            )
            print(f"[turn {turn_no}] verdict={eval_result['verdict']}: "
                  f"{eval_result['verdict_reason'][:120]}")
            print(f"[turn {turn_no}] contribution: {eval_result['contribution'][:200]}"
                  f"{'...' if len(eval_result['contribution']) > 200 else ''}")
            next_followup = eval_result["next_question"] if eval_result["verdict"] == "continue" else None
        else:
            next_followup = None  # legacy mode — let next iteration call codex driver

        # 5. Append to session
        turn_record = {
            "turn": turn_no,
            "task_id": task_id,
            "prompt": followup,
            "prompt_source": "evaluator" if (eval_result is None and next_followup is None) else "codex_resume",
            "response": response,
            "response_chars": len(response),
            "completed_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        }
        if eval_result is not None:
            turn_record["evaluator"] = {
                "contribution": eval_result["contribution"],
                "verdict": eval_result["verdict"],
                "verdict_reason": eval_result["verdict_reason"],
            }

        try:
            disk_sess = json.loads(sess_path.read_text())
        except Exception:
            disk_sess = sess
        disk_turns = disk_sess.get("turns", []) or []
        existing_idx = next((i for i, t in enumerate(disk_turns)
                             if t.get("task_id") == task_id), None)
        if existing_idx is not None:
            disk_turns[existing_idx] = turn_record
        else:
            disk_turns.append(turn_record)
        disk_sess["turns"] = disk_turns
        sess_path.write_text(json.dumps(disk_sess, indent=2, ensure_ascii=False))
        turns = list(disk_turns)
        sess = disk_sess
        print(f"[turn {turn_no}] session updated → {sess_path.name} ({len(turns)} turns total)")

        # 6. Stop logic
        if eval_result is not None:
            verdict = eval_result["verdict"]
            if verdict == "complete":
                print(f"[turn {turn_no}] COMPLETE — objective achieved per evaluator. Stopping.")
                break
            if verdict == "stuck":
                print(f"[turn {turn_no}] STUCK — evaluator says no Oracle bypass. Stopping.")
                break
            # else "continue" — loop again
        else:
            # Legacy regex mode
            if STOP_BREAKTHROUGH.search(response):
                print(f"[turn {turn_no}] BREAKTHROUGH detected (regex), stopping")
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

    if turn_no >= args.max_turns:
        print(f"\n[resume] WARN: hit safety cap max_turns={args.max_turns} without "
              f"explicit complete/stuck verdict. Bump --max-turns or inspect transcripts.")

    print(f"\n[resume] done. Final turn count: {len(turns)}")

    # --write-latex pipeline: if any prior turn already had BREAKTHROUGH (per
    # fixed regex), short-circuit further follow-ups and send the
    # WRITE_PAPER_LATEX terminal turn now to capture the paper draft.
    if args.write_latex:
        had_break = any(STOP_BREAKTHROUGH.search(t.get("response","")) for t in turns)
        if not had_break:
            print("[write-latex] no BREAKTHROUGH found in any prior turn — skipping LaTeX phase")
            return 0
        print("[write-latex] BREAKTHROUGH found; sending WRITE_PAPER_LATEX terminal turn...")
        terminal_prompt = oc.DEFAULT_WRITE_PAPER_LATEX_PROMPT
        submit_resp = submit_followup(terminal_prompt, args.conv,
                                      tag=f"{args.target}:write_latex")
        if "error" in submit_resp:
            print(f"[write-latex] submit failed: {submit_resp.get('error')}", file=sys.stderr)
            return 3
        task_id = submit_resp.get("task_id","")
        print(f"[write-latex] submitted {task_id}; polling (timeout={args.per_turn_timeout}s)...")
        response = oc.oracle_poll(task_id, timeout=args.per_turn_timeout)
        if not response:
            print("[write-latex] empty response — Oracle didn't write LaTeX", file=sys.stderr)
            return 3
        latex_body, plain_summary = oc.extract_latex_from_response(response)
        if not latex_body:
            print("[write-latex] response had no fenced LaTeX block; saving raw response",
                  file=sys.stderr)
            print(f"[write-latex] response[:400]: {response[:400]}", file=sys.stderr)
            return 3
        slug = oc._safe_outreach_slug(todo.slug())
        latex_out = oc._outreach_latex_path(slug)
        latex_out.parent.mkdir(parents=True, exist_ok=True)
        latex_out.write_text(latex_body, encoding="utf-8")
        print(f"[write-latex] saved {len(latex_body)} chars → {latex_out}")
        if plain_summary:
            (latex_out.parent / "plain_summary.txt").write_text(plain_summary, encoding="utf-8")

        # Persist the terminal turn into session
        turn_record = {
            "turn": len(turns) + 1,
            "task_id": task_id,
            "prompt": terminal_prompt,
            "prompt_source": "terminal_write_latex",
            "response": response,
            "response_chars": len(response),
            "completed_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        }
        try:
            disk_sess = json.loads(sess_path.read_text())
        except Exception:
            disk_sess = sess
        dt = disk_sess.get("turns", []) or []
        dt.append(turn_record)
        disk_sess["turns"] = dt
        sess_path.write_text(json.dumps(disk_sess, indent=2, ensure_ascii=False))

        if args.polish:
            print(f"[polish] running codex on {latex_out}...")
            try:
                oc.generate_outreach_paper(latex_out, timeout=3600)
                print(f"[polish] done")
            except Exception as exc:
                print(f"[polish] failed: {exc}", file=sys.stderr)
                return 4

        if args.ship_paper and args.polish:
            print(f"[ship] running paper pipeline on {latex_out.parent}...")
            try:
                result = oc.run_paper_pipeline(latex_out.parent)
                print(f"[ship] exit={result.get('exit_code')} pdf={result.get('pdf_path','')}")
                if result.get("error"):
                    print(f"[ship] error: {result['error']}", file=sys.stderr)
            except Exception as exc:
                print(f"[ship] failed: {exc}", file=sys.stderr)
                return 5

    return 0


if __name__ == "__main__":
    sys.exit(main())
