#!/usr/bin/env python3
"""oracle_consultant.py — outreach pipeline's oracle stage (importable module).

This is NOT a standalone CLI tool the user invokes. It is wired into
`dispatch_worktree.py --supervise --oracle`, which calls `OracleConsultant.review`
after the supervisor analyses a target. Oracle becomes Stage B-third-opinion
inside the existing supervise flow.

Talks to:
  - tools/community-outreach/outreach_oracle_server.py on http://localhost:8766
  - tools/community-outreach/outreach_oracle_macos.user.js running in a ChatGPT.com
    browser tab (the userscript is the ONLY code that touches chatgpt.com)

Multi-turn capable from day 1:
  - .review(...)  → opens a fresh conversation (conversation_id auto-issued)
  - .deepen(...)  → follows up in the same conversation
  - .close(...)   → marks the conversation done on the server

Hard rules:
  - Never auto-publish anything. Output goes to outreach_state JSON + log files.
  - State JSON merge does NOT clobber dispatch-side fields.
  - If the outreach oracle server is down, review records the error and returns
    silently — the supervisor flow keeps going.

Public API (called from dispatch_worktree.supervise_board when --oracle is set):
    OracleConsultant.review(todo, research_md_path) -> OracleReview
    OracleConsultant.deepen(conv_id, follow_up_prompt) -> str
    OracleConsultant.close(conv_id) -> None
    OracleConsultant.is_alive() -> bool

There is also a small `_cli` for manual smoke tests, but the supported workflow
is via dispatch_worktree.py.
"""

from __future__ import annotations

import argparse
import base64
import json
import re
import subprocess
import sys
import time
import urllib.request
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, Optional

REPO_ROOT = Path(__file__).resolve().parents[2]
# OUTREACH-SPECIFIC: separate server (port 8766) from the paper-pipeline oracle (8765).
# Multi-turn capable from day 1 via outreach_oracle_server.py.
ORACLE_SERVER = "http://localhost:8766"
TARGETS_DIR = REPO_ROOT / "tools/community-outreach/targets"
ORACLE_LOGS_DIR = REPO_ROOT / "tools/community-outreach/logs/oracle"
STATE_DIR = REPO_ROOT / "tools/community-outreach/outreach_state"
DEFAULT_TIMEOUT = 7200  # 2 hours; ChatGPT Pro thinking can run 60+ min
DEFAULT_POLL_INTERVAL = 30
DEFAULT_WRITE_PAPER_LATEX_PROMPT = r"""You have reached a substantive result. Now write the full paper as LaTeX.

Output requirements:
1. A single self-contained LaTeX document starting with \documentclass{article} (or amsart).
2. Standard amsmath / amsthm / amssymb preamble; no exotic packages.
3. Sections in this order: Abstract, Introduction, Preliminaries, Main results (with proofs), Discussion / Open questions, References.
4. All theorems numbered. All proofs complete. All references concrete (arxiv IDs, journal volumes, year).
5. Output the LaTeX inside a single fenced block: ```latex ... ```
6. After the fenced block, write a one-paragraph summary in plain text suitable for a forum post.

Length target: 8-15 pages. No outline-only content.
"""

# Reuse the dispatch board parser
sys.path.insert(0, str(Path(__file__).parent))
from dispatch_worktree import parse_board, BOARD_PATH_DEFAULT, TodoSpec  # noqa: E402


# ---------------------------------------------------------------------------
# HTTP helpers (lifted verbatim from oracle_pipeline.py:646-664)
# ---------------------------------------------------------------------------


def http_post(url: str, data: dict, timeout: int = 30) -> dict:
    req = urllib.request.Request(
        url,
        data=json.dumps(data).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    resp = urllib.request.urlopen(req, timeout=timeout)
    # OUTREACH FIX: ChatGPT responses can contain literal control chars
    # (e.g. tab, form-feed); strict json.loads rejects them. strict=False
    # allows them inside strings, matching what the server actually sends.
    return json.loads(resp.read().decode("utf-8"), strict=False)


def http_get(url: str, timeout: int = 10) -> dict:
    resp = urllib.request.urlopen(url, timeout=timeout)
    return json.loads(resp.read().decode("utf-8"), strict=False)


def is_server_alive() -> bool:
    try:
        return "queue_length" in http_get(f"{ORACLE_SERVER}/status", timeout=5)
    except Exception:
        return False


# ---------------------------------------------------------------------------
# Submit + poll (adapted from oracle_pipeline.py:771-840 — same wire format)
# ---------------------------------------------------------------------------


def oracle_submit(task_id: str, prompt: str, *,
                  conversation_id: Optional[str] = None,
                  is_followup: bool = False,
                  tag: str = "",
                  pdf_path: Optional[Path] = None,
                  model: str = "chatgpt-5.5-pro") -> dict:
    """POST to /submit (new conv) or /continue (existing conv).

    Returns the server's JSON response (contains conversation_id + queue_position)
    or a dict with 'error' key on failure. Never raises.
    """
    payload: dict = {"task_id": task_id, "prompt": prompt, "model": model, "tag": tag}
    if conversation_id:
        payload["conversation_id"] = conversation_id
    if pdf_path and pdf_path.exists():
        with open(pdf_path, "rb") as f:
            payload["pdf_base64"] = base64.b64encode(f.read()).decode("ascii")
        payload["pdf_name"] = pdf_path.name
    endpoint = "/continue" if is_followup else "/submit"
    try:
        return http_post(f"{ORACLE_SERVER}{endpoint}", payload, timeout=30)
    except Exception as exc:  # noqa: BLE001
        print(f"[oracle] submit failed: {exc}", file=sys.stderr)
        return {"error": str(exc)}


def oracle_poll(task_id: str, *, timeout: int = DEFAULT_TIMEOUT,
                poll_interval: int = DEFAULT_POLL_INTERVAL,
                progress: bool = True) -> str:
    start = time.time()
    while time.time() - start < timeout:
        try:
            data = http_get(f"{ORACLE_SERVER}/result/{task_id}", timeout=10)
            if data.get("status") == "completed":
                r = data.get("response", "")
                if progress:
                    print(f"[oracle] done {task_id} in {int(time.time()-start)}s, "
                          f"{len(r)} chars", file=sys.stderr)
                return r
        except Exception:
            pass
        elapsed = int(time.time() - start)
        if progress and elapsed > 0 and elapsed % 60 == 0:
            print(f"[oracle] waiting on {task_id}... ({elapsed}s)", file=sys.stderr)
        time.sleep(poll_interval)
    if progress:
        print(f"[oracle] timeout {task_id} after {timeout}s", file=sys.stderr)
    return ""


# ---------------------------------------------------------------------------
# Outreach-specific response validity (different from paper-review version)
# ---------------------------------------------------------------------------


def is_outreach_response_valid(response: str) -> bool:
    """Reject extraction-failure garbage. Tuned for outreach research.md review.

    The paper-pipeline `is_oracle_response_valid` looks for "verdict / blocker /
    referee" anchors. Outreach reviews want different anchors: math content,
    score, recommendation. We keep length floor + at least one structural anchor.
    """
    if not response:
        return False
    cleaned = response.strip()
    if len(cleaned) < 1500:
        return False
    if len(cleaned.split()) < 40:
        return False
    lower = cleaned.lower()
    anchors = (
        "score", "verdict", "recommend", "fit", "fresh", "overtaken", "closed",
        "novelty", "attack", "lemma", "theorem", "proof", "bound", "open", "stage",
        "research", "missing", "concern", "risk",
    )
    return any(a in lower for a in anchors)


# ---------------------------------------------------------------------------
# Outreach review prompt
# ---------------------------------------------------------------------------


_OUTREACH_REVIEW_PROMPT = """You are an independent expert reviewer for the Omega Project's community-outreach pipeline. The pipeline targets open mathematical problems on registries like erdosproblems.com, OPG, and AimPL, with the goal: solve or substantially advance, then submit to the public venue.

You are receiving a Stage A research.md drafted by another AI assistant (Codex). You do NOT see the rest of the project; treat this as a cold read.

## Target metadata

- TODO id: {todo_id}
- Title: {title}
- Source URL: {source}
- Status (per Omega's research board): {status}
- Untouched evidence (per the board): {untouched}
- Submission target: {submission_type} → {submission_venue}

## research.md (full text, drafted by Codex)

```
{research_md}
```

## Your job, in order

1. **Literature staleness check.** Has this problem been solved, disproved, or substantially advanced in the literature (especially 2024-2026)? If yes, name the paper and verdict; the outreach contribution is then formalization-only or zero. Search what you remember and what you can infer; flag anything Codex missed.

2. **Mathematical correctness.** Are the claims in research.md true? Identify any error, ambiguity, or unstated assumption. For each issue, give a concrete fix or counterexample.

3. **Attack-plan realism.** Will the proposed attack plan actually produce a publishable contribution? Be skeptical. State what would have to be true for this to succeed and what is most likely to fail.

4. **First-mover risk.** Is anyone else (AI tool, recent paper, active forum thread) likely to publish a similar result before us? Quantify if possible.

5. **Final verdict** in this exact form, on its own line near the end:

VERDICT: <one of: PROCEED / PROCEED-WITH-CAUTION / NARROW-SCOPE / DROP / HANDOFF-LEAN>
SCORE: <integer 1-10, where 1=worthless, 5=marginal, 8=clear publishable contribution, 10=major>
TOP-RISK: <one sentence>
TOP-RECOMMENDATION: <one sentence>

Be direct. No filler. No "great question". Disagree with Codex when you have grounds. The Omega team will read your full review and make the dispatch decision."""


def build_review_prompt(todo: TodoSpec, research_md: str) -> str:
    sub = todo.submission_target()
    return _OUTREACH_REVIEW_PROMPT.format(
        todo_id=todo.todo_id,
        title=todo.title,
        source=todo.source or "(none)",
        status=todo.status or "(none)",
        untouched=todo.untouched or "(none)",
        submission_type=sub["type"],
        submission_venue=sub["venue"],
        research_md=research_md[:60000],  # safety cap
    )


# ---------------------------------------------------------------------------
# Verdict parsing
# ---------------------------------------------------------------------------


_VERDICT_TOKENS = {"PROCEED", "PROCEED-WITH-CAUTION", "NARROW-SCOPE", "DROP", "HANDOFF-LEAN"}


def parse_oracle_verdict(response: str) -> dict[str, str]:
    out: dict[str, str] = {"verdict": "", "score": "", "top_risk": "", "top_recommendation": ""}
    if not response:
        return out
    m = re.search(r"VERDICT\s*:\s*([A-Z][A-Z\-]+)", response)
    if m and m.group(1).upper() in _VERDICT_TOKENS:
        out["verdict"] = m.group(1).upper()
    m = re.search(r"SCORE\s*:\s*(\d{1,2})", response)
    if m:
        out["score"] = m.group(1)
    m = re.search(r"TOP-?RISK\s*:\s*(.+?)(?:\n|$)", response, re.IGNORECASE)
    if m:
        out["top_risk"] = m.group(1).strip()
    m = re.search(r"TOP-?RECOMMENDATION\s*:\s*(.+?)(?:\n|$)", response, re.IGNORECASE)
    if m:
        out["top_recommendation"] = m.group(1).strip()
    return out


def extract_latex_from_response(text: str) -> tuple[str, str]:
    """Extract oracle-authored LaTeX plus any plain-text post summary.

    Preferred format is a single fenced ```latex block. A bare response that
    starts with \\documentclass is also accepted. If no LaTeX document is found,
    return ("", text) so callers can persist the failure text separately.
    """
    if not text:
        return "", ""
    fence = re.search(r"```(?:latex|tex)\s*\n?(.*?)\n?```", text, re.IGNORECASE | re.DOTALL)
    if fence:
        latex_body = fence.group(1).strip()
        plain_summary = text[fence.end():].strip()
        return (latex_body + "\n") if latex_body else "", plain_summary
    stripped = text.lstrip()
    if stripped.startswith(r"\documentclass"):
        return stripped.rstrip() + "\n", ""
    return "", text


def _safe_outreach_slug(raw_slug: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9_-]+", "_", raw_slug.strip())
    slug = re.sub(r"_+", "_", slug).strip("_-")
    return slug or "untitled"


def _outreach_latex_path(slug: str) -> Path:
    safe_slug = _safe_outreach_slug(slug)
    return REPO_ROOT / "theory" / f"2026_outreach_{safe_slug}" / "main.tex"


# ---------------------------------------------------------------------------
# Review record
# ---------------------------------------------------------------------------


@dataclass
class OracleReview:
    todo_id: str
    title: str
    task_id: str
    conversation_id: str
    chatgpt_url: str
    submitted_at: str
    completed_at: str
    elapsed_seconds: int
    response_chars: int
    response_valid: bool
    verdict: str
    score: str
    top_risk: str
    top_recommendation: str
    response_log_path: str
    prompt_log_path: str
    is_followup: bool = False
    parent_task_id: str = ""
    error: str = ""

    def to_dict(self) -> dict:
        return asdict(self)


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


class OracleConsultant:
    """Phase 1: single-shot third-opinion reviewer for outreach research.md."""

    def __init__(self, *, server_url: str = ORACLE_SERVER,
                 logs_dir: Path = ORACLE_LOGS_DIR,
                 state_dir: Path = STATE_DIR):
        self.server_url = server_url
        self.logs_dir = logs_dir
        self.state_dir = state_dir
        self.logs_dir.mkdir(parents=True, exist_ok=True)
        self.state_dir.mkdir(parents=True, exist_ok=True)

    def is_alive(self) -> bool:
        return is_server_alive()

    def review(self, todo: TodoSpec, research_md_path: Path,
               *, timeout: int = DEFAULT_TIMEOUT,
               conversation_id: Optional[str] = None) -> OracleReview:
        """Submit research.md to outreach oracle. New conversation by default.

        If `conversation_id` is given, the review continues an existing thread
        (Phase 2 / multi-turn). If None, server issues a fresh conversation_id.
        Caller should check `is_alive()` first; on server-down the review is
        recorded with error.
        """
        slug = todo.slug()
        task_id = f"review_{slug}_{int(time.time())}"
        submitted_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        prompt_log = self.logs_dir / f"{task_id}.prompt.txt"
        response_log = self.logs_dir / f"{task_id}.response.txt"

        def _empty(error: str, conv_id: str = "") -> OracleReview:
            return OracleReview(
                todo_id=todo.todo_id, title=todo.title, task_id=task_id,
                conversation_id=conv_id, chatgpt_url="",
                submitted_at=submitted_at, completed_at=submitted_at, elapsed_seconds=0,
                response_chars=0, response_valid=False,
                verdict="", score="", top_risk="", top_recommendation="",
                response_log_path="", prompt_log_path=str(prompt_log) if prompt_log.exists() else "",
                is_followup=bool(conversation_id), parent_task_id="",
                error=error,
            )

        if not research_md_path.exists():
            return _empty(f"research.md not found at {research_md_path}")
        if not self.is_alive():
            return _empty(
                f"outreach oracle server unreachable at {self.server_url}; "
                "start: python3 tools/community-outreach/outreach_oracle_server.py"
            )

        research_md = research_md_path.read_text(encoding="utf-8")
        prompt = build_review_prompt(todo, research_md)
        prompt_log.write_text(prompt, encoding="utf-8")

        start = time.time()
        submit_resp = oracle_submit(
            task_id, prompt,
            conversation_id=conversation_id,
            is_followup=bool(conversation_id),
            tag=f"{todo.todo_id}:{slug}",
        )
        if "error" in submit_resp:
            return _empty(f"oracle_submit error: {submit_resp.get('error')}")
        conv_id = submit_resp.get("conversation_id", conversation_id or "")

        response = oracle_poll(task_id, timeout=timeout)
        elapsed = int(time.time() - start)
        completed_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        response_log.write_text(response or "", encoding="utf-8")
        valid = is_outreach_response_valid(response)
        verdict_fields = parse_oracle_verdict(response) if valid else {
            "verdict": "", "score": "", "top_risk": "", "top_recommendation": ""
        }

        # Pull the chatgpt_url back from the server's result record
        chatgpt_url = ""
        try:
            res_record = http_get(f"{self.server_url}/result/{task_id}", timeout=5)
            chatgpt_url = res_record.get("chatgpt_url", "") if isinstance(res_record, dict) else ""
        except Exception:
            pass

        review = OracleReview(
            todo_id=todo.todo_id,
            title=todo.title,
            task_id=task_id,
            conversation_id=conv_id,
            chatgpt_url=chatgpt_url,
            submitted_at=submitted_at,
            completed_at=completed_at,
            elapsed_seconds=elapsed,
            response_chars=len(response or ""),
            response_valid=valid,
            verdict=verdict_fields["verdict"],
            score=verdict_fields["score"],
            top_risk=verdict_fields["top_risk"],
            top_recommendation=verdict_fields["top_recommendation"],
            response_log_path=str(response_log),
            prompt_log_path=str(prompt_log),
            is_followup=bool(conversation_id),
            parent_task_id="",
            error="" if response else "empty response (timeout or extraction failure)",
        )
        self._merge_into_state(slug=slug, review=review)
        return review

    def deepen(self, conversation_id: str, follow_up_prompt: str, *,
               todo: Optional[TodoSpec] = None,
               timeout: int = DEFAULT_TIMEOUT) -> OracleReview:
        """Send a follow-up turn into an existing conversation.

        For Phase 2 / multi-turn deep reasoning. Caller obtains conversation_id
        from a prior `.review()` result and posts a new prompt that ChatGPT will
        answer with full prior-conversation context.
        """
        if todo is None:
            class _Stub:
                todo_id = "deepen"
                title = "follow-up turn"
                source = ""
                status = ""
                untouched = ""
                def slug(self_inner) -> str: return f"deepen_{conversation_id[:12]}"
                def submission_target(self_inner) -> dict[str, str]:
                    return {"type": "unknown", "venue": "", "format": "markdown"}
            todo = _Stub()  # type: ignore[assignment]
        slug = todo.slug()
        task_id = f"deepen_{slug}_{int(time.time())}"
        submitted_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        prompt_log = self.logs_dir / f"{task_id}.prompt.txt"
        response_log = self.logs_dir / f"{task_id}.response.txt"
        prompt_log.write_text(follow_up_prompt, encoding="utf-8")

        if not self.is_alive():
            return OracleReview(
                todo_id=getattr(todo, "todo_id", "deepen"),
                title=getattr(todo, "title", "deepen"),
                task_id=task_id, conversation_id=conversation_id, chatgpt_url="",
                submitted_at=submitted_at, completed_at=submitted_at,
                elapsed_seconds=0, response_chars=0, response_valid=False,
                verdict="", score="", top_risk="", top_recommendation="",
                response_log_path="", prompt_log_path=str(prompt_log),
                is_followup=True, parent_task_id="",
                error=f"outreach oracle server unreachable at {self.server_url}",
            )

        start = time.time()
        submit_resp = oracle_submit(
            task_id, follow_up_prompt,
            conversation_id=conversation_id,
            is_followup=True,
            tag=getattr(todo, "todo_id", ""),
        )
        if "error" in submit_resp:
            return OracleReview(
                todo_id=getattr(todo, "todo_id", "deepen"),
                title=getattr(todo, "title", "deepen"),
                task_id=task_id, conversation_id=conversation_id, chatgpt_url="",
                submitted_at=submitted_at, completed_at=submitted_at,
                elapsed_seconds=0, response_chars=0, response_valid=False,
                verdict="", score="", top_risk="", top_recommendation="",
                response_log_path="", prompt_log_path=str(prompt_log),
                is_followup=True, parent_task_id="",
                error=f"oracle_submit error: {submit_resp.get('error')}",
            )
        response = oracle_poll(task_id, timeout=timeout)
        elapsed = int(time.time() - start)
        completed_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        response_log.write_text(response or "", encoding="utf-8")
        valid = is_outreach_response_valid(response)
        chatgpt_url = ""
        try:
            res_record = http_get(f"{self.server_url}/result/{task_id}", timeout=5)
            chatgpt_url = res_record.get("chatgpt_url", "") if isinstance(res_record, dict) else ""
        except Exception:
            pass
        review = OracleReview(
            todo_id=getattr(todo, "todo_id", "deepen"),
            title=getattr(todo, "title", "deepen"),
            task_id=task_id, conversation_id=conversation_id, chatgpt_url=chatgpt_url,
            submitted_at=submitted_at, completed_at=completed_at,
            elapsed_seconds=elapsed, response_chars=len(response or ""),
            response_valid=valid,
            verdict="", score="", top_risk="", top_recommendation="",
            response_log_path=str(response_log), prompt_log_path=str(prompt_log),
            is_followup=True, parent_task_id="",
            error="" if response else "empty response (timeout or extraction failure)",
        )
        self._merge_into_state(slug=slug, review=review)
        return review

    def close(self, conversation_id: str) -> bool:
        """Tell the server this conversation is done. Idempotent."""
        try:
            http_post(f"{self.server_url}/close", {"conversation_id": conversation_id}, timeout=10)
            return True
        except Exception:
            return False

    def deep_reasoning(self, todo: TodoSpec, initial_prompt: str, *,
                       max_turns: int = 10,
                       follow_up_prompts: Optional[list[str]] = None,
                       per_turn_timeout: int = DEFAULT_TIMEOUT,
                       stop_breakthrough_re: str = r"\bBREAKTHROUGH\b|\bPROVED\b|\bQ\.E\.D\.?\b",
                       stop_stuck_re: str = r"\bSTUCK\b|\bdead end\b|\bcannot proceed\b",
                       stuck_streak_threshold: int = 2,
                       terminal_prompt: str | None = None,
                       slug: str | None = None) -> dict:
        """Drive multi-turn deep reasoning on `todo`.

        Pattern (matches Liam Price-style "keep prodding"):
          turn 0: open conversation with `initial_prompt` (full problem framing)
          turn k>0: send next follow-up prompt from `follow_up_prompts` (rotates)
          After each turn: scan response for breakthrough or stuck markers.
          If a breakthrough is found and `terminal_prompt` is not None, send
          one final WRITE_PAPER_LATEX-style turn and save the oracle-authored
          document under theory/2026_outreach_<slug>/main.tex.

        Stop conditions:
          - response contains stop_breakthrough_re → return with verdict='BREAKTHROUGH'
          - same stuck-marker hit `stuck_streak_threshold` turns in a row → 'STUCK'
          - server unreachable / timeout on a turn → record + break
          - max_turns reached → 'EXHAUSTED'

        Returns dict:
          {
            'todo_id', 'conversation_id', 'chatgpt_url',
            'turns': [ {turn, prompt, response, response_chars, elapsed_seconds, error} ],
            'final_verdict': 'BREAKTHROUGH' | 'STUCK' | 'EXHAUSTED' | 'FAILED',
            'total_elapsed_seconds', 'stopped_at_turn',
          }
        State is also merged into outreach_state/<slug>.json under
        `oracle_deep_runs[]` so future supervisor invocations can see prior runs.
        """
        if follow_up_prompts is None:
            follow_up_prompts = DEFAULT_DEEPENING_PROMPTS
        run_slug = _safe_outreach_slug(slug or todo.slug())
        run_id = f"deep_{run_slug}_{int(time.time())}"
        run_started_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        if not self.is_alive():
            return {
                "todo_id": todo.todo_id, "conversation_id": "", "chatgpt_url": "",
                "turns": [], "final_verdict": "FAILED",
                "total_elapsed_seconds": 0, "stopped_at_turn": 0,
                "run_id": run_id, "run_started_at": run_started_at,
                "latex_path": "", "plain_summary": "",
                "error": f"oracle server unreachable at {self.server_url}",
            }
        turns: list[dict] = []
        conversation_id = ""
        chatgpt_url = ""
        latex_path = ""
        plain_summary = ""
        terminal_latex_error = ""
        stuck_streak = 0
        stop_break = re.compile(stop_breakthrough_re, re.IGNORECASE)
        stop_stuck = re.compile(stop_stuck_re, re.IGNORECASE)
        verdict = "EXHAUSTED"
        total_start = time.time()
        for turn_idx in range(max_turns):
            if turn_idx == 0:
                prompt = initial_prompt
                review = self._submit_turn(initial_prompt, conversation_id="",
                                           todo=todo, timeout=per_turn_timeout)
            else:
                # Rotate through follow-up prompts; cycle if max_turns > prompts
                fup_idx = (turn_idx - 1) % len(follow_up_prompts)
                prompt = follow_up_prompts[fup_idx]
                review = self._submit_turn(prompt, conversation_id=conversation_id,
                                           todo=todo, timeout=per_turn_timeout)
            if not conversation_id and review.conversation_id:
                conversation_id = review.conversation_id
            if review.chatgpt_url:
                chatgpt_url = review.chatgpt_url
            turn_record = {
                "turn": turn_idx,
                "prompt": prompt,
                "response": (review.response_log_path
                             if review.response_log_path else ""),
                "response_chars": review.response_chars,
                "elapsed_seconds": review.elapsed_seconds,
                "task_id": review.task_id,
                "error": review.error or "",
            }
            turns.append(turn_record)
            # Read actual response text (we wrote it to disk; cheaper than passing around)
            try:
                response_text = (Path(review.response_log_path).read_text(encoding="utf-8")
                                 if review.response_log_path else "")
            except Exception:
                response_text = ""
            if review.error:
                verdict = "FAILED"
                break
            if stop_break.search(response_text):
                verdict = "BREAKTHROUGH"
                break
            if stop_stuck.search(response_text):
                stuck_streak += 1
                if stuck_streak >= stuck_streak_threshold:
                    verdict = "STUCK"
                    break
            else:
                stuck_streak = 0
        reasoning_stopped_at_turn = len(turns) - 1
        if verdict == "BREAKTHROUGH" and terminal_prompt:
            terminal_review = self._submit_turn(
                terminal_prompt,
                conversation_id=conversation_id,
                todo=todo,
                timeout=per_turn_timeout,
            )
            if not conversation_id and terminal_review.conversation_id:
                conversation_id = terminal_review.conversation_id
            if terminal_review.chatgpt_url:
                chatgpt_url = terminal_review.chatgpt_url
            turns.append({
                "turn": len(turns),
                "prompt": terminal_prompt,
                "response": (terminal_review.response_log_path
                             if terminal_review.response_log_path else ""),
                "response_chars": terminal_review.response_chars,
                "elapsed_seconds": terminal_review.elapsed_seconds,
                "task_id": terminal_review.task_id,
                "error": terminal_review.error or "",
                "terminal": "WRITE_PAPER_LATEX",
            })
            try:
                terminal_response = (
                    Path(terminal_review.response_log_path).read_text(encoding="utf-8")
                    if terminal_review.response_log_path else ""
                )
            except Exception:
                terminal_response = ""
            if terminal_review.error:
                terminal_latex_error = terminal_review.error
            else:
                latex_body, plain_summary = extract_latex_from_response(terminal_response)
                if latex_body:
                    out_path = _outreach_latex_path(run_slug)
                    out_path.parent.mkdir(parents=True, exist_ok=True)
                    out_path.write_text(latex_body, encoding="utf-8")
                    latex_path = str(out_path)
                else:
                    terminal_latex_error = (
                        "terminal response did not contain a fenced latex block "
                        "or bare \\documentclass document"
                    )
        total_elapsed = int(time.time() - total_start)
        run = {
            "run_id": run_id,
            "todo_id": todo.todo_id,
            "conversation_id": conversation_id,
            "chatgpt_url": chatgpt_url,
            "turns": turns,
            "final_verdict": verdict,
            "total_elapsed_seconds": total_elapsed,
            "stopped_at_turn": reasoning_stopped_at_turn,
            "run_started_at": run_started_at,
            "run_completed_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "max_turns": max_turns,
            "latex_path": latex_path,
            "plain_summary": plain_summary,
            "terminal_prompt_sent": bool(verdict == "BREAKTHROUGH" and terminal_prompt),
            "terminal_latex_error": terminal_latex_error,
        }
        self._merge_deep_run(slug=run_slug, run=run)
        return run

    def _submit_turn(self, prompt: str, *, conversation_id: str,
                     todo: TodoSpec, timeout: int) -> OracleReview:
        """Submit one turn (initial or follow-up) and poll. Returns OracleReview-shaped record."""
        slug = todo.slug()
        task_id = f"deep_{slug}_t{int(time.time() * 1000)}"
        prompt_log = self.logs_dir / f"{task_id}.prompt.txt"
        response_log = self.logs_dir / f"{task_id}.response.txt"
        prompt_log.write_text(prompt, encoding="utf-8")
        is_followup = bool(conversation_id)
        submit_resp = oracle_submit(
            task_id, prompt,
            conversation_id=conversation_id or None,
            is_followup=is_followup,
            tag=f"{todo.todo_id}:deep",
        )
        submitted_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        if "error" in submit_resp:
            return OracleReview(
                todo_id=todo.todo_id, title=todo.title, task_id=task_id,
                conversation_id=conversation_id, chatgpt_url="",
                submitted_at=submitted_at, completed_at=submitted_at,
                elapsed_seconds=0, response_chars=0, response_valid=False,
                verdict="", score="", top_risk="", top_recommendation="",
                response_log_path="", prompt_log_path=str(prompt_log),
                is_followup=is_followup, parent_task_id="",
                error=f"submit error: {submit_resp.get('error')}",
            )
        new_conv = submit_resp.get("conversation_id", conversation_id or "")
        start = time.time()
        response = oracle_poll(task_id, timeout=timeout)
        elapsed = int(time.time() - start)
        completed_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        response_log.write_text(response or "", encoding="utf-8")
        chatgpt_url = ""
        try:
            res_record = http_get(f"{self.server_url}/result/{task_id}", timeout=5)
            chatgpt_url = res_record.get("chatgpt_url", "") if isinstance(res_record, dict) else ""
        except Exception:
            pass
        return OracleReview(
            todo_id=todo.todo_id, title=todo.title, task_id=task_id,
            conversation_id=new_conv, chatgpt_url=chatgpt_url,
            submitted_at=submitted_at, completed_at=completed_at,
            elapsed_seconds=elapsed, response_chars=len(response or ""),
            response_valid=is_outreach_response_valid(response),
            verdict="", score="", top_risk="", top_recommendation="",
            response_log_path=str(response_log), prompt_log_path=str(prompt_log),
            is_followup=is_followup, parent_task_id="",
            error="" if response else "empty response (timeout or extraction failure)",
        )

    def _merge_deep_run(self, *, slug: str, run: dict) -> None:
        path = self.state_dir / f"{slug}.json"
        try:
            state = json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}
        except json.JSONDecodeError:
            state = {}
        runs = state.setdefault("oracle_deep_runs", [])
        if isinstance(runs, list):
            runs.append(run)
        state["latest_oracle_deep_verdict"] = run["final_verdict"]
        state["latest_oracle_deep_turns"] = len(run["turns"])
        state["latest_oracle_deep_at"] = run["run_completed_at"]
        state["latest_oracle_latex_path"] = run.get("latex_path", "")
        state["latest_oracle_plain_summary"] = run.get("plain_summary", "")
        state["latest_oracle_terminal_latex_error"] = run.get("terminal_latex_error", "")
        history = state.setdefault("action_history", [])
        if isinstance(history, list):
            history.append({
                "timestamp": run["run_completed_at"],
                "stage": "B-oracle-deep",
                "round": len(runs),
                "action": "oracle deep reasoning loop",
                "detail": (f"verdict={run['final_verdict']} turns={len(run['turns'])} "
                           f"elapsed={run['total_elapsed_seconds']}s "
                           f"conv={run.get('conversation_id','')[:12]} "
                           f"latex={bool(run.get('latex_path'))}"),
            })
        path.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n",
                        encoding="utf-8")

    def retry(self, *, task_id: str = "", conversation_id: str = "",
              timeout: int = DEFAULT_TIMEOUT) -> Optional[OracleReview]:
        """Re-extract a previously-failed review without resubmitting the prompt.

        Server queues a re-extract task (or repeat-prompt if conversation_url
        not yet known). Userscript picks it up, navigates to the existing chat,
        skips prompt entry, reads the latest assistant message, posts result.

        Returns the new OracleReview or None on submit failure.
        """
        if not self.is_alive():
            return None
        try:
            resp = http_post(
                f"{self.server_url}/retry",
                {"task_id": task_id, "conversation_id": conversation_id},
                timeout=10,
            )
        except Exception as exc:  # noqa: BLE001
            print(f"[oracle] retry submit failed: {exc}", file=sys.stderr)
            return None
        if "error" in resp:
            print(f"[oracle] retry error: {resp.get('error')}", file=sys.stderr)
            return None
        new_task_id = resp.get("task_id", "")
        conv_id = resp.get("conversation_id", "")
        mode = resp.get("mode", "?")
        if not new_task_id:
            return None
        print(f"[oracle] retry queued ({mode}) task={new_task_id} conv={conv_id[:12]}; "
              f"polling up to {timeout}s")
        start = time.time()
        response = oracle_poll(new_task_id, timeout=timeout)
        elapsed = int(time.time() - start)
        completed_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        prompt_log = self.logs_dir / f"{new_task_id}.prompt.txt"
        response_log = self.logs_dir / f"{new_task_id}.response.txt"
        prompt_log.write_text(f"[retry mode={mode} task_id={new_task_id} conv={conv_id}]",
                              encoding="utf-8")
        response_log.write_text(response or "", encoding="utf-8")
        valid = is_outreach_response_valid(response)
        verdict_fields = parse_oracle_verdict(response) if valid else {
            "verdict": "", "score": "", "top_risk": "", "top_recommendation": "",
        }
        chatgpt_url = ""
        try:
            res_record = http_get(f"{self.server_url}/result/{new_task_id}", timeout=5)
            chatgpt_url = res_record.get("chatgpt_url", "") if isinstance(res_record, dict) else ""
        except Exception:
            pass
        review = OracleReview(
            todo_id="retry", title=f"retry of {task_id or conv_id}",
            task_id=new_task_id, conversation_id=conv_id, chatgpt_url=chatgpt_url,
            submitted_at=completed_at, completed_at=completed_at,
            elapsed_seconds=elapsed, response_chars=len(response or ""),
            response_valid=valid,
            verdict=verdict_fields["verdict"], score=verdict_fields["score"],
            top_risk=verdict_fields["top_risk"],
            top_recommendation=verdict_fields["top_recommendation"],
            response_log_path=str(response_log), prompt_log_path=str(prompt_log),
            is_followup=True, parent_task_id=task_id,
            error="" if response else "empty response (timeout or extraction failure)",
        )
        if conv_id:
            slug_guess = conv_id
            try:
                self._merge_into_state(slug=slug_guess, review=review)
            except Exception:
                pass
        return review

    def _merge_into_state(self, *, slug: str, review: OracleReview) -> None:
        """Append the review to outreach_state/<slug>.json without clobbering."""
        path = self.state_dir / f"{slug}.json"
        try:
            state = json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}
        except json.JSONDecodeError:
            state = {}
        oracle_log = state.setdefault("oracle_reviews", [])
        if isinstance(oracle_log, list):
            oracle_log.append(review.to_dict())
        # Convenience top-level for the latest review
        state["latest_oracle_verdict"] = review.verdict
        state["latest_oracle_score"] = review.score
        state["latest_oracle_at"] = review.completed_at
        if review.conversation_id:
            state["oracle_conversation_id"] = review.conversation_id
        if review.chatgpt_url:
            state["oracle_chatgpt_url"] = review.chatgpt_url
        # Append to action_history if dispatch seeded one
        history = state.setdefault("action_history", [])
        if isinstance(history, list):
            stage_label = "B-oracle-deepen" if review.is_followup else "B-oracle"
            history.append({
                "timestamp": review.completed_at,
                "stage": stage_label,
                "round": 0,
                "action": "oracle review" if not review.is_followup else "oracle deepen",
                "detail": (f"verdict={review.verdict} score={review.score} "
                           f"chars={review.response_chars} elapsed={review.elapsed_seconds}s "
                           f"valid={review.response_valid} "
                           f"conv={review.conversation_id[:12]}"),
            })
        path.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n",
                        encoding="utf-8")


# Default rotating follow-up prompts. Generative, not narrowly templated, so
# ChatGPT chooses the right depth. Tuned to push for concrete math content
# rather than meta-commentary.
DEFAULT_DEEPENING_PROMPTS: list[str] = [
    "Continue. Take the most promising thread from your previous turn and push one full level deeper. Show concrete calculations, not summaries. If you reach an obstacle, name it precisely and propose ONE specific bypass attempt.",
    "Find the weakest link in what you just argued. Try to break it. Construct a small finite counterexample if you can, or precisely identify the unproven gap.",
    "Pick the most concrete sub-claim you've made and formalize it as a precise lemma with explicit hypotheses. Then attempt a complete proof, calculation, or detailed proof sketch.",
    "Test your current line of attack on a small concrete example. Do the actual arithmetic. Do the prediction and the verification match? If not, what does the discrepancy tell you?",
    "Step back. Are you attacking the right sub-problem? Is there a different angle (algebraic / combinatorial / probabilistic / generating-function) that might be cheaper? If yes, sketch it; if no, justify why your current angle is the best.",
    "Where are you most stuck right now? Name the precise obstacle in one sentence. Then propose ONE concrete experiment or computation that would reveal whether the obstacle is real.",
    "Survey your work so far. List in 5 bullets: (1) what is rigorously proved, (2) what is plausibly true with sketch, (3) what is still open, (4) the next single most informative experiment, (5) the most likely failure mode.",
    "Try a completely different angle now: pretend you've never seen the problem before. Re-derive your strongest result from scratch. Did you arrive at the same conclusion? If your re-derivation differs, which is correct?",
    "Build an explicit small computational test that would either confirm your strongest current claim or break it. Specify exact parameter ranges, expected output, and how you'd interpret the result.",
    "If after all this you still cannot make further progress, write 'STUCK' on its own line and give a final summary of where the next person should pick up. Otherwise continue with the deepest open thread.",
]


class _PromptHolder:
    """Internal: lets `deep_reasoning` reuse `review`-style submit logic with raw prompt."""
    def __init__(self, prompt: str):
        self._prompt = prompt


# ---------------------------------------------------------------------------
# Paper digest (Round 1 input — what we have, what we can do)
# ---------------------------------------------------------------------------


_MAIN_PAPER_DIR = REPO_ROOT / "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence"
_LEAN_OMEGA_DIR = REPO_ROOT / "lean4/Omega"
CODEX_BIN = Path("/opt/homebrew/bin/codex")

ORACLE_OUTREACH_BACKFLOW_LANGUAGE_POLICY = """BACKFLOW_LANGUAGE_POLICY for oracle-authored outreach papers:
- The standalone outreach paper must be written entirely in English.
- Remove Chinese prose and Chinese punctuation from title, abstract, section headings,
  theorem names, captions, tables, bibliography notes, and comments.
- Keep mathematical notation unchanged unless a LaTeX error requires a minimal fix.
- Do not translate or rewrite a theorem into a different mathematical claim.
"""


def _has_cjk(text: str) -> bool:
    return bool(re.search(r"[\u3400-\u9fff]", text))


def build_outreach_paper_polish_prompt(latex_path: Path) -> str:
    canonical_main = _MAIN_PAPER_DIR / "main.tex"
    return f"""You are Codex in EDITOR/POLISHER mode for the Omega community-outreach oracle pipeline.

Oracle, not Codex, authored the LaTeX paper. Your job is to polish the existing file in place, not to synthesize a new paper from transcripts.

Edit exactly this file:
{latex_path}

Canonical structure reference:
{canonical_main}

Tasks:
1. Read the existing oracle-authored LaTeX at the edit path. If it is missing or empty, stop with an error.
2. Preserve the mathematical content, theorem statements, and proof strategy unless you find a concrete LaTeX or citation defect.
3. Normalize the standalone paper structure to match the canonical paper conventions where practical: clean preamble, title/author/date, abstract before introduction, numbered theorem environments, coherent section ordering, and references at the end.
4. Polish bibliography entries in-place: replace vague references with concrete arXiv IDs, journal names, volumes, years, and URLs when the source text already identifies them. Do not invent citations.
5. Enforce the language policy below.
6. Do not create a replacement outline. Do not discard oracle-authored proofs. Do not commit or push.

{ORACLE_OUTREACH_BACKFLOW_LANGUAGE_POLICY}

After editing, leave the result as a single self-contained LaTeX document at the same path.
"""


def generate_outreach_paper(
    latex_path: Path | str,
    *,
    codex_bin: Path | str = CODEX_BIN,
    timeout: int = 3600,
) -> Path:
    """Polish an oracle-authored outreach paper in place using Codex CLI.

    This intentionally does not generate a paper from transcripts. The input
    must already be the oracle-saved main.tex produced by the terminal
    WRITE_PAPER_LATEX turn.
    """
    path = Path(latex_path)
    if not path.exists():
        raise FileNotFoundError(f"oracle-authored LaTeX not found: {path}")
    original = path.read_text(encoding="utf-8")
    if not original.strip():
        raise ValueError(f"oracle-authored LaTeX is empty: {path}")
    if r"\documentclass" not in original:
        raise ValueError(f"oracle-authored LaTeX lacks \\documentclass: {path}")

    codex = Path(codex_bin)
    if not codex.exists():
        raise FileNotFoundError(f"codex CLI not found at {codex}")

    prompt = build_outreach_paper_polish_prompt(path.resolve())
    result = subprocess.run(
        [
            str(codex),
            "exec",
            "--dangerously-bypass-approvals-and-sandbox",
            "-C",
            str(REPO_ROOT),
            prompt,
        ],
        capture_output=True,
        text=True,
        timeout=timeout,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    if result.returncode != 0:
        detail = (result.stderr or result.stdout or "").strip()
        raise RuntimeError(f"codex polish failed with rc={result.returncode}: {detail[:1200]}")

    polished = path.read_text(encoding="utf-8")
    if not polished.strip():
        raise ValueError(f"codex polish left LaTeX empty: {path}")
    if r"\documentclass" not in polished:
        raise ValueError(f"codex polish removed \\documentclass: {path}")
    if _has_cjk(polished):
        raise ValueError(f"codex polish did not enforce English/no-Chinese policy: {path}")
    return path


def build_paper_digest(
    *,
    paper_dir: Path = _MAIN_PAPER_DIR,
    lean_dir: Path = _LEAN_OMEGA_DIR,
    extra_papers_glob: Optional[Iterable[str]] = None,
    git_log_count: int = 30,
) -> str:
    """Compose a text digest of the Omega project's actual capabilities.

    Round-1 oracle uses this to judge which open problems we can really solve.
    The digest lists:
      - Main paper directory + body-section structure
      - Lean module map (top-level subdirs + file counts)
      - Recent git commits (proof of what's been built lately)
      - PROGRAM_BOARD.md status line for the main paper, if available

    Kept text-only and bounded to ~25K chars so it fits in one ChatGPT prompt.
    """
    parts: list[str] = []
    parts.append("# Omega Project capability digest")
    parts.append(f"Generated: {datetime.now(timezone.utc).isoformat(timespec='seconds')}")
    parts.append("")
    parts.append("## Main paper")
    parts.append(f"Directory: `{paper_dir.relative_to(REPO_ROOT)}`")
    main_tex = paper_dir / "main.tex"
    if main_tex.exists():
        head = main_tex.read_text(encoding="utf-8", errors="replace").splitlines()[:80]
        title = next((l for l in head if r"\title" in l or r"\Title" in l), "(title not found)")
        parts.append(f"Title line: {title.strip()[:200]}")
    body_root = paper_dir / "sections" / "body"
    if body_root.exists():
        parts.append("Body sections (subdir → tex file count):")
        for sub in sorted(body_root.iterdir()):
            if sub.is_dir():
                n = len(list(sub.rglob("*.tex")))
                parts.append(f"  - {sub.name}: {n} tex files")
    appendix_root = paper_dir / "sections" / "appendix"
    if appendix_root.exists():
        parts.append("Appendix sections (subdir → tex file count):")
        for sub in sorted(appendix_root.iterdir()):
            if sub.is_dir():
                n = len(list(sub.rglob("*.tex")))
                parts.append(f"  - {sub.name}: {n} tex files")
    parts.append("")
    parts.append("## Lean 4 library (lean4/Omega/)")
    if lean_dir.exists():
        for sub in sorted(lean_dir.iterdir()):
            if sub.is_dir():
                lean_files = list(sub.rglob("*.lean"))
                if lean_files:
                    parts.append(f"  - Omega/{sub.name}/  ({len(lean_files)} lean files)")
        parts.append(f"Total lean files under Omega/: {len(list(lean_dir.rglob('*.lean')))}")
    parts.append("")
    parts.append("## Recent commits (last "+ str(git_log_count) + ", evidence of active capabilities)")
    try:
        import subprocess as _sub
        log = _sub.run(
            ["git", "log", "--oneline", f"-{git_log_count}"],
            cwd=REPO_ROOT, capture_output=True, text=True, timeout=10,
        )
        for line in log.stdout.splitlines():
            parts.append(f"  {line[:180]}")
    except Exception as exc:  # noqa: BLE001
        parts.append(f"  (git log unavailable: {exc})")
    program_board = REPO_ROOT / "papers/publication/PROGRAM_BOARD.md"
    if program_board.exists():
        parts.append("")
        parts.append("## PROGRAM_BOARD.md (paper portfolio status; first 40 lines)")
        for line in program_board.read_text(encoding="utf-8").splitlines()[:40]:
            parts.append(f"  {line}")
    text = "\n".join(parts)
    return text[:30000]  # safety bound


def build_candidates_block(todos: dict[str, TodoSpec]) -> str:
    """Render board TODOs as a compact block oracle can rank.

    Includes only fresh-ish candidates (skips ones flagged closed/overtaken
    in their status field). Truncates verbose fields to keep prompt bounded.
    """
    parts = ["## Candidate open problems (from RESEARCH_BOARD.md)"]
    parts.append("(Skipped if status field already says 'closed' / 'overtaken'.)")
    parts.append("")
    skipped: list[str] = []
    rendered = 0
    for tid in sorted(todos.keys(), key=lambda x: int(x.split("-")[1])):
        t = todos[tid]
        s = (t.status or "").lower()
        if "closed" in s or "overtaken" in s or "drop" in s or "handoff to lean4" in s:
            skipped.append(t.todo_id)
            continue
        parts.append(f"### {t.todo_id} · {t.title}")
        parts.append(f"- Source: {t.source}")
        parts.append(f"- Type: {t.type_}")
        parts.append(f"- Untouched evidence: {t.untouched}")
        parts.append(f"- Omega fit (board): {t.fit_score}/10")
        parts.append(f"- Topic value (board): {t.topic_score}/10")
        parts.append(f"- Effort: {t.effort}  Risk: {t.risk}")
        if t.statement:
            parts.append(f"- Problem statement: {t.statement[:600]}")
        if t.prior:
            parts.append(f"- Prior (board): {t.prior[:400]}")
        if t.omega_fit_detail:
            parts.append(f"- Claimed Omega fit detail: {t.omega_fit_detail[:300]}")
        parts.append("")
        rendered += 1
    parts.append(f"(Skipped {len(skipped)} as already-closed: {', '.join(skipped)})")
    parts.append(f"(Rendered {rendered} live candidates.)")
    return "\n".join(parts)[:30000]


_DISCOVERY_PROMPT_TEMPLATE = """You are an independent senior reviewer. The Omega Project asks you to do a CAPABILITY-AWARE scope check before we commit any worker time.

# Round 1: Discovery

You will see two things:

1. The Omega Project's CURRENT capability digest (paper structure, Lean library, recent commits) — this is what we actually have right now.
2. A list of candidate open mathematical problems from our research board.

Your job:

1. SURVEY the live status of each candidate (literature, AI activity, registry state). FLAG any that are already proved/disproved/solved/substantially advanced — we will drop those.
2. For the survivors, RANK by:
   - Real solvability given Omega's actual capabilities (be honest — "Omega has Pisano period machinery" only matters if Pisano period is the right tool for that problem)
   - Community engagement (active forum, recent paper, named individuals working on it)
   - Publishable value of a partial result if full breakthrough fails
   - First-mover risk (someone else likely to publish first)
3. Pick TOP-3 to deep-reason on, with explicit reasoning per pick.
4. For the TOP-1, draft the SPECIFIC sub-goal that you'd ask oracle to deep-reason on in Round 2 — i.e. one precise mathematical statement we could prove or disprove in 1-3 weeks.

Output structure (be terse, no fluff):

```
## Discarded (literature already closed or overtaken)
- T-NN: <reason in one line>
- ...

## Survivors ranked
1. T-NN · <title> — <2-3 sentences of reasoning>
2. ...

## TOP-3 picks for deep reasoning
- T-NN: <one paragraph: WHY this one, what the publishable contribution looks like>
- T-NN: ...
- T-NN: ...

## TOP-1 deep-reasoning sub-goal
TARGET: T-NN
SUB-GOAL: <one precise mathematical statement, ≤ 3 sentences, including any explicit constants / parameter ranges / lemma names>
WHY-OMEGA-FIT: <one sentence linking to a SPECIFIC Lean module or section>
EXPECTED-PUBLICATION: <forum post / arXiv preprint / paper appendix>
ESTIMATED-DAYS: <integer>
```

Be willing to disagree with the board's claimed scores. Be willing to say all candidates are weak. Do not pad.

---

{paper_digest}

---

{candidates_block}

---

Begin Round 1 now.
"""


def build_discovery_prompt(paper_digest: str, candidates_block: str) -> str:
    return _DISCOVERY_PROMPT_TEMPLATE.format(
        paper_digest=paper_digest,
        candidates_block=candidates_block,
    )


@dataclass
class DiscoveryReport:
    submitted_at: str
    completed_at: str
    elapsed_seconds: int
    response_chars: int
    response_valid: bool
    conversation_id: str
    chatgpt_url: str
    discarded: list[dict[str, str]]   # [{"todo_id", "reason"}]
    ranked: list[dict[str, str]]      # [{"todo_id", "title", "reason"}]
    top_picks: list[dict[str, str]]   # [{"todo_id", "rationale"}]
    top1_subgoal: dict[str, str]      # {"target", "sub_goal", "omega_fit", "publication", "days"}
    response_log_path: str
    prompt_log_path: str
    error: str = ""


def _parse_discovery_response(text: str) -> dict:
    """Best-effort parse of oracle's structured response.

    ChatGPT 5.5 strips markdown # headers in some renderings, so we accept
    bare-line section labels too.
    """
    out: dict = {"discarded": [], "ranked": [], "top_picks": [], "top1_subgoal": {}}
    # Section regex: tolerant of ChatGPT's `Thought for Xm Ys` running into
    # the next header without a newline. We don't require the section name to
    # be at start of line — just look for the literal label in the text and
    # capture until the NEXT section label.
    def _section(label_re: str) -> str:
        pat = re.compile(
            r"(?:#{1,3}\s*)?(?:" + label_re + r")[^\n]*\n(.*?)(?=(?:#{1,3}\s*)?(?:Discarded|Survivors\s+ranked|TOP-?3\s+picks|TOP-?1\s+deep|TOP-?1\s+sub|\Z))",
            re.DOTALL | re.IGNORECASE,
        )
        m = pat.search(text)
        return m.group(1) if m else ""

    # Discarded
    sect = _section(r"Discarded")
    for line in sect.splitlines():
        mm = re.match(r"^[\-*]?\s*(T-\d+)\s*[:\-—]\s*(.+)$", line.strip())
        if mm:
            out["discarded"].append({"todo_id": mm.group(1), "reason": mm.group(2).strip()})

    # Ranked survivors
    sect = _section(r"Survivors\s+ranked")
    for line in sect.splitlines():
        mm = re.match(r"^(?:\d+\.\s*)?(T-\d+)\s*[·\-]\s*(.+?)\s*(?:[:—\-]\s*(.+))?$", line.strip())
        if mm and mm.group(1):
            out["ranked"].append({
                "todo_id": mm.group(1),
                "title": (mm.group(2) or "").strip(),
                "reason": (mm.group(3) or "").strip()[:300],
            })

    # Top-3 picks
    sect = _section(r"TOP-?3\s+picks")
    for chunk in re.split(r"\n[\-*]\s*|\n(?=T-\d+)", "\n" + sect.strip()):
        chunk = chunk.strip()
        if not chunk:
            continue
        mm = re.match(r"^(T-\d+)\s*[:\-]?\s*(.+)$", chunk, re.DOTALL)
        if mm:
            out["top_picks"].append({"todo_id": mm.group(1), "rationale": mm.group(2).strip()[:1500]})

    # Top-1 sub-goal — labels appear bare, not under ## TOP-1 always
    block_pat = re.search(
        r"(?:#{1,3}\s*)?TOP-?1[^\n]*\n(.*?)(?=\Z)",
        text, re.DOTALL | re.IGNORECASE,
    )
    block = block_pat.group(1) if block_pat else text
    for key, label in [
        ("target", r"TARGET\s*:\s*(.+)"),
        ("sub_goal", r"SUB-?GOAL\s*:\s*(.+?)(?=\nWHY|\nEXPECTED|\nESTIMATED|\n\n|\Z)"),
        ("omega_fit", r"WHY-?OMEGA-?FIT\s*:\s*(.+)"),
        ("publication", r"EXPECTED-?PUBLICATION\s*:\s*(.+)"),
        ("days", r"ESTIMATED-?DAYS\s*:\s*(\d+)"),
    ]:
        mm = re.search(label, block, re.DOTALL | re.IGNORECASE)
        if mm:
            val = mm.group(1).strip()
            if key != "sub_goal":
                val = val.splitlines()[0].strip()
            out["top1_subgoal"][key] = val
    return out


def discover_targets(consultant: "OracleConsultant", todos: dict[str, TodoSpec],
                     *, timeout: int = DEFAULT_TIMEOUT,
                     paper_digest: Optional[str] = None) -> DiscoveryReport:
    """Round 1: ask oracle which board TODOs are real, valuable, doable."""
    submitted_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
    if paper_digest is None:
        paper_digest = build_paper_digest()
    candidates = build_candidates_block(todos)
    prompt = build_discovery_prompt(paper_digest, candidates)
    task_id = f"discover_{int(time.time())}"
    prompt_log = consultant.logs_dir / f"{task_id}.prompt.txt"
    response_log = consultant.logs_dir / f"{task_id}.response.txt"
    prompt_log.write_text(prompt, encoding="utf-8")
    if not consultant.is_alive():
        return DiscoveryReport(
            submitted_at=submitted_at, completed_at=submitted_at, elapsed_seconds=0,
            response_chars=0, response_valid=False,
            conversation_id="", chatgpt_url="",
            discarded=[], ranked=[], top_picks=[], top1_subgoal={},
            response_log_path="", prompt_log_path=str(prompt_log),
            error=f"oracle server unreachable at {consultant.server_url}",
        )
    submit_resp = oracle_submit(task_id, prompt, tag="discover")
    if "error" in submit_resp:
        return DiscoveryReport(
            submitted_at=submitted_at, completed_at=submitted_at, elapsed_seconds=0,
            response_chars=0, response_valid=False,
            conversation_id="", chatgpt_url="",
            discarded=[], ranked=[], top_picks=[], top1_subgoal={},
            response_log_path="", prompt_log_path=str(prompt_log),
            error=f"submit error: {submit_resp.get('error')}",
        )
    conv_id = submit_resp.get("conversation_id", "")
    start = time.time()
    response = oracle_poll(task_id, timeout=timeout)
    elapsed = int(time.time() - start)
    completed_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
    response_log.write_text(response or "", encoding="utf-8")
    chatgpt_url = ""
    try:
        rec = http_get(f"{consultant.server_url}/result/{task_id}", timeout=5)
        chatgpt_url = rec.get("chatgpt_url", "") if isinstance(rec, dict) else ""
    except Exception:
        pass
    valid = is_outreach_response_valid(response)
    parsed = _parse_discovery_response(response or "")
    report = DiscoveryReport(
        submitted_at=submitted_at, completed_at=completed_at, elapsed_seconds=elapsed,
        response_chars=len(response or ""), response_valid=valid,
        conversation_id=conv_id, chatgpt_url=chatgpt_url,
        discarded=parsed["discarded"], ranked=parsed["ranked"],
        top_picks=parsed["top_picks"], top1_subgoal=parsed["top1_subgoal"],
        response_log_path=str(response_log), prompt_log_path=str(prompt_log),
        error="" if response else "empty response (timeout or extraction failure)",
    )
    # Persist
    out_dir = consultant.state_dir.parent / "discovery"
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / f"{task_id}.json").write_text(
        json.dumps(asdict(report), ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return report


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _resolve_research_md(todo: TodoSpec) -> Path:
    return TARGETS_DIR / todo.slug() / "research.md"


def _cmd_status() -> int:
    alive = is_server_alive()
    print(f"oracle_server at {ORACLE_SERVER}: {'ALIVE' if alive else 'DOWN'}")
    if alive:
        try:
            data = http_get(f"{ORACLE_SERVER}/status", timeout=5)
            print(json.dumps(data, ensure_ascii=False, indent=2))
        except Exception as exc:  # noqa: BLE001
            print(f"(could not read /status: {exc})")
    return 0 if alive else 1


def _cmd_review(args: argparse.Namespace) -> int:
    todos = parse_board(Path(args.board))
    tid = args.todo_id
    if tid not in todos:
        print(f"unknown TODO {tid}; run --list to inspect", file=sys.stderr)
        return 1
    todo = todos[tid]
    research_md = Path(args.research_md) if args.research_md else _resolve_research_md(todo)
    consultant = OracleConsultant()
    if args.dry_run:
        if not research_md.exists():
            print(f"(dry-run) research.md not found at {research_md}")
            return 1
        prompt = build_review_prompt(todo, research_md.read_text(encoding="utf-8"))
        print(prompt)
        return 0
    review = consultant.review(todo, research_md, timeout=args.timeout)
    print(json.dumps(review.to_dict(), ensure_ascii=False, indent=2))
    return 0 if review.response_valid else 2


def _cli(argv: Iterable[str] | None = None) -> int:
    """Manual smoke-test CLI; supported flow is dispatch_worktree.py --supervise --oracle.

    Subcommands:
        status         probe outreach oracle server
        review T-NN    one-shot review of a TODO's research.md (manual debug)
        deepen T-NN <conv_id>  follow-up into an existing conversation
        dry-run T-NN   print the review prompt without contacting oracle
    """
    parser = argparse.ArgumentParser(
        description="oracle_consultant smoke-test CLI (use dispatch_worktree --supervise --oracle for the supported workflow)"
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    sub.add_parser("status", help="Probe outreach oracle server")

    pr = sub.add_parser("review", help="One-shot review of a TODO's research.md")
    pr.add_argument("todo_id", help="TODO id like T-21")
    pr.add_argument("--research-md", help="Override path to research.md")
    pr.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)
    pr.add_argument("--board", default=str(BOARD_PATH_DEFAULT))
    pr.add_argument("--dry-run", action="store_true",
                    help="Print the prompt and exit; do not contact oracle")
    pr.add_argument("--conversation-id", default=None,
                    help="Continue an existing conversation (Phase 2 multi-turn)")

    pd = sub.add_parser("deepen", help="Follow-up into an existing conversation")
    pd.add_argument("conversation_id")
    pd.add_argument("prompt_file", help="Path to file containing the follow-up prompt")
    pd.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)

    args = parser.parse_args(list(argv) if argv is not None else None)
    if args.cmd == "status":
        return _cmd_status()
    if args.cmd == "review":
        return _cmd_review(args)
    if args.cmd == "deepen":
        consultant = OracleConsultant()
        prompt = Path(args.prompt_file).read_text(encoding="utf-8")
        review = consultant.deepen(args.conversation_id, prompt, timeout=args.timeout)
        print(json.dumps(review.to_dict(), ensure_ascii=False, indent=2))
        return 0 if review.response_valid else 2
    return 0


if __name__ == "__main__":
    sys.exit(_cli())
