#!/usr/bin/env python3
"""oracle_consultant.py — outreach pipeline's oracle stage (importable module).

This is NOT a standalone CLI tool the user invokes. It is wired into
`dispatch_worktree.py --supervise --oracle`, which calls `OracleConsultant.review`
after the supervisor analyses a target. Oracle becomes Stage B-third-opinion
inside the existing supervise flow.

Talks to:
  - tools/community-outreach/outreach_oracle_server.py on http://127.0.0.1:8766
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
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import time
import urllib.request
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Iterable, Optional

REPO_ROOT = Path(__file__).resolve().parents[2]
# OUTREACH-SPECIFIC: separate server (port 8766) from the paper-pipeline oracle (8765).
# Multi-turn capable from day 1 via outreach_oracle_server.py.
ORACLE_SERVER = os.environ.get("OUTREACH_ORACLE_SERVER_URL", "http://127.0.0.1:8766")
TARGETS_DIR = REPO_ROOT / "tools/community-outreach/targets"
ORACLE_LOGS_DIR = REPO_ROOT / "tools/community-outreach/logs/oracle"
STATE_DIR = REPO_ROOT / "tools/community-outreach/outreach_state"
COMMUNITY_PROMPTS_DIR = REPO_ROOT / "tools/community-outreach/prompts"
DEFAULT_TIMEOUT = 7200  # 2 hours; ChatGPT Pro thinking can run 60+ min
DEFAULT_POLL_INTERVAL = 30
DEFAULT_ZERO_EXTRACT_CANCEL_S = int(os.environ.get("OUTREACH_ORACLE_ZERO_EXTRACT_CANCEL_S", "7200"))
PRE_ORACLE_WORKUP_REUSE_SECONDS = int(os.environ.get("OUTREACH_PRE_ORACLE_WORKUP_REUSE_SECONDS", "900") or "900")
ORACLE_TRANSPORT_ERROR_RE = re.compile(
    r"^\s*ERROR\b|No assistant output after|re-extract: nothing meaningful|"
    r"Task cancelled by server|empty response",
    re.IGNORECASE,
)
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

# Reuse the zero-dep board parser
sys.path.insert(0, str(Path(__file__).parent))
from outreach_board_parser import parse_board, BOARD_PATH_DEFAULT, TodoSpec  # noqa: E402
from outreach_profile import load_profile  # noqa: E402
from outreach_science_gate import science_contract_block  # noqa: E402

_DISTILL_LOG_DIR = None
_distill_codex_exec = None
_CODEX_EXEC_IMPORT_ERROR = None


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


def _http_get_with_curl(url: str, timeout: int = 10) -> dict:
    proc = subprocess.run(
        ["curl", "-fsS", "--max-time", str(max(1, int(timeout))), url],
        capture_output=True,
        text=True,
        timeout=timeout + 2,
        check=False,
    )
    if proc.returncode != 0:
        stderr = (proc.stderr or "").strip()
        raise RuntimeError(stderr or f"curl exited {proc.returncode}")
    return json.loads(proc.stdout, strict=False)


def is_server_alive(server_url: str = ORACLE_SERVER, *, verbose: bool = False) -> bool:
    try:
        return "queue_length" in http_get(f"{server_url}/status", timeout=5)
    except Exception as exc:  # noqa: BLE001
        urllib_exc = exc
    try:
        return "queue_length" in _http_get_with_curl(f"{server_url}/status", timeout=5)
    except Exception as exc:  # noqa: BLE001
        if verbose:
            print(
                f"[oracle] status check failed at {server_url}: "
                f"urllib={urllib_exc}; curl={exc}",
                file=sys.stderr,
            )
        return False


def oracle_bridge_readiness(server_url: str = ORACLE_SERVER) -> tuple[bool, str, dict]:
    """Return whether the browser bridge can currently accept Oracle work.

    The HTTP server being alive is not sufficient: after a userscript bump the
    server can be reachable while all ChatGPT tabs are still running an older
    script version. Treat that as an operator-refresh health state instead of a
    mathematical transport failure.
    """
    try:
        status = http_get(f"{server_url}/status", timeout=5)
    except Exception as exc:  # noqa: BLE001
        try:
            status = _http_get_with_curl(f"{server_url}/status", timeout=5)
        except Exception as curl_exc:  # noqa: BLE001
            return False, f"server unreachable: urllib={exc}; curl={curl_exc}", {}
    if "queue_length" not in status:
        return False, "server status missing queue_length", status
    required = str(status.get("required_script_version") or "")
    compatible = status.get("compatible_active_poll_agents") or []
    project_active = status.get("project_active_poll_agents") or []
    active = status.get("active_poll_agents") or []
    if not compatible:
        seen_versions: list[str] = []
        for rec in (status.get("recent_agents") or {}).values():
            if not isinstance(rec, dict):
                continue
            metrics = rec.get("metrics") if isinstance(rec.get("metrics"), dict) else {}
            version = str(metrics.get("script_version") or "")
            if version and version not in seen_versions:
                seen_versions.append(version)
        if active:
            detail = (
                f"no compatible Outreach Oracle tab; required={required or '-'} "
                f"seen={','.join(seen_versions) or '-'} active={len(active)}"
            )
        elif project_active:
            detail = (
                f"project tabs are active but not compatible; required={required or '-'} "
                f"seen={','.join(seen_versions) or '-'}"
            )
        else:
            detail = f"no active Outreach Oracle tab; required={required or '-'}"
        return False, detail, status
    return True, "", status


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
            if data.get("status") == "cancelled":
                if progress:
                    print(f"[oracle] cancelled {task_id} after {int(time.time()-start)}s", file=sys.stderr)
                return ""
        except Exception:
            pass
        try:
            status = http_get(f"{ORACLE_SERVER}/status", timeout=5)
            agent_rows = status.get("recent_agents") or {}
            for agent_id, rec in agent_rows.items():
                metrics = rec.get("metrics") or {}
                if metrics.get("task_id") != task_id:
                    continue
                extracted = int(metrics.get("extracted_chars") or 0)
                elapsed_gen = int(metrics.get("elapsed_seconds") or 0)
                generating = bool(metrics.get("generating"))
                generation = metrics.get("generation") if isinstance(metrics.get("generation"), dict) else {}
                if (not generating) and generation.get("post_think") and extracted < 5 and elapsed_gen >= 600:
                    http_post(f"{ORACLE_SERVER}/cancel", {"task_id": task_id}, timeout=10)
                    if progress:
                        print(
                            f"[oracle] auto-cancel {task_id}: agent={agent_id} "
                            f"post-think with only {extracted} extracted chars after {elapsed_gen}s",
                            file=sys.stderr,
                    )
                    return ""
                if (not generating) and extracted == 0 and elapsed_gen >= 900:
                    http_post(f"{ORACLE_SERVER}/cancel", {"task_id": task_id}, timeout=10)
                    if progress:
                        print(
                            f"[oracle] auto-cancel {task_id}: agent={agent_id} "
                            f"idle with 0 extracted chars after {elapsed_gen}s",
                            file=sys.stderr,
                        )
                    return ""
                if generating and extracted == 0 and elapsed_gen >= DEFAULT_ZERO_EXTRACT_CANCEL_S:
                    http_post(f"{ORACLE_SERVER}/cancel", {"task_id": task_id}, timeout=10)
                    if progress:
                        print(
                            f"[oracle] auto-cancel {task_id}: agent={agent_id} "
                            f"generating {elapsed_gen}s with 0 extracted chars",
                            file=sys.stderr,
                        )
                    return ""
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


def is_oracle_transport_error(response: str) -> bool:
    return bool(ORACLE_TRANSPORT_ERROR_RE.search(response or ""))


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
        return is_server_alive(self.server_url, verbose=True)

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
                       max_turns: int = 999,
                       follow_up_prompts: Optional[list[str]] = None,
                       prompt_generator: Callable[[int, str, list[dict], TodoSpec], str] | None = None,
                       per_turn_timeout: int = DEFAULT_TIMEOUT,
                       resume_conversation_id: str = "",
                       # Drop the leading word-boundary entirely on the
                       # all-caps markers — ChatGPT 5.5 Pro frequently emits
                       # "Thought for 39m 33sBREAKTHROUGH:" with no space
                       # between the timestamp and the marker, so any
                       # left-boundary check (\\b or negative-letter
                       # lookbehind) misses the signal. The all-caps tokens
                       # (BREAKTHROUGH, PROVED, Q.E.D.) are not substrings of
                       # any English word, so dropping the left-side
                       # constraint is safe. Right-side \\b still required so
                       # we don't match noise.
                       stop_breakthrough_re: str = r"(?:BREAKTHROUGH|PROVED|Q\.E\.D\.?)\b",
                       stop_stuck_re: str = r"\bSTUCK\b|\bdead end\b|\bcannot proceed\b",
                       stuck_streak_threshold: int = 2,
                       terminal_prompt: str | None = None,
                       slug: str | None = None) -> dict:
        """Drive multi-turn deep reasoning on `todo`.

        Pattern (matches Liam Price-style "keep prodding"):
          turn 0: open conversation with `initial_prompt` (full problem framing),
                  or post it as a follow-up when `resume_conversation_id` is set.
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
            'turns': [ {turn, prompt, prompt_source, response, response_chars, elapsed_seconds, error} ],
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
        pre_oracle_workup: dict = {}
        if _is_board_research_todo(todo):
            pre_oracle_workup = _run_pre_oracle_codex_workup_for_todo(
                todo,
                per_turn_timeout=per_turn_timeout,
            )
            if not pre_oracle_workup.get("ok"):
                run = {
                    "todo_id": todo.todo_id,
                    "conversation_id": resume_conversation_id or "",
                    "chatgpt_url": "",
                    "turns": [],
                    "final_verdict": "FAILED",
                    "total_elapsed_seconds": 0,
                    "stopped_at_turn": 0,
                    "run_id": run_id,
                    "run_started_at": run_started_at,
                    "run_completed_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
                    "latex_path": "",
                    "plain_summary": "",
                    "terminal_latex_error": "",
                    "pre_oracle_codex_workup": pre_oracle_workup,
                    "error": (
                        "pre-Oracle Codex local workup required before Oracle: "
                        f"{pre_oracle_workup.get('error') or pre_oracle_workup.get('reason')}"
                    ),
                }
                self._merge_deep_run(slug=run_slug, run=run)
                return run
        turns: list[dict] = []
        conversation_id = resume_conversation_id or ""
        chatgpt_url = ""
        latex_path = ""
        plain_summary = ""
        terminal_latex_error = ""
        stuck_streak = 0
        no_progress_streak = 0
        stop_break = re.compile(stop_breakthrough_re, re.IGNORECASE)
        stop_stuck = re.compile(stop_stuck_re, re.IGNORECASE)
        verdict = "EXHAUSTED"
        total_start = time.time()
        previous_response_text = ""
        next_followup_override = ""
        profile, _ = load_profile(slug or todo.slug())
        contract_text = science_contract_block(profile)
        patience = 2
        if profile is not None and profile.science_contract is not None:
            patience = profile.science_contract.no_progress_patience_turns
        objective = "\n".join([
            f"Target: {todo.todo_id} {todo.title}",
            "Science contract:",
            contract_text,
            "Board statement:",
            todo.statement or "",
        ])
        for turn_idx in range(max_turns):
            prompt_source = "initial"
            if turn_idx == 0:
                prompt = initial_prompt
                if conversation_id:
                    prompt, prompt_source = _resume_short_prompt(
                        todo,
                        slug=run_slug,
                        prompt_generator=prompt_generator,
                    )
                review = self._submit_turn(prompt, conversation_id=conversation_id,
                                           todo=todo, timeout=per_turn_timeout)
            else:
                # Rotate through follow-up prompts; cycle if max_turns > prompts
                fup_idx = (turn_idx - 1) % len(follow_up_prompts)
                template_prompt = follow_up_prompts[fup_idx]
                prompt = template_prompt
                prompt_source = "template"
                if next_followup_override:
                    prompt = next_followup_override
                    prompt_source = "evaluator"
                    next_followup_override = ""
                elif prompt_generator is not None:
                    try:
                        generated = (prompt_generator(turn_idx, previous_response_text, turns, todo)
                                     or "").strip()
                    except Exception:
                        generated = ""
                    fallback_prompt = DEFAULT_DEEPENING_PROMPTS[
                        (turn_idx - 1) % len(DEFAULT_DEEPENING_PROMPTS)
                    ]
                    if generated == fallback_prompt:
                        prompt = generated
                    elif generated and generated != template_prompt:
                        prompt = generated
                        prompt_source = "codex_driven"
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
                "prompt_source": prompt_source,
            }
            turns.append(turn_record)
            # Read actual response text (we wrote it to disk; cheaper than passing around)
            try:
                response_text = (Path(review.response_log_path).read_text(encoding="utf-8")
                                 if review.response_log_path else "")
            except Exception:
                response_text = ""
            previous_response_text = response_text
            digest_result = _codex_digest_oracle_turn(
                todo,
                response_text,
                response_log_path=review.response_log_path,
            )
            if digest_result.get("materialized_artifacts"):
                turn_record["materialized_artifacts"] = digest_result["materialized_artifacts"]
            if digest_result.get("claim_packet"):
                turn_record["claim_packet"] = digest_result["claim_packet"]
            turn_record["science_gate_after_turn"] = {
                "status": digest_result.get("science_gate_status", ""),
                "missing": digest_result.get("science_gate_missing", []),
                "next_action": digest_result.get("science_gate_next_action", ""),
            }
            if review.error:
                verdict = "FAILED"
                break
            effective_gate_status = str(digest_result.get("science_gate_status") or "").upper()
            effective_gate_missing = list(digest_result.get("science_gate_missing", []) or [])
            if not review.error and not is_oracle_transport_error(response_text):
                local_replay = _run_local_codex_replay_after_oracle(
                    todo,
                    turn_idx=turn_idx,
                    per_turn_timeout=per_turn_timeout,
                )
                turn_record["local_codex_replay"] = local_replay
                if not local_replay.get("ok"):
                    verdict = "FAILED"
                    turn_record["error"] = (
                        "post-oracle local Codex replay failed: "
                        f"{local_replay.get('error') or local_replay.get('reason') or local_replay.get('returncode')}"
                    )
                    break
                refreshed_gate = _science_gate_status_for_todo(todo)
                refreshed_gate_missing = list(refreshed_gate.get("missing", []) or [])
                effective_gate_status = str(refreshed_gate.get("status") or "").upper()
                effective_gate_missing = refreshed_gate_missing
                turn_record["science_gate_after_local_replay"] = {
                    "status": refreshed_gate.get("status", ""),
                    "next_action": refreshed_gate.get("next_action", ""),
                    "missing": refreshed_gate_missing,
                    "next_oracle_question": local_replay.get("next_oracle_question", ""),
                }
                if effective_gate_status in {"WRITEBACK_READY", "CLOSE_TARGET"}:
                    verdict = "BREAKTHROUGH" if effective_gate_status == "WRITEBACK_READY" else "STUCK"
                    turn_record["gate_stop"] = (
                        f"post-Oracle local replay moved deterministic science gate to {effective_gate_status}; "
                        "stop this Oracle batch and hand off to writeback/review gates"
                    )
                    break
                if local_replay.get("next_oracle_question"):
                    next_followup_override = _as_continuation_prompt(str(local_replay["next_oracle_question"]))

            eval_result = codex_evaluate_progress(
                turn_idx,
                response_text,
                turns,
                objective,
                todo=todo,
            )
            turn_record["contribution"] = eval_result.get("contribution", "")
            turn_record["evaluator_verdict"] = eval_result.get("verdict", "")
            turn_record["evaluator_reason"] = eval_result.get("verdict_reason", "")
            generated_next = (eval_result.get("next_question") or "").strip()
            gate_missing = effective_gate_missing or _science_gate_missing_for_todo(todo)
            gate_complete = not gate_missing
            gate_status = effective_gate_status
            if gate_status in {"WRITEBACK_READY", "CLOSE_TARGET"}:
                verdict = "BREAKTHROUGH" if gate_status == "WRITEBACK_READY" else "STUCK"
                turn_record["gate_stop"] = (
                    f"deterministic science gate reached {gate_status}; "
                    "stop this Oracle batch and hand off to local writeback/review gates"
                )
                break
            if stop_break.search(response_text):
                if gate_complete:
                    verdict = "BREAKTHROUGH"
                    break
                turn_record["gate_override"] = "breakthrough text ignored because science gate still has missing evidence"
                if _missing_requires_local_artifact_repair(gate_missing):
                    next_followup_override = _artifact_repair_prompt(todo, gate_missing, last_response=response_text)
                else:
                    missing_block = "\n".join(f"- {m}" for m in gate_missing)
                    next_followup_override = (
                        "Continue from your previous answer in this same conversation; do not restart. "
                        "The repository science gate did not accept the result as closed because these "
                        f"proof/verification gaps remain:\n{missing_block}\n\n"
                        "Do not return FILE blocks unless a concrete file is truly missing. "
                        "Either prove the missing closure step, identify a precise mathematical obstruction, "
                        "or state a bounded closure criterion that would let Codex mark the current result as closed."
                    )
                continue
            if eval_result.get("verdict") == "complete":
                if gate_complete:
                    verdict = "BREAKTHROUGH"
                    break
                turn_record["gate_override"] = "evaluator complete ignored because science gate still has missing evidence"
                if _missing_requires_local_artifact_repair(gate_missing):
                    next_followup_override = _artifact_repair_prompt(todo, gate_missing, last_response=response_text)
                else:
                    missing_block = "\n".join(f"- {m}" for m in gate_missing)
                    next_followup_override = (
                        "Continue from your previous answer in this same conversation; do not restart. "
                        "The local evaluator thought this was complete, but the deterministic science gate "
                        f"still reports proof/closure gaps:\n{missing_block}\n\n"
                        "Resolve those gaps directly: give the missing proof, give a falsifying obstruction, "
                        "or give a precise bounded-result closure statement that is honest and publishable."
                    )
                continue
            if eval_result.get("verdict") == "stuck":
                stuck_streak += 1
            contribution = (eval_result.get("contribution") or "").lower()
            has_progress = any(
                term in contribution
                for term in (
                    "lemma", "proof", "calculation", "construction",
                    "counterexample", "certificate", "bound", "obstruction",
                    "reduction", "new "
                )
            )
            if not has_progress and turn_idx > 0:
                no_progress_streak += 1
            else:
                no_progress_streak = 0
            if no_progress_streak >= patience:
                turn_record["gate_override"] = (
                    f"no substantive progress for {no_progress_streak} consecutive turns; "
                    "forcing strategy shift instead of treating this as a scientific stop"
                )
                next_followup_override = (
                    "You have repeated the same line without lowering the science-contract progress metric. "
                    "Choose exactly one route now: RESCOPE to a smaller publishable lemma/certificate, "
                    "NEW_ATTACK with a different proof or computation strategy and a new progress metric, "
                    "or CLOSE_WITH_OBSTRUCTION by giving a FILE block for "
                    f"`tools/community-outreach/targets/{todo.slug()}/failure_analysis.md` "
                    "that identifies the concrete obstruction. Do not summarize; execute the route."
                )
                no_progress_streak = 0
                continue
            if stop_stuck.search(response_text):
                stuck_streak += 1
                if stuck_streak >= stuck_streak_threshold:
                    verdict = "STUCK"
                    break
            else:
                stuck_streak = 0
            if turn_idx == len(turns) - 1 and generated_next and not next_followup_override:
                turn_record["generated_next_question"] = generated_next
                next_followup_override = generated_next
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
                "prompt_source": "terminal",
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
            "pre_oracle_codex_workup": pre_oracle_workup,
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
        if (not response) or is_oracle_transport_error(response):
            retry_review = self.retry(
                task_id=task_id,
                conversation_id=new_conv,
                timeout=min(timeout, DEFAULT_TIMEOUT),
            )
            if (
                retry_review is not None
                and retry_review.response_log_path
                and retry_review.response_chars >= 500
                and not retry_review.error
            ):
                retry_review.todo_id = todo.todo_id
                retry_review.title = todo.title
                retry_review.parent_task_id = task_id
                return retry_review
            response = ""
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
        state["latest_oracle_deep_conversation_id"] = run.get("conversation_id", "")
        state["latest_oracle_deep_url"] = run.get("chatgpt_url", "")
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


OMEGA_CAPABILITIES_BLURB = (
    "Lean 4 mathlib formalization, ETDS/JFM-grade analytic proofs, "
    "numerical verification scripts, oracle-driven research cycles."
)


def _fallback_deepening_prompt(turn: int) -> str:
    return DEFAULT_DEEPENING_PROMPTS[(turn - 1) % len(DEFAULT_DEEPENING_PROMPTS)]


def _missing_requires_local_artifact_repair(missing: list[str]) -> bool:
    """Return true when the gate is asking for disk artifacts, not proof work."""
    text = "\n".join(str(x).lower() for x in missing or [])
    needles = (
        "referenced local artifact missing",
        "local runnable replay artifact",
        "local runnable reproducer",
        "lacks a local runnable reproducer",
        "replay/formal verification",
        "verifier_command",
        "checker_command",
        "reproduction_command",
        "enumerator_command",
        "script_path",
    )
    return any(needle in text for needle in needles)


def _read_next_oracle_question_for_todo(todo: TodoSpec, *, limit: int = 4000) -> str:
    target_dir = REPO_ROOT / "tools/community-outreach/targets" / todo.slug()
    p = target_dir / "next_oracle_question.md"
    try:
        text = p.read_text(encoding="utf-8", errors="replace").strip()
    except OSError:
        text = ""
    if text:
        return text[:limit]
    workup = ""
    try:
        workup = (target_dir / "codex_workup.md").read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""
    match = re.search(r"(?ims)^##\s+Next\s+Oracle\s+question\s*$\s*(.*?)(?=^##\s+|\Z)", workup)
    if not match:
        return ""
    return match.group(1).strip()[:limit]


def _terminate_process_group(proc: subprocess.Popen, *, grace_seconds: float = 5.0) -> None:
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except (ProcessLookupError, OSError):
        return
    try:
        proc.wait(timeout=grace_seconds)
        return
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except (ProcessLookupError, OSError):
        pass


def _pre_oracle_target_files_recent(slug: str, *, max_age_seconds: int) -> tuple[bool, str]:
    target_dir = TARGETS_DIR / slug
    required = (
        "codex_workup.md",
        "next_oracle_question.md",
        "local_repair_report.md",
    )
    oldest_age = 0.0
    for name in required:
        path = target_dir / name
        try:
            age = time.time() - path.stat().st_mtime
        except OSError:
            return False, f"missing {name}"
        oldest_age = max(oldest_age, age)
    if oldest_age > max_age_seconds:
        return False, f"Codex handoff older than reuse window ({oldest_age:.0f}s > {max_age_seconds}s)"
    return True, ""


def _is_board_research_todo(todo: TodoSpec) -> bool:
    """Return true for RESEARCH_BOARD targets that should use the math harness.

    OracleConsultant.deep_reasoning is also used by operator-curated drafting
    tasks via lightweight TodoSpec-shaped stubs.  Those tasks should still use
    Oracle, but they are not target-local theorem/replay jobs and should not be
    blocked by outreach_local_repair.py requiring a RESEARCH_BOARD row.
    """
    try:
        todos = parse_board(BOARD_PATH_DEFAULT)
    except Exception:
        return False
    board_todo = todos.get(getattr(todo, "todo_id", ""))
    if board_todo is None:
        return False
    try:
        return board_todo.slug() == todo.slug()
    except Exception:
        return False


def _is_concrete_oracle_question(question: str) -> bool:
    q = (question or "").strip()
    if len(q) < 120:
        return False
    lowered = q.lower()
    generic_markers = (
        "continue research",
        "继续研究",
        "do the next step",
        "lower the progress metric",
        "provide metadata",
        "review the board",
        "look into this problem",
        "make progress",
        "find something useful",
    )
    if any(marker in lowered for marker in generic_markers):
        return False
    concrete_markers = (
        "prove",
        "disprove",
        "certificate",
        "construction",
        "counterexample",
        "verifier",
        "exact",
        "bound",
        "obstruction",
        "cnf",
        "lrat",
        "drat",
        "graph",
        "lemma",
        "theorem",
        "compute",
        "enumerate",
        "check",
    )
    return any(marker in lowered for marker in concrete_markers)


def _local_grounding_tokens(text: str) -> set[str]:
    body = text or ""
    lowered = body.lower()
    tokens: set[str] = set()
    patterns = (
        r"tools/community-outreach/targets/[A-Za-z0-9_.\-/]+",
        r"\b[A-Za-z0-9_.\-/]*(?:results\.json|verify[A-Za-z0-9_.-]*\.py|check[A-Za-z0-9_.-]*\.py|oracle_claim_packet_[A-Za-z0-9_.-]*\.md)\b",
        r"\b[A-Za-z0-9_.\-/]+\.(?:json|py|cnf|drat|lrat|rup|g6|graph6|edge|vtx|sage|m)\b",
        r"\b(?:sha-?256|hash)\s*[:= ]\s*[a-f0-9]{6,64}\b",
        r"\bcase[- ]?\d+\b",
        r"\b(?:n|k|m)\s*=\s*\d+\b",
        r"\b(?:\d+)\s+(?:vertices|edges|clauses|variables)\b",
    )
    for pattern in patterns:
        for match in re.findall(pattern, body, flags=re.IGNORECASE):
            token = match if isinstance(match, str) else " ".join(match)
            token = re.sub(r"\s+", " ", token.strip().lower())
            if len(token) >= 4:
                tokens.add(token)
    for phrase in (
        "no local replay",
        "found no",
        "not present",
        "first failed check",
        "missing certificate",
        "missing lemma",
        "missing proof",
        "failed at the first local check",
        "exit 0",
        "exited 0",
        "unsat",
        "sat",
    ):
        if phrase in lowered:
            tokens.add(phrase)
    return tokens


def _extract_markdown_section(text: str, heading: str, *, max_chars: int) -> str:
    """Extract one `## Heading` section from a target-local Codex workup."""
    if not text:
        return ""
    pattern = re.compile(
        r"(?ims)^##\s+"
        + re.escape(heading).replace(r"\ ", r"\s+")
        + r"\s*$"
        + r"(.*?)"
        + r"(?=^##\s+|\Z)"
    )
    match = pattern.search(text)
    if not match:
        return ""
    body = match.group(1).strip()
    if len(body) <= max_chars:
        return body
    return body[: max_chars // 2] + "\n\n...[middle truncated]...\n\n" + body[-max_chars // 2 :]


def _question_is_grounded_in_local_work(question: str, workup: str, slug: str) -> bool:
    q = (question or "").lower()
    if not q.strip():
        return False
    local_body = _extract_markdown_section(workup, "Local evidence checked", max_chars=20000)
    commands_body = _extract_markdown_section(workup, "Commands run", max_chars=20000)
    attempt_body = _extract_markdown_section(workup, "Codex attempt before Oracle", max_chars=20000)
    artifact_body = _extract_markdown_section(workup, "Verifier/artifact status", max_chars=20000)
    obligations_body = _extract_markdown_section(workup, "Proof obligations still open", max_chars=20000)
    evidence = "\n".join([local_body, commands_body, attempt_body, artifact_body, obligations_body])
    tokens = _local_grounding_tokens(evidence)
    tokens.add(slug.lower())
    return any(token and token in q for token in tokens)


def _pre_oracle_codex_handoff_ok(slug: str, *, require_recent: bool = True) -> tuple[bool, str]:
    question = _read_target_next_oracle_question(slug)
    if not question:
        return False, "missing Codex-selected next_oracle_question backed by local trace"
    if not _is_concrete_oracle_question(question):
        return False, "Codex-selected next_oracle_question is generic or metadata-only"
    target_dir = TARGETS_DIR / slug
    try:
        workup = (target_dir / "codex_workup.md").read_text(encoding="utf-8", errors="replace")
    except OSError:
        return False, "missing codex_workup.md"
    ok, reason = _target_workup_local_trace_status(workup)
    if not ok:
        return False, reason
    if not _question_is_grounded_in_local_work(question, workup, slug):
        return False, (
            "Codex-selected next_oracle_question is not grounded in this local workup; "
            "it must reuse a target-local path/artifact, command result, hash, finite "
            "case label, or explicit local failure"
        )
    trace_ok, trace_reason = _local_repair_last_has_codex_command_trace(slug)
    if not trace_ok:
        return False, trace_reason
    if require_recent:
        recent_ok, recent_reason = _pre_oracle_target_files_recent(
            slug,
            max_age_seconds=PRE_ORACLE_WORKUP_REUSE_SECONDS,
        )
        if not recent_ok:
            return False, recent_reason
    return True, ""


def _run_pre_oracle_codex_workup_for_todo(todo: TodoSpec, *, per_turn_timeout: int) -> dict:
    """Oracle-consultant-level preflight before any deep Oracle turn.

    dispatch_worktree and outreach_research_loop normally run the same handoff
    first.  This function is a final safety net for direct/manual callers:
    Oracle must get a Codex-processed local workup, not a raw board card.
    """
    slug = todo.slug()
    ok, reason = _pre_oracle_codex_handoff_ok(slug, require_recent=True)
    if ok:
        return {"ok": True, "slug": slug, "reused_recent": True}
    script = REPO_ROOT / "tools/community-outreach/outreach_local_repair.py"
    if not script.exists():
        return {"ok": False, "slug": slug, "error": f"missing local repair script at {script}"}
    timeout = max(
        120,
        min(int(per_turn_timeout), int(os.environ.get("OUTREACH_PRE_ORACLE_REPLAY_TIMEOUT", "1800") or "1800")),
    )
    log_dir = STATE_DIR / "research_loop_logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    tag = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_path = log_dir / f"oracle_consultant_pre_oracle_local_repair_{todo.todo_id}_{tag}.log"
    cmd = [
        "python3",
        str(script),
        "--todo-id",
        todo.todo_id,
        "--timeout",
        str(timeout),
        "--json",
    ]
    started = time.time()
    with open(log_path, "ab") as logf:
        proc = subprocess.Popen(
            cmd,
            cwd=str(REPO_ROOT),
            stdout=logf,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        try:
            rc = proc.wait(timeout=timeout + 120)
        except subprocess.TimeoutExpired:
            _terminate_process_group(proc)
            rc = 124
            logf.write(f"\nTIMEOUT after {timeout}s; terminated local repair process group\n".encode("utf-8"))
    if rc != 0:
        return {
            "ok": False,
            "slug": slug,
            "returncode": rc,
            "error": f"local repair rc={rc}",
            "log_path": str(log_path.relative_to(REPO_ROOT)),
            "previous_reason": reason,
        }
    ok, reason = _pre_oracle_codex_handoff_ok(slug, require_recent=True)
    if not ok:
        return {
            "ok": False,
            "slug": slug,
            "returncode": rc,
            "error": reason,
            "elapsed_seconds": int(time.time() - started),
            "log_path": str(log_path.relative_to(REPO_ROOT)),
        }
    return {
        "ok": True,
        "slug": slug,
        "returncode": rc,
        "elapsed_seconds": int(time.time() - started),
        "log_path": str(log_path.relative_to(REPO_ROOT)),
    }


def _run_local_codex_replay_after_oracle(
    todo: TodoSpec,
    *,
    turn_idx: int,
    per_turn_timeout: int,
) -> dict:
    """Run the local Codex worker after an Oracle answer and before follow-up.

    The Oracle can suggest proofs, constructions, or certificate plans, but the
    pipeline must not blindly continue the ChatGPT thread. This hook forces the
    local harness to inspect the newly preserved claim packet / materialized
    FILE blocks, run feasible checks, and select the next precise Oracle task.
    """
    script = REPO_ROOT / "tools/community-outreach/outreach_local_repair.py"
    if not script.exists():
        return {"ok": False, "error": f"missing local repair script at {script}"}
    timeout = max(120, min(int(per_turn_timeout), int(os.environ.get("OUTREACH_POST_ORACLE_REPLAY_TIMEOUT", "1800"))))
    cmd = [
        "python3",
        str(script),
        "--todo-id",
        todo.todo_id,
        "--timeout",
        str(timeout),
        "--json",
    ]
    started = time.time()
    stdout_chunks: list[bytes] = []
    stderr_chunks: list[bytes] = []
    timed_out = False
    proc = subprocess.Popen(
        cmd,
        cwd=str(REPO_ROOT),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        stdout_b, stderr_b = proc.communicate(timeout=timeout + 120)
        stdout_chunks.append(stdout_b or b"")
        stderr_chunks.append(stderr_b or b"")
    except subprocess.TimeoutExpired:
        timed_out = True
        _terminate_process_group(proc)
        try:
            stdout_b, stderr_b = proc.communicate(timeout=5)
            stdout_chunks.append(stdout_b or b"")
            stderr_chunks.append(stderr_b or b"")
        except subprocess.TimeoutExpired:
            pass
    stdout = b"".join(stdout_chunks).decode("utf-8", errors="replace")
    stderr = b"".join(stderr_chunks).decode("utf-8", errors="replace")
    if timed_out:
        stderr = (stderr + f"\nTIMEOUT after {timeout}s; terminated local repair process group").strip()
        return {
            "ok": False,
            "todo_id": todo.todo_id,
            "turn": turn_idx,
            "returncode": 124,
            "elapsed_seconds": int(time.time() - started),
            "stdout": _compact_excerpt(stdout, 2000),
            "stderr": _compact_excerpt(stderr, 2000),
        }
    returncode = proc.returncode if proc.returncode is not None else 1
    payload: dict = {}
    if stdout.strip():
        try:
            payload = json.loads(stdout)
        except json.JSONDecodeError:
            payload = {}
    ok = returncode == 0 and bool(payload.get("ok"))
    target_dir = REPO_ROOT / "tools/community-outreach/targets" / todo.slug()
    state_path = target_dir / "local_repair_last.json"
    state: dict = {}
    try:
        state = json.loads(state_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        state = {}
    postcheck = state.get("postcheck") if isinstance(state, dict) else {}
    if not isinstance(postcheck, dict):
        postcheck = {}
    substantive = postcheck.get("substantive_local_work") if isinstance(postcheck, dict) else {}
    trace = postcheck.get("codex_command_trace") if isinstance(postcheck, dict) else {}
    diagnostics = []
    if isinstance(substantive, dict):
        diagnostics.extend(str(x) for x in substantive.get("diagnostics", []) or [])
    if not ok:
        diagnostics.append(str(payload.get("error") or payload.get("returncode") or stderr[:500] or "local repair failed"))
    return {
        "ok": ok,
        "todo_id": todo.todo_id,
        "turn": turn_idx,
        "returncode": returncode,
        "elapsed_seconds": int(time.time() - started),
        "stdout_excerpt": _compact_excerpt(stdout, 2000),
        "stderr_excerpt": _compact_excerpt(stderr, 2000),
        "local_repair_last": str(state_path.relative_to(REPO_ROOT)) if state_path.exists() else "",
        "postcheck_ok": bool(postcheck.get("ok")) if isinstance(postcheck, dict) else False,
        "codex_command_trace_ok": bool(trace.get("ok")) if isinstance(trace, dict) else False,
        "substantive_local_work_ok": bool(substantive.get("ok")) if isinstance(substantive, dict) else False,
        "diagnostics": diagnostics[:8],
        "next_oracle_question": _read_next_oracle_question_for_todo(todo),
    }


def _load_distill_codex_exec() -> bool:
    global _DISTILL_LOG_DIR, _distill_codex_exec, _CODEX_EXEC_IMPORT_ERROR
    if _distill_codex_exec is not None:
        return True
    if _CODEX_EXEC_IMPORT_ERROR is not None:
        return False
    if str(REPO_ROOT) not in sys.path:
        sys.path.insert(0, str(REPO_ROOT))
    try:
        from tools.distillation.distill import LOG_DIR as distill_log_dir  # noqa: PLC0415
        from tools.distillation.distill import codex_exec as distill_codex_exec  # noqa: PLC0415
    except Exception as exc:  # noqa: BLE001
        _CODEX_EXEC_IMPORT_ERROR = exc
        return False
    _DISTILL_LOG_DIR = distill_log_dir
    _distill_codex_exec = distill_codex_exec
    return True


def _compact_excerpt(text: str, limit: int) -> str:
    squashed = re.sub(r"\s+", " ", text or "").strip()
    if len(squashed) <= limit:
        return squashed
    return squashed[: max(0, limit - 3)].rstrip() + "..."


def _turn_response_text(turn: dict) -> str:
    response = str(turn.get("response", "") or "")
    if response:
        try:
            path = Path(response)
            if path.exists() and path.is_file():
                return path.read_text(encoding="utf-8", errors="replace")
        except (OSError, ValueError):
            return response
        except Exception:
            return ""
    return response


def _latest_response_text_for_slug(slug: str, *, state_dir: Path = STATE_DIR) -> str:
    path = state_dir / f"{_safe_outreach_slug(slug)}.json"
    try:
        state = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return ""
    runs = state.get("oracle_deep_runs") or []
    if not isinstance(runs, list):
        return ""
    for run in reversed(runs):
        if not isinstance(run, dict):
            continue
        for turn in reversed(run.get("turns") or []):
            if not isinstance(turn, dict):
                continue
            text = _turn_response_text(turn).strip()
            if text:
                return text
    return ""


def _resume_short_prompt(
    todo: TodoSpec,
    *,
    slug: str,
    prompt_generator: Callable[[int, str, list[dict], TodoSpec], str] | None,
) -> tuple[str, str]:
    next_oracle_question = _read_target_next_oracle_question(slug)
    if next_oracle_question:
        return (
            "\n".join([
                "Continue from the previous answer in this same conversation. Do not restart or restate the whole problem.",
                "Codex just inspected/replayed the local workspace and selected this exact next Oracle task. Answer it directly.",
                "",
                next_oracle_question,
                "",
                "Respect the local facts above. Produce one concrete proof move, certificate, replay artifact, or target-specific obstruction.",
            ]),
            "codex_next_oracle_question",
        )
    last_response = _latest_response_text_for_slug(slug)
    gate_missing = _science_gate_missing_for_todo(todo)
    if gate_missing and last_response and _missing_requires_local_artifact_repair(gate_missing):
        return _artifact_repair_prompt(todo, gate_missing, last_response=last_response), "artifact_repair"
    if prompt_generator is not None and last_response:
        try:
            generated = (prompt_generator(1, last_response, [], todo) or "").strip()
        except Exception:
            generated = ""
        if generated:
            return generated, "codex_resume"
    if gate_missing:
        missing_block = "\n".join(f"- {m}" for m in gate_missing)
        artifact_sentence = (
            "If a file is missing, return a FILE block with exact content."
            if _missing_requires_local_artifact_repair(gate_missing)
            else (
                "These are proof/closure verification gaps, not a request for FILE blocks. "
                "Prove the missing mathematical step, identify the exact obstruction, or state "
                "whether the current result should close as a bounded computational record."
            )
        )
        return (
            "Continue from the previous answer in this same conversation. "
            "Do not restate the whole problem. The repository science gate is still missing:\n"
            f"{missing_block}\n\n"
            f"Produce the next concrete artifact or proof step now. {artifact_sentence}",
            "resume_gate_short",
        )
    return (
        "Continue from the previous answer in this same conversation. Do not restate the whole problem. "
        "Use the last result as context and make the next concrete proof/computation move that lowers the science-contract progress metric.",
        "resume_short",
    )


def _read_target_next_oracle_question(slug: str, *, max_chars: int = 4000) -> str:
    """Read the local Codex-selected next Oracle prompt for a target.

    This is deliberately duplicated here instead of importing dispatch_worktree:
    oracle_consultant is the final prompt-selection layer for resumed ChatGPT
    conversations, so it must not silently fall back to generic gate prompts
    after Codex already produced a concrete local workup.
    """
    target_dir = TARGETS_DIR / slug
    workup = target_dir / "codex_workup.md"
    try:
        workup_text = workup.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""
    if not _target_workup_has_local_trace(workup_text):
        return ""

    match = re.search(r"(?ims)^##\s+Next\s+Oracle\s+question\s*$\s*(.*?)(?=^##\s+|\Z)", workup_text)
    workup_question = match.group(1).strip() if match else ""
    direct = target_dir / "next_oracle_question.md"
    try:
        direct_text = direct.read_text(encoding="utf-8", errors="replace").strip()
    except OSError:
        direct_text = ""
    if direct_text:
        try:
            if workup_question and workup.stat().st_mtime > direct.stat().st_mtime + 300:
                question = workup_question
            else:
                question = direct_text
        except OSError:
            question = direct_text
    else:
        question = workup_question
    if not question:
        return ""
    if len(question) <= max_chars:
        return question
    return question[: max_chars // 2] + "\n\n...[middle truncated]...\n\n" + question[-max_chars // 2 :]


def _target_workup_local_trace_status(text: str) -> tuple[bool, str]:
    """Guard resumed Oracle prompts against metadata-only next questions."""
    stripped = (text or "").strip()
    if len(stripped) < 500:
        return False, "codex_workup.md too short to show local processing"
    lowered = stripped.lower()
    required_sections = (
        "## local evidence checked",
        "## commands run",
        "## codex attempt before oracle",
        "## verifier/artifact status",
        "## proof obligations still open",
        "## next oracle question",
    )
    missing = [section for section in required_sections if section not in lowered]
    if missing:
        return False, "codex_workup.md missing sections: " + ", ".join(missing)
    local_body = _extract_markdown_section(stripped, "Local evidence checked", max_chars=20000)
    commands_body = _extract_markdown_section(stripped, "Commands run", max_chars=20000)
    attempt_body = _extract_markdown_section(stripped, "Codex attempt before Oracle", max_chars=20000)
    artifact_body = _extract_markdown_section(stripped, "Verifier/artifact status", max_chars=20000)
    if len(local_body) < 80:
        return False, "Local evidence checked section too thin to prove target inspection"
    if len(commands_body) < 80:
        return False, "Commands run section too thin to prove local execution"
    if len(attempt_body) < 120:
        return False, "Codex attempt before Oracle section too thin to prove an actual local/proof attempt"
    if len(artifact_body) < 80:
        return False, "Verifier/artifact status section too thin to prove artifact review"
    command_markers = (
        "```",
        "$ ",
        "python3 ",
        "python ",
        "rg ",
        "find ",
        "git status",
        "sed -n",
        "cat ",
        "ls ",
        "date ",
        "lean ",
        "lake ",
        "sage ",
        "magma ",
        "gap ",
        "node ",
        "npm ",
        "pytest",
        "curl ",
        "unzip ",
        "sha256sum",
    )
    if not any(marker in commands_body.lower() for marker in command_markers):
        return False, "Commands run section lacks concrete shell/tool commands"
    inspection_markers = (
        "inspected",
        "searched",
        "found",
        "confirmed",
        "checked",
        "ran",
        "replayed",
        "no oracle claim",
        "missing",
        "absent",
    )
    local_artifact_text = f"{local_body}\n{artifact_body}".lower()
    if not any(marker in local_artifact_text for marker in inspection_markers):
        return False, "local evidence/artifact sections do not describe an actual inspection result"
    if not _text_has_codex_attempt(attempt_body):
        return False, "Codex attempt before Oracle lacks a real attempt/action/outcome on the current mathematical gap"
    trace_markers = (
        "command",
        "ran",
        "checked",
        "verified",
        "passed",
        "failed",
        "missing",
        "not run",
        "no local",
        "no oracle claim",
        "results.json",
        "verifier",
        "artifact",
        "python",
    )
    if not any(marker in lowered for marker in trace_markers):
        return False, "codex_workup.md lacks local command/check/artifact trace"
    return True, ""


def _target_workup_has_local_trace(text: str) -> bool:
    ok, _reason = _target_workup_local_trace_status(text)
    return ok


def _text_has_codex_attempt(text: str) -> bool:
    body = (text or "").strip()
    if len(body) < 120:
        return False
    lowered = body.lower()
    action_markers = (
        "attempted", "tried", "ran", "computed", "checked", "replayed",
        "verified", "constructed", "enumerated", "proved", "reduced",
        "tested", "split", "derived", "bounded", "failed", "blocked",
        "no local replay",
    )
    outcome_markers = (
        "result", "outcome", "therefore", "because", "confirmed", "refuted",
        "mismatch", "counterexample", "obstruction", "blocker", "missing",
        "not present", "timeout", "unsat", "sat", "pass", "fail", "cannot",
        "needs oracle",
    )
    math_or_artifact_markers = (
        "proof", "lemma", "theorem", "bound", "certificate", "construction",
        "verifier", "script", "results.json", "oracle_claim_packet", "cnf",
        "drat", "lrat", "graph", "hash", "sha", "case", "finite",
        "recurrence",
    )
    return (
        any(marker in lowered for marker in action_markers)
        and any(marker in lowered for marker in outcome_markers)
        and any(marker in lowered for marker in math_or_artifact_markers)
    )


def _local_repair_last_has_codex_command_trace(slug: str) -> tuple[bool, str]:
    path = TARGETS_DIR / slug / "local_repair_last.json"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError:
        return False, "missing local_repair_last.json"
    except json.JSONDecodeError as exc:
        return False, f"invalid local_repair_last.json: {exc}"
    if not payload.get("ok"):
        return False, "last local repair did not pass"
    postcheck = payload.get("postcheck") if isinstance(payload, dict) else None
    if not isinstance(postcheck, dict):
        return False, "last local repair missing postcheck"
    trace = postcheck.get("codex_command_trace")
    if not isinstance(trace, dict):
        return False, "last local repair missing Codex command trace"
    if not trace.get("ok"):
        return False, str(trace.get("reason") or "Codex command trace not ok")
    if int(trace.get("target_command_count") or 0) <= 0:
        return False, "Codex command trace has no target-local commands"
    substantive = postcheck.get("substantive_local_work")
    if not isinstance(substantive, dict):
        return False, "last local repair missing substantive local-work check"
    if not substantive.get("ok"):
        diagnostics = substantive.get("diagnostics")
        if isinstance(diagnostics, list) and diagnostics:
            return False, "substantive local-work check failed: " + "; ".join(str(item) for item in diagnostics[:4])
        return False, "substantive local-work check failed"
    return True, ""


def _science_gate_missing_for_todo(todo: TodoSpec) -> list[str]:
    try:
        from outreach_science_gate import evaluate as science_gate_evaluate  # noqa: PLC0415
        verdict = science_gate_evaluate(todo)
    except Exception:
        return []
    return list(getattr(verdict, "missing", []) or [])


def _science_gate_context_for_todo(todo: TodoSpec) -> str:
    try:
        from outreach_science_gate import evaluate as science_gate_evaluate  # noqa: PLC0415
        verdict = science_gate_evaluate(todo)
        data = verdict.to_dict()
    except Exception as exc:  # noqa: BLE001
        return f"science_gate unavailable: {exc}"
    keep = {
        "status": data.get("status", ""),
        "next_action": data.get("next_action", ""),
        "verification_status": data.get("verification_status", ""),
        "closure_status": data.get("closure_status", ""),
        "writeback_ready": data.get("writeback_ready", False),
        "close_ready": data.get("close_ready", False),
        "missing": data.get("missing", []) or [],
        "reasons": data.get("reasons", []) or [],
    }
    return json.dumps(keep, ensure_ascii=False, indent=2)


def _science_gate_status_for_todo(todo: TodoSpec) -> dict:
    try:
        from outreach_science_gate import evaluate as science_gate_evaluate  # noqa: PLC0415
        verdict = science_gate_evaluate(todo)
        data = verdict.to_dict()
    except Exception as exc:  # noqa: BLE001
        return {"error": str(exc), "status": "", "next_action": "", "missing": []}
    return {
        "status": data.get("status", ""),
        "next_action": data.get("next_action", ""),
        "missing": data.get("missing", []) or [],
    }


def _local_harness_context_for_todo(todo: TodoSpec) -> str:
    target_dir = REPO_ROOT / "tools/community-outreach/targets" / todo.slug()
    lines = ["Science gate now:", _science_gate_context_for_todo(todo)]
    for name in (
        "next_oracle_question.md",
        "codex_workup.md",
        "local_repair_report.md",
        "local_repair_last.json",
        "results.json",
    ):
        p = target_dir / name
        if not p.exists() or not p.is_file():
            continue
        try:
            text = p.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        limit = 5000 if name == "codex_workup.md" else 3000
        lines.extend([f"\n{name} excerpt:", _compact_excerpt(text, limit)])
    claim_packets = sorted(
        target_dir.glob("oracle_claim_packet_*.md"),
        key=lambda p: p.stat().st_mtime if p.exists() else 0,
        reverse=True,
    )
    for packet in claim_packets[:1]:
        try:
            text = packet.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        lines.extend([f"\nLatest Oracle claim packet ({packet.name}) excerpt:", _compact_excerpt(text, 3500)])
    py_files = sorted(p.name for p in target_dir.glob("*.py") if p.is_file())
    if py_files:
        lines.append("\nTarget-local runnable scripts: " + ", ".join(py_files[:20]))
    return "\n".join(lines)


def _expected_artifact_paths_for_todo(todo: TodoSpec) -> list[str]:
    paths: list[str] = []
    try:
        profile, _ = load_profile(todo.slug())
    except Exception:
        profile = None
    if profile is not None:
        for value in getattr(profile, "expected_artifacts", []) or []:
            if isinstance(value, str) and value.strip():
                paths.append(value.strip())
        contract = getattr(profile, "science_contract", None)
        terminal = getattr(contract, "terminal_artifact", "") if contract is not None else ""
        if isinstance(terminal, str) and terminal.strip():
            paths.append(terminal.strip())
    for fallback in (
        f"tools/community-outreach/targets/{todo.slug()}/research.md",
        f"tools/community-outreach/targets/{todo.slug()}/results.json",
    ):
        paths.append(fallback)
    deduped: list[str] = []
    seen: set[str] = set()
    for path in paths:
        normalized = path.strip()
        if not normalized or normalized in seen:
            continue
        seen.add(normalized)
        deduped.append(normalized)
    return deduped


def _extract_paths_from_gate_missing(missing: list[str]) -> list[str]:
    """Pull concrete target-local paths out of deterministic gate messages."""
    paths: list[str] = []
    pattern = re.compile(
        r"tools/community-outreach/targets/[A-Za-z0-9_.-]+/[A-Za-z0-9_./-]+"
    )
    for item in missing or []:
        for match in pattern.finditer(str(item)):
            path = match.group(0).rstrip("`'\".,;:)")
            if path and path not in paths:
                paths.append(path)
    return paths


def _fence_language_for_path(path: str) -> str:
    suffix = Path(path).suffix.lower()
    if suffix == ".json":
        return "json"
    if suffix == ".py":
        return "python"
    if suffix == ".csv":
        return "csv"
    if suffix in {".tex", ".latex"}:
        return "latex"
    if suffix in {".md", ".markdown"}:
        return "markdown"
    return "text"


def _artifact_repair_prompt(todo: TodoSpec, missing: list[str], *, last_response: str) -> str:
    missing_block = "\n".join(f"- {m}" for m in missing) or "- unspecified missing evidence"
    artifact_paths = _expected_artifact_paths_for_todo(todo)
    for path in _extract_paths_from_gate_missing(missing):
        if path not in artifact_paths:
            artifact_paths.append(path)
    artifact_block = "\n\n".join(
        f"FILE: {path}\n```{_fence_language_for_path(path)}\n... exact file content ...\n```"
        for path in artifact_paths
    )
    try:
        profile, _ = load_profile(todo.slug())
        contract = science_contract_block(profile)
    except Exception:
        contract = ""
    contract_block = f"\n\nScience contract:\n{contract.strip()}" if contract.strip() else ""
    return f"""Continue in this same conversation from the previous answer; this is not a restart. The previous turn is NOT accepted as complete because the deterministic science gate inspected the repository and found missing disk artifacts:
{missing_block}
{contract_block}

Do not say that files have been created unless you include their exact contents in this reply.

Your task now is to produce the missing reproducible artifact packet for {todo.todo_id} ({todo.title}). Return ONLY target-specific file blocks, one after another. Use these expected paths unless the science contract explicitly requires a different verifier artifact:

{artifact_block}

If a mathematically honest artifact cannot be produced, return exactly one FILE block for `tools/community-outreach/targets/{todo.slug()}/failure_analysis.md` explaining the first unverifiable dependency and why the target must continue or be re-scoped. Do not include prose outside FILE blocks.

Formatting is part of the task. The line immediately after each FILE line must be exactly a fenced-code opener such as ```json, ```markdown, ```python, ```latex, or ```csv. Do not write JSON{{...}}, PythonRun..., csv..., Markdown lists, or prose labels. If the full packet is too long, send only the valid fenced `results.json` block first.

Previous response excerpt:
{_compact_excerpt(last_response, 2500)}
"""


def _extract_file_blocks(text: str) -> list[tuple[str, str]]:
    blocks: list[tuple[str, str]] = []
    raw_file_markers = list(re.finditer(r"(?m)^FILE:\s*(?P<path>[^\n]+)$", text or ""))
    pattern = re.compile(
        r"(?m)^FILE:\s*(?P<path>[^\n]+)\n```(?:[A-Za-z0-9_+.-]+)?\n(?P<body>.*?)\n```",
        re.DOTALL,
    )
    for match in pattern.finditer(text or ""):
        path = match.group("path").strip().strip("`")
        body = match.group("body")
        if path and body.strip():
            blocks.append((path, body.rstrip() + "\n"))
    if raw_file_markers:
        fenced_paths = {rel for rel, _body in blocks}
        blocks.extend(_extract_flattened_file_blocks(text or "", raw_file_markers, fenced_paths))
    if raw_file_markers and not blocks:
        marker_paths = ", ".join(
            (m.group("path") or "").strip() for m in raw_file_markers[:5]
        )
        print(
            "[oracle] ignored malformed FILE blocks without fenced code bodies: "
            f"{marker_paths}",
            file=sys.stderr,
        )
    return blocks


def _extract_flattened_file_blocks(
    text: str,
    markers: list[re.Match[str]],
    fenced_paths: set[str],
) -> list[tuple[str, str]]:
    """Recover safe flattened blocks produced by ChatGPT DOM extraction.

    The userscript can lose fenced-code newlines and return `JSON{...}` after a
    FILE marker. We only recover formats with a deterministic parser. In
    particular, flattened Python is not reconstructed here because missing
    newlines can change semantics; the gate should ask Oracle to resend it.
    """
    recovered: list[tuple[str, str]] = []
    for idx, marker in enumerate(markers):
        path = (marker.group("path") or "").strip().strip("`")
        if not path or path in fenced_paths:
            continue
        start = marker.end()
        end = markers[idx + 1].start() if idx + 1 < len(markers) else len(text)
        body = text[start:end].strip()
        suffix = Path(path).suffix.lower()
        if suffix == ".json":
            parsed = _recover_flattened_json_body(body)
            if parsed:
                recovered.append((path, parsed))
        elif suffix in {".md", ".markdown"}:
            parsed = _recover_flattened_markdown_body(body)
            if parsed:
                recovered.append((path, parsed))
        elif suffix == ".csv":
            parsed = _recover_flattened_csv_body(body)
            if parsed:
                recovered.append((path, parsed))
    return recovered


def _recover_flattened_json_body(body: str) -> str:
    cleaned = body.strip()
    if cleaned.startswith("JSON"):
        cleaned = cleaned[4:].lstrip()
    elif cleaned.startswith("json"):
        cleaned = cleaned[4:].lstrip()
    if not cleaned.startswith("{"):
        first = cleaned.find("{")
        if first < 0:
            return ""
        cleaned = cleaned[first:]
    candidate = _balanced_json_object(cleaned)
    if not candidate:
        return ""
    try:
        data = json.loads(candidate)
    except json.JSONDecodeError as exc:
        print(f"[oracle] flattened JSON block rejected: {exc}", file=sys.stderr)
        return ""
    return json.dumps(data, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def _recover_flattened_markdown_body(body: str) -> str:
    cleaned = body.strip()
    if cleaned.startswith("Markdown"):
        cleaned = cleaned[len("Markdown"):].lstrip()
    elif cleaned.startswith("markdown"):
        cleaned = cleaned[len("markdown"):].lstrip()
    if cleaned.startswith("---"):
        return cleaned.rstrip() + "\n"
    if not cleaned.startswith("#"):
        return ""
    # The DOM extractor can collapse fenced-code newlines, but Markdown prose
    # remains semantically inspectable. Keep the text as-is rather than trying
    # to infer paragraph breaks; science gates only need durable content.
    return cleaned.rstrip() + "\n"


def _balanced_json_object(text: str) -> str:
    depth = 0
    in_string = False
    escaped = False
    for idx, ch in enumerate(text):
        if in_string:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
        elif ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return text[: idx + 1]
    return ""


def _recover_flattened_csv_body(body: str) -> str:
    cleaned = body.strip()
    if cleaned.startswith("csv"):
        cleaned = cleaned[3:].lstrip()
    if not cleaned.startswith("c,state_count"):
        return ""
    payload = cleaned[len("c,state_count"):].strip()
    if not re.fullmatch(r"\d+(?:,\d+)+", payload):
        return ""
    pairs: list[tuple[int, int]] = []
    pos = 0
    c = 0
    while pos < len(payload):
        marker = f"{c},"
        if not payload.startswith(marker, pos):
            return ""
        value_start = pos + len(marker)
        next_marker = f"{c + 1},"
        next_pos = payload.find(next_marker, value_start)
        if next_pos < 0:
            value_text = payload[value_start:]
            pos = len(payload)
        else:
            value_text = payload[value_start:next_pos]
            pos = next_pos
        if not value_text or not value_text.isdigit():
            return ""
        pairs.append((c, int(value_text)))
        c += 1
    if not pairs or pairs[0][0] != 0:
        return ""
    lines = ["c,state_count", *(f"{c},{count}" for c, count in pairs)]
    return "\n".join(lines) + "\n"


def _materialize_file_blocks(text: str) -> list[str]:
    written: list[str] = []
    for rel, body in _extract_file_blocks(text):
        p = Path(rel)
        dest = p if p.is_absolute() else REPO_ROOT / p
        try:
            dest.resolve().relative_to(REPO_ROOT.resolve())
        except ValueError:
            continue
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(body, encoding="utf-8")
        written.append(str(dest.relative_to(REPO_ROOT)))
    return written


def _codex_digest_oracle_turn(
    todo: TodoSpec,
    response_text: str,
    *,
    response_log_path: str = "",
) -> dict:
    """Force a local Codex-side digest after every Oracle deep turn.

    Oracle is used for search/deep reasoning. It is not the owner of repository
    state. This digest gives the deterministic harness a chance to materialize
    safe FILE blocks, preserve meaningful non-FILE claims as target-local claim
    packets, and re-run the science gate before the next prompt is chosen.
    """
    result = {
        "materialized_artifacts": [],
        "claim_packet": "",
        "science_gate_status": "",
        "science_gate_missing": [],
        "science_gate_next_action": "",
    }
    text = response_text or ""
    written = _materialize_file_blocks(text)
    result["materialized_artifacts"] = written

    gate_missing = _science_gate_missing_for_todo(todo)
    if text.strip() and not written and gate_missing and not _is_transport_stub_response(text):
        slug = todo.slug()
        target_dir = REPO_ROOT / "tools/community-outreach/targets" / slug
        target_dir.mkdir(parents=True, exist_ok=True)
        digest = hashlib.sha256(text.encode("utf-8", errors="replace")).hexdigest()[:12]
        packet = target_dir / f"oracle_claim_packet_{digest}.md"
        if not packet.exists():
            packet.write_text(
                "\n".join([
                    f"# Oracle Claim Packet — {todo.todo_id} {todo.title}",
                    "",
                    "This packet preserves an Oracle/ChatGPT response that did not",
                    "materialize verifier artifacts. It is not accepted evidence until",
                    "Codex/local scripts produce independent files and the science gate",
                    "passes.",
                    "",
                    f"- source_response_log: `{response_log_path or '(not logged)'}`",
                    f"- missing_after_turn: {json.dumps(gate_missing, ensure_ascii=False)}",
                    "",
                    "## Oracle Response",
                    "",
                    text.strip(),
                    "",
                ]),
                encoding="utf-8",
            )
        result["claim_packet"] = str(packet.relative_to(REPO_ROOT))

    gate_json = REPO_ROOT / "tools/community-outreach/targets" / todo.slug() / "science_gate.json"
    try:
        proc = subprocess.run(
            [
                "python3",
                str(REPO_ROOT / "tools/community-outreach/outreach_science_gate.py"),
                "--todo-id",
                todo.todo_id,
                "--write-ledger",
                "--json",
            ],
            cwd=str(REPO_ROOT),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=120,
        )
        if proc.returncode == 0 and proc.stdout.strip():
            payload = json.loads(proc.stdout)
            row = payload[0] if isinstance(payload, list) and payload else payload
            if isinstance(row, dict):
                result["science_gate_status"] = row.get("status", "")
                result["science_gate_missing"] = row.get("missing", []) or []
                result["science_gate_next_action"] = row.get("next_action", "")
        elif gate_json.exists():
            row = json.loads(gate_json.read_text(encoding="utf-8"))
            result["science_gate_status"] = row.get("status", "")
            result["science_gate_missing"] = row.get("missing", []) or []
            result["science_gate_next_action"] = row.get("next_action", "")
    except Exception as exc:  # noqa: BLE001
        result["science_gate_error"] = str(exc)
    return result


def _is_transport_stub_response(text: str) -> bool:
    stripped = (text or "").strip()
    if not stripped:
        return True
    lowered = stripped.lower()
    transport_markers = (
        "error: task cancelled by server",
        "error (re-extract):",
        "error: empty response",
        "empty response (timeout or extraction failure)",
        "no assistant output after",
        "re-extract: nothing meaningful",
        "re-extract: empty response",
        "server unreachable",
    )
    if any(lowered.startswith(marker) for marker in transport_markers):
        return True
    return len(stripped) < 80 and "cancelled" in lowered and "server" in lowered


def _prior_turns_summary(all_turns: list[dict], *, limit: int = 2000) -> str:
    parts: list[str] = []
    for idx, turn in enumerate(all_turns):
        turn_no = turn.get("turn", idx)
        prompt = _compact_excerpt(str(turn.get("prompt", "") or ""), 200)
        response = _compact_excerpt(_turn_response_text(turn), 300)
        parts.append(f"T{turn_no} prompt: {prompt} -> response: {response}")
    summary = " | ".join(parts)
    return _compact_excerpt(summary, limit) or "(no prior turns)"


def _read_distill_codex_artifact(log_tag: str, suffix: str) -> str:
    if _DISTILL_LOG_DIR is None:
        return ""
    codex_dir = Path(_DISTILL_LOG_DIR) / "codex"
    matches = sorted(
        codex_dir.glob(f"{log_tag}_*.{suffix}"),
        key=lambda p: p.stat().st_mtime if p.exists() else 0,
        reverse=True,
    )
    if not matches:
        return ""
    try:
        return matches[0].read_text(encoding="utf-8", errors="replace")
    except Exception:
        return ""


def _write_codex_driver_log(
    *,
    log_path: Path,
    log_tag: str,
    prompt: str,
    parsed_output: str,
    error: str = "",
) -> None:
    stdout = _read_distill_codex_artifact(log_tag, "stdout.jsonl")
    stderr = _read_distill_codex_artifact(log_tag, "stderr.txt")
    out_file = _read_distill_codex_artifact(log_tag, "out.txt")
    sections = [
        f"log_tag: {log_tag}",
        f"created_at: {datetime.now(timezone.utc).isoformat(timespec='seconds')}",
        "",
        "=== prompt ===",
        prompt,
        "",
        "=== codex_exec parsed output ===",
        parsed_output,
        "",
        "=== stdout.jsonl ===",
        stdout,
        "",
        "=== stderr.txt ===",
        stderr,
        "",
        "=== output.txt ===",
        out_file,
    ]
    if error:
        sections.extend(["", "=== error ===", error])
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text("\n".join(sections).rstrip() + "\n", encoding="utf-8")


def _normalize_codex_followup(text: str) -> str:
    cleaned = (text or "").strip()
    cleaned = re.sub(r"^```(?:text)?\s*|\s*```$", "", cleaned, flags=re.IGNORECASE).strip()
    cleaned = re.sub(r"(?i)^\s*(?:question|follow-up question)\s*:\s*", "", cleaned)
    cleaned = re.sub(r"\s+", " ", cleaned).strip()
    return cleaned[:1200].strip()


def codex_driven_prompt_generator(turn: int, last_response: str, all_turns: list[dict],
                                   todo: TodoSpec, *, timeout_s: int = 300) -> str:
    """Spawn codex CLI to read transcript + last oracle response, return next deepening prompt.

    Imports tools.distillation.distill.codex_exec — uses its JSONL fallback + process
    tree cleanup. Returns a single-line/short paragraph follow-up question.
    Falls back to DEFAULT_DEEPENING_PROMPTS[(turn-1) % 10] on codex failure/empty/timeout.
    """
    fallback = _fallback_deepening_prompt(turn)
    task_id = f"{_safe_outreach_slug(todo.slug())}_turn{turn}_{int(time.time() * 1000)}"
    log_path = ORACLE_LOGS_DIR / f"codex_driver_{task_id}.txt"
    template_path = COMMUNITY_PROMPTS_DIR / "codex_driver_followup.txt"

    try:
        template = template_path.read_text(encoding="utf-8")
    except Exception as exc:  # noqa: BLE001
        _write_codex_driver_log(
            log_path=log_path,
            log_tag=f"community_followup_{task_id}",
            prompt=f"(failed to load template {template_path})",
            parsed_output="",
            error=str(exc),
        )
        return fallback

    prompt = template.format(
        turn_number=str(turn),
        problem_statement=_compact_excerpt(todo.statement or todo.title or "", 4000),
        prior_turns_summary=_prior_turns_summary(all_turns, limit=2000),
        last_oracle_response=_compact_excerpt(last_response, 6000),
        omega_capabilities=(
            OMEGA_CAPABILITIES_BLURB
            + "\n\nLocal harness context:\n"
            + _local_harness_context_for_todo(todo)
        ),
    )
    log_tag = f"community_followup_{task_id}"

    if not _load_distill_codex_exec():
        _write_codex_driver_log(
            log_path=log_path,
            log_tag=log_tag,
            prompt=prompt,
            parsed_output="",
            error=f"codex_exec import failed: {_CODEX_EXEC_IMPORT_ERROR}",
        )
        return fallback

    try:
        assert _distill_codex_exec is not None
        output = _distill_codex_exec(
            prompt,
            work_dir=REPO_ROOT,
            timeout_seconds=timeout_s,
            log_tag=log_tag,
        )
    except Exception as exc:  # noqa: BLE001
        _write_codex_driver_log(
            log_path=log_path,
            log_tag=log_tag,
            prompt=prompt,
            parsed_output="",
            error=str(exc),
        )
        return fallback

    _write_codex_driver_log(
        log_path=log_path,
        log_tag=log_tag,
        prompt=prompt,
        parsed_output=output,
    )

    followup = _normalize_codex_followup(output)
    if (not followup
        or followup.startswith("(codex-exec-failed")
        or followup.startswith("(start-failed)")
        or followup.startswith("(dry run")):
        return fallback
    return _as_continuation_prompt(followup)


def _as_continuation_prompt(question: str) -> str:
    cleaned = (question or "").strip()
    if not cleaned:
        return cleaned
    if re.search(r"\b(continue|previous|last answer|same conversation|上一|继续)\b", cleaned[:240], re.IGNORECASE):
        return cleaned
    return (
        "Continue from your previous answer in this same conversation; do not restart or restate the whole problem. "
        f"{cleaned}"
    )


def codex_evaluate_progress(
    turn: int,
    last_response: str,
    all_turns: list[dict],
    objective: str,
    *,
    todo: TodoSpec | None = None,
    timeout_s: int = 300,
) -> dict:
    """Spawn codex CLI to (a) summarise the new contribution this Oracle turn
    made, (b) decide complete / continue / stuck against the original objective,
    and (c) propose the next follow-up question if continue.

    Returns a dict with keys: contribution, verdict, verdict_reason,
    next_question. On any failure (codex import, timeout, malformed JSON),
    falls back to verdict='continue', empty contribution, and
    next_question=DEFAULT_DEEPENING_PROMPTS[turn % 10] so the loop survives.

    Designed for use in resume_deep / supervise loops that want
    objective-completion termination instead of a hard turn count, and that
    want per-turn contribution recorded in the session JSON for downstream
    paper composition + audit.
    """
    fallback = {
        "contribution": "",
        "verdict": "continue",
        "verdict_reason": "evaluator failed; loop continues with templated follow-up",
        "next_question": _fallback_deepening_prompt(turn),
    }
    task_id = f"eval_turn{turn}_{int(time.time() * 1000)}"
    log_path = ORACLE_LOGS_DIR / f"codex_evaluator_{task_id}.txt"
    template_path = COMMUNITY_PROMPTS_DIR / "codex_evaluator.txt"

    try:
        template = template_path.read_text(encoding="utf-8")
    except Exception as exc:  # noqa: BLE001
        _write_codex_driver_log(
            log_path=log_path, log_tag=f"evaluator_{task_id}",
            prompt=f"(failed to load template {template_path})",
            parsed_output="", error=str(exc),
        )
        return fallback

    local_context = _local_harness_context_for_todo(todo) if todo is not None else "(target-local harness context unavailable)"
    prompt = template.format(
        objective=_compact_excerpt(objective or "(no explicit objective)", 4000),
        prior_turns_summary=_prior_turns_summary(all_turns, limit=2000),
        last_oracle_response=_compact_excerpt(last_response, 6000),
        omega_capabilities=(
            OMEGA_CAPABILITIES_BLURB
            + "\n\nLocal harness context:\n"
            + local_context
        ),
    )
    log_tag = f"evaluator_{task_id}"

    if not _load_distill_codex_exec():
        _write_codex_driver_log(
            log_path=log_path, log_tag=log_tag, prompt=prompt,
            parsed_output="", error=f"codex_exec import failed: {_CODEX_EXEC_IMPORT_ERROR}",
        )
        return fallback

    try:
        assert _distill_codex_exec is not None
        output = _distill_codex_exec(
            prompt, work_dir=REPO_ROOT,
            timeout_seconds=timeout_s, log_tag=log_tag,
        )
    except Exception as exc:  # noqa: BLE001
        _write_codex_driver_log(
            log_path=log_path, log_tag=log_tag, prompt=prompt,
            parsed_output="", error=str(exc),
        )
        return fallback

    _write_codex_driver_log(
        log_path=log_path, log_tag=log_tag, prompt=prompt, parsed_output=output,
    )

    # Parse the JSON. Codex sometimes wraps output in ```json fences or in
    # surrounding prose; strip those before json.loads.
    cleaned = (output or "").strip()
    if cleaned.startswith("```"):
        # remove leading ```[json]? and trailing ```
        cleaned = re.sub(r"^```(?:json)?\s*", "", cleaned)
        cleaned = re.sub(r"\s*```\s*$", "", cleaned)
    # Find the JSON object — first { to last }
    first_brace = cleaned.find("{")
    last_brace = cleaned.rfind("}")
    if first_brace < 0 or last_brace <= first_brace:
        return fallback
    json_blob = cleaned[first_brace : last_brace + 1]
    try:
        parsed = json.loads(json_blob)
    except json.JSONDecodeError:
        return fallback
    verdict = parsed.get("verdict", "continue")
    if verdict not in ("complete", "continue", "stuck"):
        verdict = "continue"
    next_q = parsed.get("next_question", "") or ""
    if verdict == "continue" and not next_q.strip():
        next_q = _fallback_deepening_prompt(turn)
    return {
        "contribution": (parsed.get("contribution") or "").strip(),
        "verdict": verdict,
        "verdict_reason": (parsed.get("verdict_reason") or "").strip(),
        "next_question": next_q.strip(),
    }


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


_PROGRAM_BOARD_JOURNAL_EXPAND = {
    "ergodic th. dyn. sys.": "Ergodic Theory and Dynamical Systems",
    "etds": "Ergodic Theory and Dynamical Systems",
    "ann. pure appl. logic": "Annals of Pure and Applied Logic",
    "apal": "Annals of Pure and Applied Logic",
    "trans. ams": "Transactions of the American Mathematical Society",
    "j. funct. anal.": "Journal of Functional Analysis",
    "jfa": "Journal of Functional Analysis",
    "j. spectral theory": "Journal of Spectral Theory",
    "dynamical systems": "Ergodic Theory and Dynamical Systems",
    "imrn": "International Mathematics Research Notices",
}


def _normalize_program_board_journal(raw: str) -> str:
    journal = re.sub(r"\*+", "", raw or "").strip().strip("`")
    if not journal or journal == "—":
        return ""
    return _PROGRAM_BOARD_JOURNAL_EXPAND.get(journal.lower(), journal)


def _target_journal_from_program_board(paper_dir: Path, *, repo_root: Path = REPO_ROOT) -> str:
    board = repo_root / "papers/publication/PROGRAM_BOARD.md"
    if not board.exists():
        return ""
    try:
        text = board.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return ""

    slug = paper_dir.name
    slug_norm = re.sub(r"[^a-z0-9]+", "_", slug.lower()).strip("_")
    for line in text.splitlines():
        if "|" not in line or "`" not in line:
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 2:
            continue
        dir_name = cells[0].strip().strip("`")
        dir_norm = re.sub(r"[^a-z0-9]+", "_", dir_name.lower()).strip("_")
        if not dir_norm:
            continue
        if dir_name == slug or dir_norm == slug_norm or dir_norm in slug_norm or slug_norm in dir_norm:
            return _normalize_program_board_journal(cells[1])
    return ""


def _newest_pdf_in_paper_dir(paper_dir: Path) -> Path | None:
    candidates: list[Path] = []
    candidates.extend(p for p in paper_dir.glob("*.pdf") if p.is_file())
    build_dir = paper_dir / "build"
    if build_dir.exists():
        candidates.extend(p for p in build_dir.rglob("*.pdf") if p.is_file())
    if not candidates:
        return None
    return max(candidates, key=lambda p: p.stat().st_mtime)


def _parse_pipeline_stages(stdout: str) -> list[str]:
    seen: list[str] = []
    for match in re.finditer(r"\b(?:STAGE|Stage)\s+([FABCD])\b", stdout or ""):
        stage = match.group(1).upper()
        if stage not in seen:
            seen.append(stage)
    return seen


def _timeout_text(value: object) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def run_paper_pipeline(paper_dir: Path, *,
                       target_journal: str | None = None,
                       repo_root: Path = REPO_ROOT,
                       log_dir: Path | None = None,
                       continuous: bool = False) -> dict:
    """Spawn `python3 tools/chatgpt-oracle/oracle_pipeline.py --paper <paper_dir>`.

    - Pulls target_journal from PROGRAM_BOARD.md if not provided; falls back to
      "arXiv preprint" with ETDS-style profile.
    - Captures stdout/stderr to log_dir/<slug>.{out,err}.log.
    - Returns:
      {"paper_dir": str, "pdf_path": str, "pipeline_log": str,
       "stages_completed": list[str], "exit_code": int, "error": str}
    - Default continuous=False so pipeline stops at first user-gate (no auto-publish).
    - Times out at 6 hours.
    """
    root = Path(repo_root)
    paper_path = Path(paper_dir)
    if not paper_path.is_absolute():
        paper_path = root / paper_path
    slug = _safe_outreach_slug(paper_path.name)
    logs = log_dir or (root / "tools/community-outreach/logs/ship_paper")
    logs.mkdir(parents=True, exist_ok=True)
    out_log = logs / f"{slug}.out.log"
    err_log = logs / f"{slug}.err.log"

    journal = target_journal or _target_journal_from_program_board(paper_path, repo_root=root)
    if not journal:
        journal = "arXiv preprint"

    pipeline_script = root / "tools/chatgpt-oracle/oracle_pipeline.py"
    cmd = [
        "python3",
        str(pipeline_script),
        "--paper",
        str(paper_path),
        "--target-journal",
        journal,
    ]
    if continuous:
        cmd.append("--continuous")
    else:
        cmd.extend(["--stop-after", "A"])

    env = os.environ.copy()
    env.setdefault("ORACLE_PAPER_TIME_BUDGET_HOURS", "6")

    exit_code = 0
    error = ""
    stdout = ""
    stderr = ""
    try:
        completed = subprocess.run(
            cmd,
            cwd=root,
            capture_output=True,
            text=True,
            timeout=6 * 60 * 60,
            encoding="utf-8",
            errors="replace",
            check=False,
            env=env,
        )
        exit_code = completed.returncode
        stdout = completed.stdout or ""
        stderr = completed.stderr or ""
        if completed.returncode != 0:
            detail = (stderr or stdout).strip()
            error = f"oracle_pipeline.py exited rc={completed.returncode}: {detail[:1200]}"
    except subprocess.TimeoutExpired as exc:
        exit_code = -9
        stdout = _timeout_text(exc.stdout)
        stderr = _timeout_text(exc.stderr)
        error = "oracle_pipeline.py timed out after 21600s"
    except Exception as exc:  # noqa: BLE001
        exit_code = -1
        error = str(exc)

    out_log.write_text(stdout, encoding="utf-8")
    err_log.write_text(stderr, encoding="utf-8")

    pdf = _newest_pdf_in_paper_dir(paper_path)
    pdf_path = str(pdf) if pdf else ""
    if not pdf_path:
        missing = "no PDF found in paper_dir or paper_dir/build"
        error = f"{error}; {missing}" if error else missing

    return {
        "paper_dir": str(paper_path),
        "pdf_path": pdf_path,
        "pipeline_log": str(out_log),
        "stages_completed": _parse_pipeline_stages(stdout),
        "exit_code": exit_code,
        "error": error,
    }


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


def build_candidates_block(
    todos: dict[str, TodoSpec],
    *,
    arxiv_hits_by_todo: Optional[dict[str, list[dict]]] = None,
) -> str:
    """Render board TODOs as a compact block oracle can rank.

    Includes only fresh-ish candidates (skips ones flagged closed/overtaken
    in their status field). Truncates verbose fields to keep prompt bounded.

    If `arxiv_hits_by_todo` is supplied (mapping todo_id -> list of paper
    hits from arxiv_watch.scan_board), each candidate gets a
    `Recent arXiv (≤window)` subsection so oracle ranking can factor in
    freshness signal alongside board self-declared status.
    """
    parts = ["## Candidate open problems (from RESEARCH_BOARD.md)"]
    parts.append("(Skipped if status field already says 'closed' / 'overtaken'.)")
    parts.append("")
    skipped: list[str] = []
    rendered = 0
    arxiv_hits_by_todo = arxiv_hits_by_todo or {}
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
        hits = arxiv_hits_by_todo.get(tid) or []
        if hits:
            parts.append(f"- Recent arXiv overlap ({len(hits)} hits, freshness signal):")
            for h in hits[:5]:
                paper = h.get("paper", {}) if isinstance(h, dict) else {}
                title = (paper.get("title") or "").strip()[:100]
                pub = (paper.get("published") or "")[:10]
                arxiv_id = (paper.get("arxiv_id") or "").strip()
                matched = ",".join((h.get("matched_keywords") or [])[:5])
                score = h.get("overlap_score", "?")
                parts.append(
                    f"    - {arxiv_id} ({pub}) score={score} matched=[{matched}] :: {title}"
                )
        parts.append("")
        rendered += 1
    parts.append(f"(Skipped {len(skipped)} as already-closed: {', '.join(skipped)})")
    parts.append(f"(Rendered {rendered} live candidates.)")
    return "\n".join(parts)[:32000]


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


def _arxiv_hits_for_round1(
    todos: dict[str, TodoSpec],
    *,
    since: str = "14d",
    max_results: int = 400,
) -> dict[str, list[dict]]:
    """Run arxiv_watch on the live candidate set, return hits keyed by todo_id.

    Best-effort: returns {} if arxiv_watch is unavailable or fails. Round 1
    discover keeps working even when NyxID / arxiv-api is offline; the oracle
    just sees board self-declared status without freshness signal.
    """
    try:
        import sys as _sys, pathlib as _pl  # noqa: PLC0415
        _sys.path.insert(0, str(_pl.Path(__file__).parent))
        import arxiv_watch  # noqa: PLC0415
    except Exception:  # noqa: BLE001
        return {}
    # Skip closed/overtaken — they won't appear in the prompt anyway, no point
    # querying arxiv for them.
    active = {tid: t for tid, t in todos.items()
              if not any(k in (t.status or "").lower()
                         for k in ("closed", "overtaken", "drop", "handoff to lean4"))}
    if not active:
        return {}
    try:
        since_dt = arxiv_watch._parse_since(since)
        papers = arxiv_watch.fetch_recent_papers(
            categories=arxiv_watch.DEFAULT_CATEGORIES,
            since=since_dt,
            max_results=max_results,
            use_nyxid=True,
        )
        watch_hits = arxiv_watch.scan_board(
            todos=active, papers=papers, min_overlap=2, only_active=False,
        )
    except Exception as exc:  # noqa: BLE001
        print(f"[discover] arxiv_watch failed (non-fatal): {exc}", file=sys.stderr)
        return {}
    by_todo: dict[str, list[dict]] = {}
    for h in watch_hits:
        by_todo.setdefault(h.todo_id, []).append(h.to_dict())
    return by_todo


def discover_targets(consultant: "OracleConsultant", todos: dict[str, TodoSpec],
                     *, timeout: int = DEFAULT_TIMEOUT,
                     paper_digest: Optional[str] = None,
                     arxiv_since: str = "14d") -> DiscoveryReport:
    """Round 1: ask oracle which board TODOs are real, valuable, doable."""
    submitted_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
    if paper_digest is None:
        paper_digest = build_paper_digest()
    arxiv_hits = _arxiv_hits_for_round1(todos, since=arxiv_since)
    if arxiv_hits:
        total_hits = sum(len(v) for v in arxiv_hits.values())
        print(f"[discover] injecting arxiv freshness signal: "
              f"{total_hits} hit(s) across {len(arxiv_hits)} TODO(s)",
              file=sys.stderr)
    candidates = build_candidates_block(todos, arxiv_hits_by_todo=arxiv_hits)
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
