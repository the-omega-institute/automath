#!/usr/bin/env python3
"""outreach_board_refill — refill RESEARCH_BOARD via ChatGPT Project oracle.

Triggered by outreach_supervisor on cooldown (default 24h, see
DEFAULT_BOARD_REFILL_HOURS in supervisor). Layer-2 of the architecture
the operator scoped on 2026-05-08:

  Layer 1 (NyxID)         arxiv_watch + lit_staleness                ──┐
                                                                       ▼
  Layer 2 (this script)   ChatGPT Project (oracle deep exploration)   ──┐
                          attached: main.pdf + READMEs                  │
                          → 5-10 candidates                             ▼
  Layer 3 (local CLI)     claude judge dedup vs current RESEARCH_BOARD ──┐
                                                                         ▼
                          atomic append survivors → RESEARCH_BOARD.md

Hard rules:
  - oracle does NOT see current RESEARCH_BOARD (kept "blind" to avoid
    anchoring); dedup happens locally
  - never auto-runs Lean
  - never sends anything externally
  - on missing tab / dead userscript / oracle timeout, logs + retries on
    next cooldown — does not crash the supervisor
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
import urllib.request
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_DIR = SCRIPT_DIR / "outreach_state"
STATUS_PATH = STATE_DIR / "board_refill.status.json"
LOG_DIR = STATE_DIR / "board_refill_logs"
ARXIV_RECENT_PATH = STATE_DIR / "arxiv_recent.txt"
LIT_STALENESS_PATH = STATE_DIR / "lit_staleness_recent.txt"
RESEARCH_BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"
PROMPT_PATH = SCRIPT_DIR / "prompts" / "outreach_board_refill.txt"

ORACLE_SERVER_URL = "http://localhost:8766"

# Operator-set Project URL — once you build a NEW Project, replace this. The
# userscript must already be configured to recognize this tab; if not, the
# oracle call will time out gracefully.
REFILL_PROJECT_URL = (
    "https://chatgpt.com/g/g-p-69fdba181e648191a0eb330852658373-openproblem/project"
)

DEFAULT_TIMEOUT_S = 5400        # 90 min total budget for the oracle call
DEFAULT_POLL_INTERVAL = 30
SIGNAL_TAIL_BYTES = 8000        # cap how much arxiv/lit data we feed in


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _log(msg: str) -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {msg}"
    print(line, flush=True)
    with open(LOG_DIR / "board_refill.log", "a", encoding="utf-8") as f:
        f.write(line + "\n")


def _status_write(payload: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    try:
        STATUS_PATH.write_text(
            json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8"
        )
    except OSError as exc:
        _log(f"status write failed: {exc}")


def _status_noop(reason: str) -> int:
    payload = {"ran_at": _now_iso(), "verdict": "noop", "reason": reason}
    _status_write(payload)
    print(json.dumps(payload, ensure_ascii=False, indent=2))
    return 0


def _read_signal(path: Path, max_bytes: int = SIGNAL_TAIL_BYTES) -> str:
    if not path.exists():
        return ""
    try:
        text = path.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return ""
    if len(text) <= max_bytes:
        return text
    return text[-max_bytes:]


def _http_post(url: str, data: dict, timeout: int = 30) -> dict:
    req = urllib.request.Request(
        url,
        data=json.dumps(data).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"))


def _http_get(url: str, timeout: int = 10) -> dict:
    with urllib.request.urlopen(url, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"))


def _server_alive() -> bool:
    try:
        s = _http_get(f"{ORACLE_SERVER_URL}/status", timeout=3)
        return s.get("port") == 8766
    except Exception:
        return False


# ---------------------------------------------------------------------------
# oracle dispatch
# ---------------------------------------------------------------------------


def _build_prompt() -> str:
    if not PROMPT_PATH.exists():
        raise FileNotFoundError(f"prompt template missing at {PROMPT_PATH}")
    template = PROMPT_PATH.read_text(encoding="utf-8")
    arxiv = _read_signal(ARXIV_RECENT_PATH) or "(no recent arxiv signal — pipeline may be cold)"
    lit = _read_signal(LIT_STALENESS_PATH) or "(no recent lit_staleness signal)"
    # Use plain replace rather than str.format because the template has
    # literal `{` / `}` in its JSON output spec.
    return template.replace("{arxiv_watch_recent}", arxiv).replace("{lit_staleness_recent}", lit)


def _submit_oracle_task(prompt: str) -> str | None:
    """POST /submit and return task_id, or None on failure."""
    if not _server_alive():
        _log("oracle server not alive on :8766 — skipping refill cycle")
        return None
    payload = {
        "prompt": prompt,
        "tag": "outreach-board-refill",
        "project_url": REFILL_PROJECT_URL,
    }
    try:
        resp = _http_post(f"{ORACLE_SERVER_URL}/submit", payload, timeout=15)
    except Exception as exc:
        _log(f"oracle submit failed: {exc}")
        return None
    task_id = resp.get("task_id")
    if not task_id:
        _log(f"oracle submit returned no task_id: {resp}")
        return None
    _log(f"oracle task submitted: {task_id} (conv={resp.get('conversation_id','-')[:12]})")
    return task_id


def _poll_oracle(task_id: str, *, timeout_s: int) -> str | None:
    """Poll /result/<task_id> until response or timeout. Return raw text or None."""
    started = time.time()
    while time.time() - started < timeout_s:
        try:
            r = _http_get(f"{ORACLE_SERVER_URL}/result/{task_id}", timeout=10)
        except Exception:
            time.sleep(DEFAULT_POLL_INTERVAL)
            continue
        if r.get("response"):
            return r["response"]
        time.sleep(DEFAULT_POLL_INTERVAL)
    _log(f"oracle poll timed out after {timeout_s}s for task {task_id}")
    return None


# ---------------------------------------------------------------------------
# parse + dedup
# ---------------------------------------------------------------------------


@dataclass
class Candidate:
    title: str = ""
    source_url: str = ""
    type: str = ""
    statement: str = ""
    untouched_evidence: str = ""
    omega_fit_detail: str = ""
    fit_score: int = 0
    topic_score: int = 0
    effort_estimate_days: int = 0
    risk_level: str = ""
    first_attack_step: str = ""
    rationale: str = ""


def _extract_json_object(text: str) -> dict | None:
    text = (text or "").strip()
    if not text:
        return None
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, re.DOTALL)
    candidate = fence.group(1) if fence else None
    if candidate is None:
        first = text.find("{")
        last = text.rfind("}")
        if first == -1 or last == -1 or last <= first:
            return None
        candidate = text[first : last + 1]
    try:
        return json.loads(candidate)
    except json.JSONDecodeError:
        return None


def _parse_candidates(raw: str) -> list[Candidate]:
    obj = _extract_json_object(raw)
    if not obj or "candidates" not in obj:
        return []
    out: list[Candidate] = []
    for c in obj.get("candidates") or []:
        if not isinstance(c, dict):
            continue
        cand = Candidate()
        for k, v in c.items():
            if hasattr(cand, k):
                try:
                    setattr(cand, k, type(getattr(cand, k))(v) if v is not None else getattr(cand, k))
                except (TypeError, ValueError):
                    setattr(cand, k, v if isinstance(v, type(getattr(cand, k))) else getattr(cand, k))
        if cand.title and cand.statement:
            out.append(cand)
    return out


def _existing_board_titles_and_sources() -> list[tuple[str, str, str]]:
    """Return list of (todo_id, title, source) for current board entries."""
    try:
        sys.path.insert(0, str(SCRIPT_DIR))
        from outreach_board_parser import parse_board  # noqa: PLC0415
        todos = parse_board(RESEARCH_BOARD_PATH)
    except Exception as exc:
        _log(f"could not parse current board for dedup: {exc}")
        return []
    return [(t.todo_id, t.title, t.source) for t in todos.values()]


_DEDUP_PROMPT = """You are deduping a candidate open-problem against a list of existing board entries. Output ONLY one JSON line:

`{{"keep": <bool>, "reason": "<short>"}}`

Drop (keep=false) iff the candidate is semantically the SAME problem as one of the existing entries, OR an obvious near-trivial reformulation, OR a strict subcase already covered. Otherwise keep=true.

# Candidate

Title: {title}
Source: {source}
Type: {ctype}
Statement: {statement}
Omega-fit detail: {omega_fit}

# Existing board entries (id | title | source)

```
{existing}
```
"""


def _dedup_candidate(cand: Candidate, existing: list[tuple[str, str, str]]) -> tuple[bool, str]:
    if not existing:
        return True, "empty board, auto-keep"
    try:
        from outreach_claude_exec import claude_exec  # noqa: PLC0415
    except Exception as exc:
        _log(f"claude_exec import failed in dedup: {exc}")
        return True, f"dedup fallback (claude unavailable: {exc})"
    listing = "\n".join(f"{tid} | {t[:80]} | {s[:80]}" for tid, t, s in existing[:32])
    prompt = _DEDUP_PROMPT.format(
        title=cand.title,
        source=cand.source_url,
        ctype=cand.type,
        statement=cand.statement,
        omega_fit=cand.omega_fit_detail,
        existing=listing,
    )
    ok, stdout, _ = claude_exec(
        prompt,
        timeout=300,
        log_tag=f"refill_dedup_{_now_tag()}",
        log_dir=LOG_DIR,
        repo_root=REPO_ROOT,
    )
    if not ok:
        return True, "dedup claude exec failed; default keep"
    obj = _extract_json_object(stdout)
    if not obj:
        return True, "dedup claude returned non-JSON; default keep"
    return bool(obj.get("keep", True)), str(obj.get("reason", ""))[:200]


# ---------------------------------------------------------------------------
# board append
# ---------------------------------------------------------------------------


def _next_todo_id(existing: list[tuple[str, str, str]]) -> str:
    nums = []
    for tid, _, _ in existing:
        m = re.match(r"^T-(\d+)$", tid)
        if m:
            nums.append(int(m.group(1)))
    n = max(nums) + 1 if nums else 1
    return f"T-{n:02d}"


def _format_candidate_block(todo_id: str, c: Candidate) -> str:
    lines = [
        f"### {todo_id} · {c.title}",
        "",
        "| field | value |",
        "|---|---|",
        f"| Status | Backlog (refill {datetime.now().date().isoformat()}) |",
        f"| Source | {c.source_url} |",
        f"| Type | {c.type or 'unspecified'} |",
        f"| Untouched | {c.untouched_evidence or '?'} |",
        f"| Omega fit | {c.fit_score}/10 |",
        f"| Topic value | {c.topic_score}/10 |",
        f"| Effort est | {c.effort_estimate_days} 天 |",
        f"| Risk | {c.risk_level or 'med'} |",
        "",
        f"**Statement.** {c.statement}",
        "",
        f"**Omega fit detail.** {c.omega_fit_detail}",
        "",
        f"**Attack plan.**\n1. {c.first_attack_step or '(not specified)'}",
        "",
        f"_Refill rationale_: {c.rationale}",
        "",
        "---",
        "",
    ]
    return "\n".join(lines)


def _append_to_board(blocks: list[str]) -> int:
    if not blocks:
        return 0
    if not RESEARCH_BOARD_PATH.exists():
        _log(f"board missing at {RESEARCH_BOARD_PATH}; cannot append")
        return 0
    text = RESEARCH_BOARD_PATH.read_text(encoding="utf-8")
    if not text.endswith("\n"):
        text += "\n"
    text += "\n" + "\n".join(blocks)
    tmp = RESEARCH_BOARD_PATH.with_suffix(".md.tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(RESEARCH_BOARD_PATH)
    return len(blocks)


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--dry-run", action="store_true", help="print prompt + parsed candidates, do not append")
    p.add_argument("--timeout-s", type=int, default=DEFAULT_TIMEOUT_S, help="oracle poll budget")
    args = p.parse_args(argv)

    LOG_DIR.mkdir(parents=True, exist_ok=True)

    if not REFILL_PROJECT_URL:
        return _status_noop("REFILL_PROJECT_URL not configured")
    if not PROMPT_PATH.exists():
        return _status_noop(f"prompt template missing at {PROMPT_PATH.name}")

    try:
        prompt = _build_prompt()
    except FileNotFoundError as exc:
        return _status_noop(str(exc))
    _log(f"built refill prompt ({len(prompt)} chars)")

    if args.dry_run:
        print("=" * 70)
        print("PROMPT (head):")
        print(prompt[:1500])
        print("=" * 70)
        _status_write({"ran_at": _now_iso(), "verdict": "dry_run"})
        return 0

    if not _server_alive():
        return _status_noop("outreach_oracle_server (:8766) not alive — skipping cycle")

    task_id = _submit_oracle_task(prompt)
    if not task_id:
        _status_write({"ran_at": _now_iso(), "verdict": "submit_failed"})
        return 1

    raw = _poll_oracle(task_id, timeout_s=args.timeout_s)
    if not raw:
        _status_write({"ran_at": _now_iso(), "verdict": "oracle_timeout", "task_id": task_id})
        return 1

    # Persist raw response for postmortem.
    raw_path = LOG_DIR / f"refill_response_{_now_tag()}.txt"
    raw_path.write_text(raw, encoding="utf-8")
    _log(f"oracle response saved to {raw_path.name} ({len(raw)} chars)")

    candidates = _parse_candidates(raw)
    _log(f"parsed {len(candidates)} candidates from oracle response")
    if not candidates:
        _status_write({
            "ran_at": _now_iso(), "verdict": "no_candidates_parsed",
            "task_id": task_id, "raw_response_path": str(raw_path),
        })
        return 0

    existing = _existing_board_titles_and_sources()
    survivors: list[Candidate] = []
    drops: list[tuple[str, str]] = []
    for c in candidates:
        keep, reason = _dedup_candidate(c, existing)
        if keep:
            survivors.append(c)
        else:
            drops.append((c.title, reason))
            _log(f"dedup drop: {c.title!r} — {reason}")

    next_id_int = int(re.match(r"T-(\d+)", _next_todo_id(existing)).group(1))
    blocks: list[str] = []
    appended_ids: list[str] = []
    for i, c in enumerate(survivors):
        tid = f"T-{next_id_int + i:02d}"
        blocks.append(_format_candidate_block(tid, c))
        appended_ids.append(tid)

    appended = _append_to_board(blocks) if blocks else 0
    payload = {
        "ran_at": _now_iso(),
        "verdict": "appended" if appended else "all_drops",
        "task_id": task_id,
        "raw_response_path": str(raw_path),
        "candidates_received": len(candidates),
        "appended_ids": appended_ids,
        "drops": drops,
    }
    _status_write(payload)
    print(json.dumps(payload, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
