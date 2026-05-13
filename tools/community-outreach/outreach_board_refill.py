#!/usr/bin/env python3
"""outreach_board_refill — refill RESEARCH_BOARD via ChatGPT Project oracle.

Triggered by outreach_supervisor on cooldown (default 24h, see
DEFAULT_BOARD_REFILL_HOURS in supervisor). Layer-2 of the architecture
the operator scoped on 2026-05-08:

  Layer 1 (NyxID)         arxiv_watch + lit_staleness                ──┐
                                                                       ▼
  Layer 2 (this script)   ChatGPT Project (oracle deep exploration)   ──┐
                          attached: main.pdf + READMEs                  │
                          → 3-7 high-impact candidates                   ▼
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
import html
from html.parser import HTMLParser
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
CONTEXT_REFRESH_PATH = STATE_DIR / "context_refresh.json"
X_SIGNAL_PATH = STATE_DIR / "x_openproblem_recent.json"
RESEARCH_BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"
PROMPT_PATH = SCRIPT_DIR / "prompts" / "outreach_board_refill.txt"
OPERATOR_MEMORY_PATH = SCRIPT_DIR / "OPERATOR_MEMORY.md"

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_candidate_inbox import academic_impact_gate  # noqa: E402

ORACLE_SERVER_URL = "http://localhost:8766"

# Operator-set Project URL — once you build a NEW Project, replace this. The
# userscript must already be configured to recognize this tab; if not, the
# oracle call will time out gracefully.
REFILL_PROJECT_URL = (
    "https://chatgpt.com/g/g-p-69fdba181e648191a0eb330852658373-openproblem/project"
)

DEFAULT_TIMEOUT_S = 5400        # 90 min total budget for the oracle call
DEFAULT_POLL_INTERVAL = 30
ZERO_EXTRACT_IDLE_CANCEL_S = 900
ZERO_EXTRACT_GENERATING_CANCEL_S = 1200
SIGNAL_TAIL_BYTES = 8000        # cap how much arxiv/lit data we feed in
SHORT_SIGNAL_BYTES = 1400
SOURCE_FETCH_BYTES = 12000


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


class _VisibleTextParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.parts: list[str] = []
        self.links: list[tuple[str, str]] = []
        self._skip = 0
        self._href: str | None = None
        self._link_text: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag in {"script", "style"}:
            self._skip += 1
            return
        if self._skip:
            return
        if tag in {"p", "div", "h1", "h2", "h3", "li", "td", "th", "br", "tr"}:
            self.parts.append("\n")
        if tag == "a":
            href = dict(attrs).get("href") or ""
            self._href = href
            self._link_text = []

    def handle_endtag(self, tag: str) -> None:
        if tag in {"script", "style"}:
            if self._skip:
                self._skip -= 1
            return
        if self._skip:
            return
        if tag == "a" and self._href:
            label = " ".join(" ".join(self._link_text).split())
            self.links.append((self._href, label))
            self._href = None
            self._link_text = []
        if tag in {"p", "div", "h1", "h2", "h3", "li", "tr"}:
            self.parts.append("\n")

    def handle_data(self, data: str) -> None:
        if self._skip:
            return
        s = " ".join(html.unescape(data).split())
        if not s:
            return
        self.parts.append(s)
        if self._href is not None:
            self._link_text.append(s)


def _visible_text_and_links(raw_html: str) -> tuple[str, list[tuple[str, str]]]:
    parser = _VisibleTextParser()
    try:
        parser.feed(raw_html)
    except Exception:
        pass
    text = "\n".join(
        line.strip()
        for line in "".join(parser.parts).splitlines()
        if line.strip()
    )
    return text, parser.links


def _fetch_public_source(url: str, *, max_bytes: int = SOURCE_FETCH_BYTES) -> dict:
    """Fetch a source page and return a small, deterministic text snapshot."""
    if not url:
        return {"ok": False, "reason": "missing source_url", "url": url}
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": "OmegaOutreach/0.1 source-bounded open-problem check",
            "Accept": "text/html,text/plain;q=0.9,*/*;q=0.5",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=25) as resp:
            status = getattr(resp, "status", 0)
            final_url = resp.geturl()
            content_type = resp.headers.get("content-type", "")
            raw = resp.read(max_bytes * 4).decode("utf-8", errors="replace")
    except Exception as exc:  # noqa: BLE001
        return {"ok": False, "reason": f"fetch failed: {exc}", "url": url}
    if "html" in content_type.lower() or raw.lstrip().startswith("<"):
        text, links = _visible_text_and_links(raw)
    else:
        text, links = raw, []
    text = "\n".join(line for line in text.splitlines() if line.strip())
    not_found = bool(re.search(r"\b(No results found|404 Not Found|Not Found)\b", text, re.I))
    return {
        "ok": bool(status and 200 <= int(status) < 400 and text.strip() and not not_found),
        "status": status,
        "url": url,
        "final_url": final_url,
        "content_type": content_type,
        "reason": "no public problem content found" if not_found else "",
        "text": text[:max_bytes],
        "links": links[:80],
    }


def _problemsilike_source_snapshot(source_url: str, source_id: str = "") -> dict:
    """Bounded adapter for Litt's problemsilike pages.

    `/range/1-end` can be a small public index while individual ids may be
    hidden or absent. If an operator asks for a specific id, verify that exact
    id before asking Oracle to reason from it.
    """
    base = "https://www.problemsilike.com"
    checks: list[str] = []
    if source_id:
        sid = source_id.strip().lstrip("#")
        checks.extend([
            f"{base}/{sid}",
            f"{base}/range/{sid}-{sid}",
            f"{base}/range/{sid}-{sid}/open",
            f"{base}/range/{sid}-{sid}/solved",
        ])
    checks.append(source_url)
    seen: set[str] = set()
    attempts: list[dict] = []
    for url in checks:
        if not url or url in seen:
            continue
        seen.add(url)
        snap = _fetch_public_source(url)
        attempts.append({k: v for k, v in snap.items() if k not in {"text", "links"}})
        if snap.get("ok"):
            text = str(snap.get("text") or "")
            if source_id:
                has_id = bool(re.search(rf"(^|\D)#?{re.escape(source_id.strip().lstrip('#'))}(\D|$)", text))
                link_hits = [
                    (href, label)
                    for href, label in snap.get("links", [])
                    if source_id.strip().lstrip("#") in href or source_id.strip().lstrip("#") in label
                ]
                if not has_id and not link_hits and "range/1-end" in url:
                    continue
            snap["attempts"] = attempts
            return snap
    return {
        "ok": False,
        "url": source_url,
        "source_id": source_id,
        "reason": "requested problemsilike id is not publicly visible from checked URLs",
        "attempts": attempts,
    }


def _source_snapshot(source_url: str = "", source_id: str = "") -> dict:
    if not source_url:
        return {"ok": False, "reason": "no source_url supplied"}
    if "problemsilike.com" in source_url.lower():
        return _problemsilike_source_snapshot(source_url, source_id=source_id)
    return _fetch_public_source(source_url)


def _context_refresh_signal(max_bytes: int = SIGNAL_TAIL_BYTES) -> str:
    if not CONTEXT_REFRESH_PATH.exists():
        return "(no targeted context refresh snapshot yet)"
    try:
        d = json.loads(CONTEXT_REFRESH_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return "(targeted context refresh snapshot unreadable)"
    rows: list[str] = [
        f"generated_at: {d.get('generated_at')}",
        f"scope: {d.get('scope')}",
    ]
    for gh in (d.get("github") or [])[:12]:
        bits = [
            f"{gh.get('repo')} {gh.get('kind')}#{gh.get('number')}",
            f"status={gh.get('status')}",
            f"state={gh.get('state')}",
            f"updated_at={gh.get('updated_at')}",
            f"title={gh.get('title')}",
        ]
        rows.append("- GH " + " | ".join(str(b) for b in bits if b))
    for mail in (d.get("mail") or [])[:12]:
        rows.append(
            "- Mail "
            + f"subject={mail.get('subject')!r} email={mail.get('email')!r} "
            + f"status={mail.get('status')} messages={len(mail.get('messages') or [])}"
        )
    text = "\n".join(rows)
    return text if len(text) <= max_bytes else text[-max_bytes:]


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


def _cancel_oracle_task(task_id: str, *, reason: str) -> None:
    if not task_id:
        return
    try:
        _http_post(f"{ORACLE_SERVER_URL}/cancel", {"task_id": task_id}, timeout=10)
        _log(f"oracle task cancelled: {task_id} ({reason})")
    except Exception as exc:  # noqa: BLE001
        _log(f"oracle task cancel failed for {task_id}: {exc}")


# ---------------------------------------------------------------------------
# oracle dispatch
# ---------------------------------------------------------------------------


def _build_prompt(*, source_url: str = "", source_id: str = "") -> str:
    if source_url:
        snap = _source_snapshot(source_url, source_id=source_id)
        if not snap.get("ok"):
            raise RuntimeError(
                "source unavailable: "
                + json.dumps({k: snap.get(k) for k in ("url", "source_id", "reason", "attempts")}, ensure_ascii=False)
            )
        text = str(snap.get("text") or "")
        return _build_source_focused_prompt(
            source_url=source_url,
            source_id=source_id,
            source_text=text,
            final_url=str(snap.get("final_url") or source_url),
        )
    return _build_compact_prompt()


def _build_compact_prompt() -> str:
    """Short default refill prompt.

    The old 17k prompt repeatedly timed out with zero extracted chars. Keep the
    Oracle task source-discovery oriented and let local gates handle structure,
    dedup, and profile expansion.
    """
    operator_memory = _read_signal(OPERATOR_MEMORY_PATH, max_bytes=SHORT_SIGNAL_BYTES) or "(none)"
    arxiv = _read_signal(ARXIV_RECENT_PATH, max_bytes=SHORT_SIGNAL_BYTES) or "(none)"
    lit = _read_signal(LIT_STALENESS_PATH, max_bytes=SHORT_SIGNAL_BYTES) or "(none)"
    x_signal = _read_signal(X_SIGNAL_PATH, max_bytes=SHORT_SIGNAL_BYTES) or "(none)"
    context = _context_refresh_signal(max_bytes=SHORT_SIGNAL_BYTES)
    return f"""You are the source-discovery oracle for Omega Outreach.

Goal: propose 1-3 high-impact open-problem candidates that an audit-first
AI-for-math pipeline could plausibly attack. Prefer named conjectures,
public problem lists, GitHub/forum/blog/X discussions, verifier gaps, and
classification/extremal/rigidity targets. Do not chase low-impact arXiv
followups. If nothing meets the bar, output {{"candidates":[]}}.

Hard requirements for each candidate:
- public source URL;
- precise mathematical statement;
- why it appears still open or not recently closed;
- concrete first artifact: proof, counterexample, reproducible certificate,
  short note, or forum/registry comment after operator approval;
- first local attack step that Codex can execute;
- success gate before any outreach.

Output ONLY JSON:
{{"candidates":[{{"title":"","source_url":"","type":"DECIDABLE|EXISTENCE|CLASSIFICATION|EXTREMALITY|OBSTRUCTION|RIGIDITY","statement":"","untouched_evidence":"","omega_fit_detail":"","fit_score":0,"topic_score":0,"effort_estimate_days":1,"risk_level":"low|med|high","first_attack_step":"","final_display_form":"","success_gate":"","rationale":""}}]}}

Operator memory:
{operator_memory}

Recent arXiv signal, use only if independently high impact:
{arxiv}

Literature staleness signal:
{lit}

X/open-problem signal:
{x_signal}

Active tracked collaborations/issues/emails to avoid duplicating:
{context}
"""


def _build_source_focused_prompt(*, source_url: str, source_id: str, source_text: str, final_url: str) -> str:
    target_label = f"#{source_id.strip().lstrip('#')}" if source_id else "the supplied source"
    return f"""You are the source-bounded research triage oracle for Omega Outreach.

Source URL: {final_url}
Requested item: {target_label}

Use ONLY the source snapshot below. Decide whether this is a serious open
problem candidate for our audit-first AI-for-math pipeline. If the snapshot
does not contain a precise open problem, output {{"candidates":[]}}.

Output ONLY JSON with at most one candidate:
{{"candidates":[{{"title":"","source_url":"{final_url}","type":"DECIDABLE|EXISTENCE|CLASSIFICATION|EXTREMALITY|OBSTRUCTION|RIGIDITY","statement":"","untouched_evidence":"","omega_fit_detail":"","fit_score":0,"topic_score":0,"effort_estimate_days":1,"risk_level":"low|med|high","first_attack_step":"","final_display_form":"","success_gate":"","rationale":""}}]}}

The candidate must name a concrete theorem/counterexample/certificate target,
not a broad direction. Set final_display_form to a reviewable artifact and
audience. Set success_gate to the exact proof/check required before external
outreach. User approval is always required before sending or posting.

Source snapshot:
{source_text[:SOURCE_FETCH_BYTES]}
"""


def _build_legacy_prompt() -> str:
    if not PROMPT_PATH.exists():
        raise FileNotFoundError(f"prompt template missing at {PROMPT_PATH}")
    template = PROMPT_PATH.read_text(encoding="utf-8")
    arxiv = _read_signal(ARXIV_RECENT_PATH) or "(no recent arxiv signal — pipeline may be cold)"
    lit = _read_signal(LIT_STALENESS_PATH) or "(no recent lit_staleness signal)"
    context = _context_refresh_signal()
    x_signal = _read_signal(X_SIGNAL_PATH) or "(no X open-problem signal snapshot yet)"
    operator_memory = _read_signal(OPERATOR_MEMORY_PATH) or "(operator memory unavailable)"
    # Use plain replace rather than str.format because the template has
    # literal `{` / `}` in its JSON output spec.
    return (
        template
        .replace("{operator_memory}", operator_memory)
        .replace("{arxiv_watch_recent}", arxiv)
        .replace("{lit_staleness_recent}", lit)
        .replace("{targeted_context_refresh}", context)
        .replace("{x_openproblem_recent}", x_signal)
    )


def _submit_oracle_task(prompt: str) -> str | None:
    """POST /submit and return task_id, or None on failure."""
    if not _server_alive():
        _log("oracle server not alive on :8766 — skipping refill cycle")
        return None
    payload = {
        "prompt": prompt,
        "tag": "openproblem-board-refill",
        "project_url": REFILL_PROJECT_URL,
    }
    try:
        resp = _http_post(f"{ORACLE_SERVER_URL}/submit", payload, timeout=15)
    except Exception as exc:
        _log(f"oracle submit failed: {exc}")
        return None
    task_id = resp.get("task_id")
    conv_id = resp.get("conversation_id") or ""
    if not task_id:
        _log(f"oracle submit returned no task_id: {resp}")
        return None
    _log(f"oracle task submitted: {task_id} (conv={conv_id[:12]})")
    return task_id, conv_id


def _submit_followup(prompt: str, conversation_id: str) -> str | None:
    """POST /continue (same conversation, new prompt). Returns task_id."""
    if not _server_alive():
        _log("oracle server not alive — cannot send follow-up")
        return None
    payload = {
        "prompt": prompt,
        "conversation_id": conversation_id,
        "tag": "openproblem-board-refill",
        "project_url": REFILL_PROJECT_URL,
    }
    try:
        resp = _http_post(f"{ORACLE_SERVER_URL}/continue", payload, timeout=15)
    except Exception as exc:
        _log(f"oracle continue failed: {exc}")
        return None
    task_id = resp.get("task_id")
    if not task_id:
        _log(f"oracle continue returned no task_id: {resp}")
        return None
    _log(f"oracle follow-up submitted: {task_id} (conv={conversation_id[:12]})")
    return task_id


def _poll_oracle(task_id: str, *, timeout_s: int) -> str | None:
    """Poll /result/<task_id> until response or timeout. Return raw text or None."""
    started = time.time()
    while time.time() - started < timeout_s:
        try:
            r = _http_get(f"{ORACLE_SERVER_URL}/result/{task_id}", timeout=10)
        except Exception:
            # /result/<task_id> returns 404 while a task is still pending. Keep
            # running the live /status health checks below so stuck browser
            # tabs are cancelled early instead of occupying an Oracle lane
            # until the outer timeout expires.
            r = {}
        else:
            if r.get("status") == "cancelled":
                _log(f"oracle task {task_id} was cancelled")
                return None
            if r.get("response"):
                text = str(r["response"] or "")
                if _is_transport_error(text):
                    _log(f"oracle returned transport error for {task_id}: {text[:180]}")
                    return None
                if len(text.strip()) < 20:
                    _log(f"oracle returned too little content for {task_id}: {text!r}")
                    return None
                return text
        try:
            status = _http_get(f"{ORACLE_SERVER_URL}/status", timeout=5)
            for agent_id, rec in (status.get("recent_agents") or {}).items():
                metrics = rec.get("metrics") or {}
                if metrics.get("task_id") != task_id:
                    continue
                extracted = int(metrics.get("extracted_chars") or 0)
                elapsed = int(metrics.get("elapsed_seconds") or 0)
                generating = bool(metrics.get("generating"))
                generation = metrics.get("generation") if isinstance(metrics.get("generation"), dict) else {}
                if (not generating) and extracted == 0 and elapsed >= ZERO_EXTRACT_IDLE_CANCEL_S:
                    _cancel_oracle_task(
                        task_id,
                        reason=(
                            f"board refill idle with 0 extracted chars after {elapsed}s "
                            f"(agent={agent_id})"
                        ),
                    )
                    return None
                if (
                    generating
                    and extracted == 0
                    and elapsed >= ZERO_EXTRACT_GENERATING_CANCEL_S
                    and generation.get("text_signal")
                ):
                    _cancel_oracle_task(
                        task_id,
                        reason=(
                            f"board refill generating with text signal but 0 extracted chars "
                            f"after {elapsed}s (agent={agent_id})"
                        ),
                    )
                    return None
        except Exception:
            pass
        time.sleep(DEFAULT_POLL_INTERVAL)
    _log(f"oracle poll timed out after {timeout_s}s for task {task_id}")
    _cancel_oracle_task(task_id, reason="board refill poll timeout")
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
    final_display_form: str = ""
    success_gate: str = ""
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


def _is_transport_error(text: str) -> bool:
    return bool(re.match(
        r"\s*ERROR\b|\s*Task cancelled by server|No assistant output after|re-extract: nothing meaningful",
        text or "",
        re.IGNORECASE,
    ))


def _codex_extract_candidates(raw: str, *, round_idx: int) -> list[Candidate]:
    """Use local Codex as the Oracle-output adapter, not as the source.

    The Oracle's job is to search and reason. The local harness owns structure.
    When ChatGPT returns readable candidate prose or malformed JSON, do one
    deterministic adapter pass through Codex so the board refill loop does not
    burn more Oracle turns only for formatting.
    """
    codex = shutil.which("codex") or "/opt/homebrew/bin/codex"
    if not codex or not Path(codex).exists():
        _log("codex candidate adapter unavailable; falling back to oracle follow-up")
        return []
    prompt = f"""You are the local structure adapter for Omega Outreach board refill.

The text below is an Oracle/ChatGPT response to an open-problem discovery prompt.
Your task is NOT to invent candidates. Extract only candidates explicitly present
in the Oracle response. If none are present, output {{"candidates":[]}}.

Output ONLY a JSON object with this exact top-level shape:
{{
  "candidates": [
    {{
      "title": "<short title, <=80 chars>",
      "source_url": "<http(s) URL from the Oracle text>",
      "type": "DECIDABLE|EXISTENCE|CLASSIFICATION|EXTREMALITY|OBSTRUCTION|RIGIDITY",
      "statement": "<one-sentence precise mathematical statement>",
      "untouched_evidence": "<freshness/SOTA/open evidence from the Oracle text>",
      "omega_fit_detail": "<Omega/Automath bridge from the Oracle text>",
      "fit_score": 0,
      "topic_score": 0,
      "effort_estimate_days": 1,
      "risk_level": "low|med|high",
      "first_attack_step": "<first concrete attack step>",
      "final_display_form": "<concrete artifact + audience>",
      "success_gate": "<required proof/check/certificate before any send>",
      "rationale": "<why this is real, doable, and not already taken>"
    }}
  ]
}}

Preserve fit_score/topic_score/effort_estimate_days if the Oracle gave them.
If scores are missing, assign conservative scores from explicit Oracle evidence:
topic_score >= 8 only for named conjectures, famous/open frontier problems,
public verifier/certificate gaps, or high-visibility specialist discussions;
fit_score >= 5 only when the Oracle names a concrete Automath/Omega/certificate
bridge. Reject broad directions, invented items, candidates without a public
source URL, and items whose source/statement/final display are not explicit in
the Oracle response.

# Oracle response

{raw[:24000]}
"""
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    prompt_path = LOG_DIR / f"refill_round{round_idx}_codex_adapter_prompt.txt"
    stdout_path = LOG_DIR / f"refill_round{round_idx}_codex_adapter_stdout.txt"
    prompt_path.write_text(prompt, encoding="utf-8")
    try:
        proc = subprocess.run(
            [codex, "exec", "--json", "--skip-git-repo-check"],
            cwd=str(REPO_ROOT),
            input=prompt,
            capture_output=True,
            text=True,
            timeout=900,
        )
    except Exception as exc:  # noqa: BLE001
        _log(f"codex candidate adapter spawn failed: {exc}")
        return []
    stdout_path.write_text(proc.stdout or "", encoding="utf-8")
    if proc.returncode != 0:
        _log(f"codex candidate adapter rc={proc.returncode}: {(proc.stderr or proc.stdout)[:300]}")
        return []
    candidates = _parse_candidates(proc.stdout)
    _log(f"codex candidate adapter round {round_idx}: extracted {len(candidates)} candidates")
    return candidates


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
    # Normal board refill must not invoke Claude. Conservative lexical overlap
    # is enough for this deterministic pre-board gate; ambiguous candidates
    # remain in inbox/profile judgment rather than being posted directly.
    title_l = cand.title.lower()
    stmt_l = cand.statement.lower()
    for tid, title, source in existing:
        existing_l = f"{title} {source}".lower()
        if title_l and title_l in existing_l:
            return False, f"deterministic title duplicate of {tid}"
        tokens = {t for t in re.findall(r"[a-z0-9_]{4,}", title_l + " " + stmt_l)}
        existing_tokens = {t for t in re.findall(r"[a-z0-9_]{4,}", existing_l)}
        if tokens and len(tokens & existing_tokens) >= max(4, min(8, len(tokens) // 2)):
            return False, f"deterministic near-duplicate token overlap with {tid}"
    return True, "deterministic dedup keep"


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
        f"| Final display | {c.final_display_form or 'TBD — must be specified before run'} |",
        f"| Success gate | {c.success_gate or 'TBD — operator-approved concrete artifact'} |",
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


def _write_candidate_inbox(candidates: list[Candidate], *, source: str = "oracle_board_refill") -> list[str]:
    if not candidates:
        return []
    try:
        from outreach_candidate_inbox import add_candidate  # noqa: PLC0415
    except Exception as exc:
        _log(f"candidate inbox import failed: {exc}")
        return []
    ids: list[str] = []
    for c in candidates:
        row = add_candidate(asdict(c), source=source)
        ids.append(row.get("candidate_id", ""))
    return ids


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--dry-run", action="store_true", help="print prompt + parsed candidates, do not append")
    p.add_argument("--candidate-inbox", action="store_true",
                   help="write surviving candidates to candidate_inbox.jsonl instead of appending RESEARCH_BOARD")
    p.add_argument("--timeout-s", type=int, default=DEFAULT_TIMEOUT_S, help="oracle poll budget")
    p.add_argument("--source-url", default="", help="triage one explicit public source URL")
    p.add_argument("--source-id", default="", help="optional source-local problem id, e.g. 367")
    args = p.parse_args(argv)

    LOG_DIR.mkdir(parents=True, exist_ok=True)

    if not REFILL_PROJECT_URL:
        return _status_noop("REFILL_PROJECT_URL not configured")
    if not PROMPT_PATH.exists():
        return _status_noop(f"prompt template missing at {PROMPT_PATH.name}")

    try:
        prompt = _build_prompt(source_url=args.source_url, source_id=args.source_id)
    except (FileNotFoundError, RuntimeError) as exc:
        payload = {
            "ran_at": _now_iso(),
            "verdict": "source_unavailable" if args.source_url else "noop",
            "source_url": args.source_url,
            "source_id": args.source_id,
            "reason": str(exc),
        }
        if not args.dry_run:
            _status_write(payload)
        _log(f"board refill source unavailable: {exc}")
        print(json.dumps(payload, ensure_ascii=False, indent=2))
        return 0 if args.source_url else 1
    _log(f"built refill prompt ({len(prompt)} chars)")

    if args.dry_run:
        print("=" * 70)
        print("PROMPT (head):")
        print(prompt[:1500])
        print("=" * 70)
        return 0

    if not _server_alive():
        return _status_noop("outreach_oracle_server (:8766) not alive — skipping cycle")

    # ── Multi-round oracle loop with follow-ups ────────────────────────
    # Round 1 sends the full prompt. If parsed candidates are insufficient
    # (< MIN_GOOD_CANDIDATES kept after dedup), we send a follow-up in the
    # same conversation (so the Project context is preserved) asking the
    # oracle to deepen / be more specific. Cap at MAX_ROUNDS rounds.
    if args.source_url:
        MIN_GOOD_CANDIDATES = 1
        MAX_ROUNDS = 1
    else:
        MIN_GOOD_CANDIDATES = 3
        MAX_ROUNDS = 3
    deadline = time.time() + max(60, args.timeout_s)

    existing = _existing_board_titles_and_sources()
    accumulated_survivors: list[Candidate] = []
    accumulated_drops: list[tuple[str, str]] = []
    round_history: list[dict] = []
    seen_titles_lower: set[str] = set()

    submit = _submit_oracle_task(prompt)
    if not submit:
        _status_write({"ran_at": _now_iso(), "verdict": "submit_failed"})
        return 1
    task_id, conv_id = submit

    for round_idx in range(1, MAX_ROUNDS + 1):
        remaining_s = int(deadline - time.time())
        if remaining_s <= 30:
            round_history.append({
                "round": round_idx,
                "task_id": task_id,
                "verdict": "budget_exhausted",
            })
            _log(f"round {round_idx}: total timeout budget exhausted, breaking")
            break
        raw = _poll_oracle(task_id, timeout_s=remaining_s)
        if not raw:
            round_history.append({
                "round": round_idx, "task_id": task_id, "verdict": "timeout",
            })
            _log(f"round {round_idx}: timeout, breaking")
            break

        raw_path = LOG_DIR / f"refill_round{round_idx}_{_now_tag()}.txt"
        raw_path.write_text(raw, encoding="utf-8")

        candidates = _parse_candidates(raw)
        parsed_by = "oracle_json"
        if not candidates:
            candidates = _codex_extract_candidates(raw, round_idx=round_idx)
            parsed_by = "codex_adapter" if candidates else "none"
        _log(f"round {round_idx}: parsed {len(candidates)} candidates from oracle response")

        round_survivors: list[Candidate] = []
        round_drops: list[tuple[str, str]] = []
        for c in candidates:
            tl = c.title.strip().lower()
            if not tl or tl in seen_titles_lower:
                round_drops.append((c.title, "duplicate within this refill cycle"))
                continue
            if not c.final_display_form.strip() or not c.success_gate.strip():
                round_drops.append((c.title, "missing final_display_form or success_gate"))
                continue
            gate = academic_impact_gate(asdict(c))
            if not gate.passed:
                reason = (
                    f"academic_impact_gate score={gate.score}: "
                    + "; ".join((gate.missing + gate.risk_flags)[:5])
                )
                round_drops.append((c.title, reason))
                _log(f"academic gate drop (round {round_idx}): {c.title!r} — {reason}")
                continue
            keep, reason = _dedup_candidate(c, existing)
            if keep:
                round_survivors.append(c)
                seen_titles_lower.add(tl)
            else:
                round_drops.append((c.title, reason))
                _log(f"dedup drop (round {round_idx}): {c.title!r} — {reason}")

        accumulated_survivors.extend(round_survivors)
        accumulated_drops.extend(round_drops)
        round_history.append({
            "round": round_idx,
            "task_id": task_id,
            "raw_response_path": str(raw_path),
            "parsed_by": parsed_by,
            "received": len(candidates),
            "kept": len(round_survivors),
            "dropped": len(round_drops),
        })

        if len(accumulated_survivors) >= MIN_GOOD_CANDIDATES:
            _log(f"round {round_idx}: have {len(accumulated_survivors)} survivors, stopping")
            break
        if round_idx >= MAX_ROUNDS:
            _log(f"reached MAX_ROUNDS={MAX_ROUNDS} with {len(accumulated_survivors)} survivors")
            break
        if time.time() + 60 >= deadline:
            _log("not enough total budget left for follow-up; ending refill loop")
            break
        if not conv_id:
            _log("no conversation_id retained; cannot follow up")
            break

        # Build a follow-up prompt that's specific about what we still need.
        dropped_titles = [t for t, _ in accumulated_drops][:8]
        followup = (
            f"That round produced {len(candidates)} candidates of which we are keeping "
            f"{len(round_survivors)} ({len(accumulated_survivors)} cumulatively). "
            f"We need at least {MIN_GOOD_CANDIDATES}. Please propose more candidates "
            f"that satisfy the original criteria, with these constraints:\n\n"
            f"1. Do NOT re-propose any of these (already considered or dropped):\n"
            + "\n".join(f"   - {t}" for t in dropped_titles)
            + (
                "\n\n2. Be more specific about the omega_fit_detail — name exact "
                "Automath/Omega modules or the certificate/checker bridge we would build.\n"
                "3. Prefer influential named conjectures, public verifier gaps, "
                "high-visibility GitHub/blog/X/forum/problem-list discussions, or serious "
                "classification/rigidity/extremal targets. Do not optimize for recent arXiv "
                "preprints unless the topic is independently high-impact.\n"
                "4. Same JSON output schema.\n"
                "5. If you genuinely cannot produce more, output `{\"candidates\": []}` and "
                "explain in the rationale of an empty placeholder why."
            )
        )
        sub2 = _submit_followup(followup, conv_id)
        if not sub2:
            _log("follow-up submit failed; ending refill loop")
            break
        task_id = sub2
        # conv_id stays the same

    # ── Append survivors to board ──────────────────────────────────────
    next_id_int = int(re.match(r"T-(\d+)", _next_todo_id(existing)).group(1))
    blocks: list[str] = []
    appended_ids: list[str] = []
    for i, c in enumerate(accumulated_survivors):
        tid = f"T-{next_id_int + i:02d}"
        blocks.append(_format_candidate_block(tid, c))
        appended_ids.append(tid)

    inbox_ids: list[str] = []
    appended = 0
    if args.candidate_inbox:
        inbox_ids = _write_candidate_inbox(accumulated_survivors)
    else:
        appended = _append_to_board(blocks) if blocks else 0
    payload = {
        "ran_at": _now_iso(),
        "verdict": (
            "candidate_inbox" if inbox_ids else
            ("appended" if appended else ("no_candidates_parsed" if not accumulated_survivors else "all_drops"))
        ),
        "rounds": round_history,
        "candidates_total": sum(r.get("received", 0) for r in round_history),
        "appended_ids": appended_ids,
        "candidate_inbox_ids": inbox_ids,
        "drops": accumulated_drops[:32],
    }
    _status_write(payload)
    print(json.dumps(payload, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
