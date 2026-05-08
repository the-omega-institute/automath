#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""PI agent — joint Codex + Claude review of pipeline health.

The supervisor handles low-level liveness (server up, inner up, queue
moving). This module adds a periodic *judgment* layer that two
independent reasoners run side by side:

  * Codex reads pipeline_state JSONs + recent supervisor logs and
    writes a technical assessment: which papers are blocked, which
    stage looks stuck, what the recommended next intervention is.
  * Claude reads the same evidence + Codex's assessment and writes
    an independent cross-check: does the assessment hold? what did
    Codex miss? any concerns the supervisor should escalate?

Both agents output one JSON object each. The PI report combines them
into a single record, appended to .pi_inbox.md and supervisor.log.
The supervisor runs this on a long cooldown (default 6h) — it is a
sanity layer, not a critical-path gate, so a cold ChatGPT or a slow
Claude here never blocks paper progress.

Usage (standalone):
    python tools/chatgpt-oracle/pi_review.py            # one-shot
    python tools/chatgpt-oracle/pi_review.py --dry-run  # skip CLI calls

Returned dict shape:
    {
        "status": "ok" | "codex_failed" | "claude_failed" | "both_failed",
        "codex_verdict": {...},   # technical assessment
        "claude_verdict": {...},  # cross-check
        "wrote_inbox": True/False,
        "summary": "one-line health snapshot",
    }
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
PIPELINE_STATE_DIR = SCRIPT_DIR / "pipeline_state"
SUPERVISOR_LOG_DIR = SCRIPT_DIR / "supervisor_logs"
PI_INBOX = SCRIPT_DIR / ".pi_inbox.md"
PI_REVIEW_LOG = SUPERVISOR_LOG_DIR / "pi_review.log"

DEFAULT_CODEX_TIMEOUT = 900
DEFAULT_CLAUDE_TIMEOUT = 600
RECENT_LOG_LINES = 200
MAX_STATE_FILES = 60

sys.path.insert(0, str(SCRIPT_DIR))


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _load_pipeline_states() -> list[dict[str, Any]]:
    if not PIPELINE_STATE_DIR.exists():
        return []
    states: list[dict[str, Any]] = []
    for p in sorted(PIPELINE_STATE_DIR.glob("*.json"))[:MAX_STATE_FILES]:
        try:
            data = json.loads(p.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            continue
        states.append({
            "paper": p.stem,
            "current_stage": data.get("current_stage"),
            "status": data.get("status"),
            "error": data.get("error"),
            "next_action": data.get("next_action"),
            "updated_at": data.get("updated_at"),
            "rounds": data.get("rounds"),
        })
    return states


def _read_recent_supervisor_log(lines: int = RECENT_LOG_LINES) -> str:
    log = SUPERVISOR_LOG_DIR / "supervisor.log"
    if not log.exists():
        return ""
    try:
        text = log.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""
    return "\n".join(text.splitlines()[-lines:])


def _evidence_payload() -> dict[str, Any]:
    return {
        "captured_at": _now_iso(),
        "pipeline_states": _load_pipeline_states(),
        "recent_supervisor_log": _read_recent_supervisor_log(),
    }


def _codex_prompt(evidence: dict[str, Any]) -> str:
    return (
        "You are the PI agent for the paper publication pipeline. Read the\n"
        "evidence below and output a technical health assessment. Be terse,\n"
        "factual, and actionable.\n\n"
        "## Evidence\n"
        "```json\n"
        f"{json.dumps(evidence, ensure_ascii=False, indent=2)}\n"
        "```\n\n"
        "## Output (JSON only, no prose, no markdown fences)\n"
        "{\n"
        '  "loop_health": "healthy|degraded|blocked",\n'
        '  "blocked_papers": [{"paper": "...", "stage": "...", "reason": "..."}],\n'
        '  "stuck_stages": ["one-line summary of any stage stuck > 1 round"],\n'
        '  "concerns": ["concrete concerns the supervisor should escalate"],\n'
        '  "recommended_actions": ["specific operator-level next steps"],\n'
        '  "summary": "one-sentence health snapshot"\n'
        "}\n\n"
        "Rules:\n"
        "- loop_health = healthy if everything is moving without intervention.\n"
        "- loop_health = degraded if there are noisy errors but progress continues.\n"
        "- loop_health = blocked if any paper is stuck and needs operator action.\n"
        "- blocked_papers and concerns must reference actual papers/stages from the evidence.\n"
        "- recommended_actions must be specific (file paths, restart files, --inner-restart).\n"
    )


def _claude_prompt(evidence: dict[str, Any], codex_verdict: dict[str, Any]) -> str:
    return (
        "You are the cross-check reviewer for the PI agent. Codex just\n"
        "produced the technical assessment below. Independently re-read the\n"
        "evidence and decide whether the assessment holds. Look for things\n"
        "Codex missed (silent stalls, mis-classified errors, drift).\n\n"
        "## Evidence\n"
        "```json\n"
        f"{json.dumps(evidence, ensure_ascii=False, indent=2)}\n"
        "```\n\n"
        "## Codex's assessment\n"
        "```json\n"
        f"{json.dumps(codex_verdict, ensure_ascii=False, indent=2)}\n"
        "```\n\n"
        "## Output (JSON only, no prose, no markdown fences)\n"
        "{\n"
        '  "agree_with_codex": true|false,\n'
        '  "disagreements": ["specific points where Codex is wrong or incomplete"],\n'
        '  "missed_concerns": ["issues the operator should know that Codex did not flag"],\n'
        '  "additional_actions": ["actions beyond Codex\'s recommendations"],\n'
        '  "final_loop_health": "healthy|degraded|blocked",\n'
        '  "summary": "one-sentence cross-check verdict"\n'
        "}\n\n"
        "If you fully agree, set agree_with_codex=true and leave disagreements / missed_concerns empty.\n"
        "Be concise. Do not paraphrase Codex back at us.\n"
    )


def _safe_json(text: str) -> dict[str, Any]:
    """Tolerant JSON extractor — handles fenced output and surrounding prose."""
    if not text:
        return {}
    s = text.strip()
    if s.startswith("```"):
        s = s.split("```", 2)[1] if s.count("```") >= 2 else s
        if s.startswith("json"):
            s = s[4:]
        s = s.strip("` \n\r\t")
    first = s.find("{")
    last = s.rfind("}")
    if first == -1 or last == -1 or last < first:
        return {}
    try:
        return json.loads(s[first: last + 1])
    except json.JSONDecodeError:
        return {}


def _write_inbox(record: dict[str, Any]) -> bool:
    """Append a human-readable PI report to .pi_inbox.md."""
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    PI_INBOX.parent.mkdir(parents=True, exist_ok=True)
    codex = record.get("codex_verdict", {}) or {}
    claude = record.get("claude_verdict", {}) or {}
    block = []
    block.append(f"## PI review — {record.get('captured_at', _now_iso())}\n")
    block.append(f"- supervisor health: **{codex.get('loop_health', '?')}**"
                 f" (claude cross-check: {claude.get('final_loop_health', '?')})\n")
    if codex.get("summary"):
        block.append(f"- codex: {codex['summary']}\n")
    if claude.get("summary"):
        block.append(f"- claude: {claude['summary']}\n")
    if codex.get("blocked_papers"):
        block.append("\n### Blocked papers\n")
        for item in codex["blocked_papers"]:
            block.append(f"- `{item.get('paper','?')}` stage `{item.get('stage','?')}`: {item.get('reason','')}\n")
    concerns = list(codex.get("concerns", []) or []) + list(claude.get("missed_concerns", []) or [])
    if concerns:
        block.append("\n### Concerns\n")
        for c in concerns:
            block.append(f"- {c}\n")
    actions = list(codex.get("recommended_actions", []) or []) + list(claude.get("additional_actions", []) or [])
    if actions:
        block.append("\n### Recommended actions\n")
        for a in actions:
            block.append(f"- {a}\n")
    if claude.get("disagreements"):
        block.append("\n### Claude disagreements with Codex\n")
        for d in claude["disagreements"]:
            block.append(f"- {d}\n")
    block.append("\n---\n\n")
    try:
        with PI_INBOX.open("a", encoding="utf-8") as f:
            f.writelines(block)
        return True
    except OSError:
        return False


def _append_log(line: str) -> None:
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    try:
        with PI_REVIEW_LOG.open("a", encoding="utf-8") as f:
            f.write(f"[{_now_iso()}] {line}\n")
    except OSError:
        pass


def run_pi_review(*, dry_run: bool = False,
                  codex_timeout: int = DEFAULT_CODEX_TIMEOUT,
                  claude_timeout: int = DEFAULT_CLAUDE_TIMEOUT,
                  model: str = "") -> dict[str, Any]:
    """Run codex + claude joint review. Returns merged record."""
    # Lazy import — oracle_pipeline pulls in lots of deps.
    import oracle_pipeline  # noqa: PLC0415

    evidence = _evidence_payload()
    record: dict[str, Any] = {
        "captured_at": evidence["captured_at"],
        "codex_verdict": {},
        "claude_verdict": {},
        "status": "ok",
        "wrote_inbox": False,
        "summary": "",
    }

    codex_prompt = _codex_prompt(evidence)
    try:
        codex_raw = oracle_pipeline.codex_exec(
            codex_prompt,
            work_dir=REPO_ROOT,
            timeout_seconds=codex_timeout,
            dry_run=dry_run,
            context_mode="contextual_supervision",
            agent_role="pi_agent_codex",
            **({"model": model} if model else {}),
        )
    except Exception as exc:
        _append_log(f"codex failed: {exc}")
        record["status"] = "codex_failed"
        record["summary"] = f"codex unavailable: {exc}"
        return record
    record["codex_verdict"] = _safe_json(codex_raw) if not dry_run else {
        "loop_health": "healthy",
        "summary": "(dry run)",
    }

    claude_prompt = _claude_prompt(evidence, record["codex_verdict"])
    try:
        claude_raw = oracle_pipeline.claude_exec(
            claude_prompt,
            work_dir=REPO_ROOT,
            timeout_seconds=claude_timeout,
            dry_run=dry_run,
            context_mode="contextual_supervision",
            agent_role="pi_agent_claude",
        )
    except Exception as exc:
        _append_log(f"claude failed: {exc}")
        # Codex's read still has value — keep it, mark partial.
        record["status"] = "claude_failed"
        record["summary"] = (record["codex_verdict"].get("summary", "")
                             or f"claude unavailable: {exc}")
        record["wrote_inbox"] = _write_inbox(record)
        return record
    record["claude_verdict"] = _safe_json(claude_raw) if not dry_run else {
        "agree_with_codex": True,
        "summary": "(dry run)",
    }

    record["summary"] = (
        record["codex_verdict"].get("summary")
        or record["claude_verdict"].get("summary")
        or "no summary"
    )
    record["wrote_inbox"] = _write_inbox(record)
    _append_log(
        f"health={record['codex_verdict'].get('loop_health','?')}/"
        f"{record['claude_verdict'].get('final_loop_health','?')} "
        f"summary={record['summary']!r}"
    )
    return record


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Joint PI agent review")
    parser.add_argument("--dry-run", action="store_true",
                        help="Skip codex/claude calls; produce a stub record.")
    parser.add_argument("--codex-timeout", type=int, default=DEFAULT_CODEX_TIMEOUT)
    parser.add_argument("--claude-timeout", type=int, default=DEFAULT_CLAUDE_TIMEOUT)
    parser.add_argument("--model", default="",
                        help="Override codex model (passed through to codex_exec)")
    args = parser.parse_args(argv)
    record = run_pi_review(
        dry_run=args.dry_run,
        codex_timeout=args.codex_timeout,
        claude_timeout=args.claude_timeout,
        model=args.model,
    )
    print(json.dumps(record, ensure_ascii=False, indent=2))
    return 0 if record.get("status") == "ok" else 1


if __name__ == "__main__":
    sys.exit(main())
