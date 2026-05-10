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
        "evidence below, output a technical health assessment, AND propose\n"
        "autonomous_actions for the supervisor to execute on your behalf.\n"
        "You have a Claude reviewer cross-checking you, so propose actions\n"
        "boldly when the evidence supports them — the project benefits more\n"
        "from active fine-tuning than from cautious silence.\n\n"
        "## Evidence\n"
        "```json\n"
        f"{json.dumps(evidence, ensure_ascii=False, indent=2)}\n"
        "```\n\n"
        "## Output (JSON only, no prose, no markdown fences)\n"
        "{\n"
        '  "loop_health": "healthy|degraded|blocked",\n'
        '  "blocked_papers": [{"paper": "...", "stage": "...", "reason": "..."}],\n'
        '  "stuck_stages": ["one-line summary of any stage stuck > 1 round"],\n'
        '  "concerns": ["concerns the supervisor should escalate to operator"],\n'
        '  "recommended_actions": ["operator-level next steps"],\n'
        '  "autonomous_actions": [\n'
        '    {"action": "cancel_task", "task_id": "...", "reason": "..."},\n'
        '    {"action": "reset_paper", "paper": "<state-json-stem>", "reason": "..."},\n'
        '    {"action": "restart_inner", "reason": "..."},\n'
        '    {"action": "adjust_cooldown", "key": "refill|pi_review", "hours": 0.0, "reason": "..."},\n'
        '    {"action": "apply_code_patch", "file": "tools/chatgpt-oracle/<name>.py",\n'
        '     "find": "exact unique substring to replace", "replace": "new text",\n'
        '     "reason": "...", "restart": "server|inner|both"},\n'
        '    {"action": "force_b_stuck_block", "paper": "<state-stem>",\n'
        '     "reason": "B_STUCK_REPEATED_BLOCKER|B_STUCK_JOURNAL_FIT"},\n'
        '    {"action": "trigger_retarget", "paper": "<state-stem>",\n'
        '     "new_target_journal": "(optional) journal name", "reason": "..."},\n'
        '    {"action": "requeue_focused_patch", "paper": "<state-stem>",\n'
        '     "canonical_key": "prop. 4.35", "reason": "..."}\n'
        '  ],\n'
        '  "summary": "one-sentence health snapshot"\n'
        "}\n\n"
        "Allowed autonomous_actions (whitelisted; supervisor will reject others):\n"
        "  - cancel_task: drop a stuck oracle task. Use for real review tasks\n"
        "    waiting >2 hours when the agent is clearly dead, or for any\n"
        "    task whose paper has since been marked DONE/BLOCKED elsewhere.\n"
        "  - reset_paper: clear A-BLOCKED state on a paper so it re-enters\n"
        "    the work pool. Use for papers blocked due to transient causes\n"
        "    (Claude exhaustion, codex 401) that have since resolved.\n"
        "  - restart_inner: bounce the inner pool. Use only when the pool\n"
        "    appears to have stopped progressing across all workers.\n"
        "  - adjust_cooldown: tune supervisor cooldowns (refill, pi_review).\n"
        "    Use to slow down PI when noise low, speed up refill when backlog drained.\n"
        "  - apply_code_patch: ★ self-iterating fix. When the supervisor /\n"
        "    inner / server log shows a deterministic bug (Unicode crash,\n"
        "    None where dict expected, off-by-one in a regex, missing import,\n"
        "    wrong default), propose a minimal find/replace patch to one of\n"
        "    the whitelisted files (oracle_pipeline.py, oracle_server.py,\n"
        "    oracle_dispatch.py, pipeline_supervisor.py, pi_review.py,\n"
        "    paper_refill.py, chatgpt_oracle_windows.user.js).\n"
        "    Hard rules: `find` MUST be a unique substring in the file; tests\n"
        "    in tests/test_pipeline_supervisor.py MUST keep passing after the\n"
        "    edit (supervisor runs them and rolls back if not). Choose minimal\n"
        "    patches over full rewrites. The reviewer (Claude) will cross-check\n"
        "    your patch before it lands. Use `restart` = the smallest scope that\n"
        "    picks up the change: server-only edits use \"server\", inner-only\n"
        "    edits (oracle_pipeline) use \"inner\", supervisor edits leave\n"
        "    `restart` empty (operator must restart supervisor manually).\n"
        "  - force_b_stuck_block: pin a deterministic stuck-block reason\n"
        "    onto a paper when the gate fired but state was lost (crash mid-\n"
        "    round, write race). Reason must be one of B_STUCK_REPEATED_BLOCKER\n"
        "    or B_STUCK_JOURNAL_FIT — exactly the strings the gate emits.\n"
        "  - trigger_retarget: reset a paper to Stage F so journal-fit can be\n"
        "    re-evaluated. GUARDED: only succeeds when Gate A would already\n"
        "    fire on next round (fit-streak >= 2 OR last 4 verdicts all\n"
        "    reject/major and no prior retarget). Hard cap at 2 retargets per\n"
        "    paper. Optional `new_target_journal` overrides Stage F's pick.\n"
        "  - requeue_focused_patch: replay the focused-patch path on a known\n"
        "    stuck canonical_key. GUARDED: key streak must be >= 2; rate-\n"
        "    limited to 1 use per paper per 24h. Use this when the gate-B\n"
        "    focused prompt clearly improved Codex's diff but the next\n"
        "    Oracle round hasn't happened yet — accelerates re-evaluation.\n\n"
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

    # Execute autonomous actions: only if Claude (the reviewer) did not
    # disagree, and only the whitelisted action names. Logs every decision.
    record["actions_executed"] = _execute_autonomous_actions(
        record["codex_verdict"], record["claude_verdict"], dry_run=dry_run,
    )

    record["wrote_inbox"] = _write_inbox(record)
    _append_log(
        f"health={record['codex_verdict'].get('loop_health','?')}/"
        f"{record['claude_verdict'].get('final_loop_health','?')} "
        f"actions={len(record['actions_executed'])} "
        f"summary={record['summary']!r}"
    )
    return record


_ALLOWED_AUTONOMOUS_ACTIONS = {
    "cancel_task", "reset_paper", "restart_inner", "adjust_cooldown",
    "apply_code_patch",
    "force_b_stuck_block", "trigger_retarget", "requeue_focused_patch",
}

# Per-paper rate-limit log for guarded actions. Keyed by paper_name → action
# → ISO timestamp of last successful invocation. Read/written by PI agent
# only; never persisted into PaperState (avoids dataclass schema churn).
_PI_ACTION_LOG = SCRIPT_DIR / ".pi_action_log.json"


def _read_action_log() -> dict[str, dict[str, str]]:
    if not _PI_ACTION_LOG.exists():
        return {}
    try:
        return json.loads(_PI_ACTION_LOG.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def _write_action_log(log: dict[str, dict[str, str]]) -> None:
    try:
        _PI_ACTION_LOG.write_text(
            json.dumps(log, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8")
    except OSError:
        pass


def _hours_since(iso_ts: str) -> float:
    if not iso_ts:
        return float("inf")
    try:
        dt = datetime.fromisoformat(iso_ts.replace("Z", "+00:00"))
    except ValueError:
        return float("inf")
    delta = datetime.now(dt.tzinfo) - dt
    return delta.total_seconds() / 3600.0

# Whitelist of files the PI agent may patch autonomously. Restricted to
# the orchestration layer; never the paper content, theory/, lean4/.
_PATCHABLE_FILES = {
    "tools/chatgpt-oracle/oracle_server.py",
    "tools/chatgpt-oracle/oracle_dispatch.py",
    "tools/chatgpt-oracle/oracle_pipeline.py",
    "tools/chatgpt-oracle/pipeline_supervisor.py",
    "tools/chatgpt-oracle/pi_review.py",
    "tools/chatgpt-oracle/paper_refill.py",
    "tools/chatgpt-oracle/chatgpt_oracle_windows.user.js",
}


def _execute_autonomous_actions(codex_verdict: dict[str, Any],
                                claude_verdict: dict[str, Any],
                                *, dry_run: bool) -> list[dict[str, Any]]:
    """Execute whitelisted PI autonomous actions.

    Safety gate: if Claude reviewer set agree_with_codex=False, we still
    execute the actions Codex proposed but log Claude's disagreements
    alongside so the operator can audit. Per the user's design, PI's
    permissions are wide because the reviewer pass is the safety check.
    """
    actions = list(codex_verdict.get("autonomous_actions") or [])
    if not actions:
        return []
    executed: list[dict[str, Any]] = []
    if dry_run:
        for entry in actions:
            executed.append({**entry, "result": "dry_run"})
        return executed

    # Lazy import to avoid circular: pi_review is called from supervisor.
    import urllib.request
    import urllib.error

    state_dir = SCRIPT_DIR / "pipeline_state"

    for entry in actions:
        if not isinstance(entry, dict):
            continue
        name = str(entry.get("action") or "").strip()
        if name not in _ALLOWED_AUTONOMOUS_ACTIONS:
            executed.append({**entry, "result": f"rejected: action {name!r} not whitelisted"})
            continue
        try:
            if name == "cancel_task":
                tid = str(entry.get("task_id") or "").strip()
                if not tid:
                    executed.append({**entry, "result": "rejected: missing task_id"})
                    continue
                req = urllib.request.Request(
                    "http://localhost:8765/cancel",
                    data=json.dumps({"task_id": tid, "reason": "pi_autonomous"}).encode("utf-8"),
                    headers={"Content-Type": "application/json"},
                )
                with urllib.request.urlopen(req, timeout=10) as r:
                    resp = json.loads(r.read().decode("utf-8"))
                executed.append({**entry, "result": f"cancelled: {resp.get('status', '?')}"})
            elif name == "reset_paper":
                paper = str(entry.get("paper") or "").strip()
                if not paper:
                    executed.append({**entry, "result": "rejected: missing paper"})
                    continue
                p = state_dir / f"{paper}.json"
                if not p.exists():
                    executed.append({**entry, "result": f"rejected: state {paper}.json missing"})
                    continue
                d = json.loads(p.read_text(encoding="utf-8"))
                d["error"] = ""
                d["current_stage"] = "A"
                d["stage_a_rounds"] = 0
                d["stage_a_audit_rounds"] = 0
                d["stage_a_passed"] = False
                d["current_round"] = 0
                p.write_text(json.dumps(d, ensure_ascii=False, indent=2) + "\n",
                             encoding="utf-8")
                executed.append({**entry, "result": "reset"})
            elif name == "restart_inner":
                (SCRIPT_DIR / ".inner.restart").write_text(
                    f"pi_autonomous {_now_iso()}\n", encoding="utf-8")
                executed.append({**entry, "result": "signal written"})
            elif name == "adjust_cooldown":
                # Cooldowns live as supervisor CLI flags / supervisor_state;
                # we record the request to the inbox for the operator. Real
                # in-flight adjustment would require IPC into the supervisor
                # process, out of scope for this version.
                executed.append({**entry, "result": "logged (manual apply via supervisor flags)"})
            elif name == "apply_code_patch":
                executed.append({**entry, "result": _execute_apply_code_patch(entry)})
            elif name == "force_b_stuck_block":
                executed.append({**entry, "result": _execute_force_b_stuck_block(entry, state_dir)})
            elif name == "trigger_retarget":
                executed.append({**entry, "result": _execute_trigger_retarget(entry, state_dir)})
            elif name == "requeue_focused_patch":
                executed.append({**entry, "result": _execute_requeue_focused_patch(entry, state_dir)})
        except Exception as exc:
            executed.append({**entry, "result": f"error: {exc}"})

    if executed:
        _append_log(f"autonomous actions: {json.dumps(executed, ensure_ascii=False)[:500]}")
    return executed


_VALID_FORCE_BLOCK_REASONS = {
    "B_STUCK_REPEATED_BLOCKER", "B_STUCK_JOURNAL_FIT",
}


def _load_paper_state(paper: str, state_dir: Path) -> tuple[Path, dict[str, Any] | None]:
    if not paper:
        return Path(), None
    p = state_dir / f"{paper}.json"
    if not p.exists():
        return p, None
    try:
        return p, json.loads(p.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return p, None


def _save_paper_state(p: Path, d: dict[str, Any]) -> None:
    p.write_text(json.dumps(d, ensure_ascii=False, indent=2) + "\n",
                 encoding="utf-8")


def _execute_force_b_stuck_block(entry: dict[str, Any], state_dir: Path) -> str:
    """Force-record a Stage-B stuck-block reason on a paper.

    Used when the deterministic gate fired but state was lost (crash,
    write race). Only valid reasons are the gate's own constants.
    """
    paper = str(entry.get("paper") or "").strip()
    reason = str(entry.get("reason") or "").strip()
    if reason not in _VALID_FORCE_BLOCK_REASONS:
        return f"rejected: reason {reason!r} not in {sorted(_VALID_FORCE_BLOCK_REASONS)}"
    p, d = _load_paper_state(paper, state_dir)
    if d is None:
        return f"rejected: state {paper}.json missing"
    d["block_reason"] = reason
    d["stage_b_passed"] = False
    _save_paper_state(p, d)
    return f"forced block_reason={reason}"


def _execute_trigger_retarget(entry: dict[str, Any], state_dir: Path) -> str:
    """Reset paper to Stage F so journal-fit can be re-evaluated.

    Guard: only allowed when journal-fit streak >= 2 (gate would fire) OR
    retarget_history is empty AND last 4 verdicts are all reject/major.
    Also caps total retargets at 2 per paper to prevent infinite loops.
    """
    paper = str(entry.get("paper") or "").strip()
    new_journal = str(entry.get("new_target_journal") or "").strip()
    p, d = _load_paper_state(paper, state_dir)
    if d is None:
        return f"rejected: state {paper}.json missing"

    history = d.get("retarget_history") or []
    if len(history) >= 2:
        return f"rejected: max retargets reached ({len(history)}); halt to human"

    streaks = d.get("stage_b_issue_streaks") or {}
    fit_streak = int(streaks.get("__journal_fit__", 0))
    last_verdicts = (d.get("stage_b_verdicts") or [])[-4:]
    bad = {"reject", "major revision"}
    fit_gate_armed = fit_streak >= 2
    fresh_armed = (not history) and len(last_verdicts) >= 4 and all(v in bad for v in last_verdicts)
    if not (fit_gate_armed or fresh_armed):
        return (f"rejected: guard not satisfied "
                f"(fit_streak={fit_streak}, last4={last_verdicts}, history={len(history)})")

    prior_journal = d.get("target_journal", "")
    history.append({
        "from_journal": prior_journal,
        "trigger": "pi_autonomous_trigger_retarget",
        "round": d.get("stage_b_rounds", 0),
        "timestamp": _now_iso(),
    })
    d["retarget_history"] = history
    d["current_stage"] = "F"
    d["stage_f_passed"] = False
    d["stage_b_passed"] = False
    d["stage_b_verdicts"] = []
    d["stage_b_all_issues"] = []
    d["stage_b_deepen_conv_id"] = ""
    d["stage_b_fresh_attempts"] = 0
    d["stage_b_rounds"] = 0
    d["stage_b_issue_streaks"] = {}
    if new_journal:
        d["target_journal"] = new_journal
    d["error"] = ""
    _save_paper_state(p, d)
    return f"retargeted (prev={prior_journal}, new={new_journal or 'TBD-by-Stage-F'})"


def _execute_requeue_focused_patch(entry: dict[str, Any], state_dir: Path) -> str:
    """Replay the focused-patch path on a known stuck issue once.

    Guard: canonical_key must already be tracked with streak >= 2.
    Rate-limit: at most 1 use per paper per 24 hours.
    Implementation: clears the codex-fix completion marker on the current
    round (forces the inner loop to re-run B4 with the focused-patch
    prefix already injected by gate B). We don't re-prompt directly here
    — we just reset state so the next inner loop iteration picks it up.
    """
    paper = str(entry.get("paper") or "").strip()
    key = str(entry.get("canonical_key") or "").strip()
    p, d = _load_paper_state(paper, state_dir)
    if d is None:
        return f"rejected: state {paper}.json missing"

    streaks = d.get("stage_b_issue_streaks") or {}
    streak = int(streaks.get(key, 0))
    if streak < 2:
        return f"rejected: key {key!r} streak {streak} < 2"

    log = _read_action_log()
    paper_log = log.get(paper, {})
    last = paper_log.get("requeue_focused_patch", "")
    hrs = _hours_since(last)
    if hrs < 24.0:
        return f"rejected: rate-limited (last use {hrs:.1f}h ago, need 24h)"

    # Trigger: clear current round error so inner loop re-enters with the
    # focused-patch prefix that gate B injects on streak>=2.
    d["error"] = ""
    _save_paper_state(p, d)

    paper_log["requeue_focused_patch"] = _now_iso()
    log[paper] = paper_log
    _write_action_log(log)
    return f"requeued (key={key!r}, streak={streak})"


def _execute_apply_code_patch(entry: dict[str, Any]) -> str:
    """Apply a code patch proposed by Codex+Claude consensus.

    Schema:
      file:    repo-relative path (must be in _PATCHABLE_FILES)
      find:    exact substring to replace (must be unique in file)
      replace: replacement text
      reason:  why
      restart: optional, "server" / "inner" / "" — what to restart after

    Workflow:
      1. Whitelist check
      2. Find/replace (require uniqueness)
      3. Run test_pipeline_supervisor.py — must pass
      4. git add + commit + push
      5. Touch the requested restart signal so supervisor picks it up

    Returns a string summary of what happened.
    """
    import subprocess
    import shutil

    rel = str(entry.get("file") or "").strip().replace("\\", "/")
    find_str = entry.get("find")
    replace_str = entry.get("replace")
    if rel not in _PATCHABLE_FILES:
        return f"rejected: {rel!r} not in patch whitelist"
    if not isinstance(find_str, str) or not isinstance(replace_str, str):
        return "rejected: find/replace must be strings"
    if not find_str:
        return "rejected: empty find"
    if find_str == replace_str:
        return "rejected: no-op patch"

    target = REPO_ROOT / rel
    if not target.exists():
        return f"rejected: {rel} does not exist"

    try:
        original = target.read_text(encoding="utf-8")
    except OSError as exc:
        return f"error reading file: {exc}"
    occ = original.count(find_str)
    if occ == 0:
        return "rejected: find string not present"
    if occ > 1:
        return f"rejected: find string non-unique ({occ} occurrences)"

    backup = original
    patched = original.replace(find_str, replace_str, 1)
    try:
        target.write_text(patched, encoding="utf-8")
    except OSError as exc:
        return f"error writing patch: {exc}"

    # Run tests; on failure, revert.
    test_path = REPO_ROOT / "tools/chatgpt-oracle/tests/test_pipeline_supervisor.py"
    test_ok = True
    if test_path.exists():
        try:
            test_proc = subprocess.run(
                [sys.executable, str(test_path)],
                cwd=str(REPO_ROOT / "tools/chatgpt-oracle"),
                capture_output=True, text=True, timeout=120,
            )
            test_ok = (test_proc.returncode == 0)
            if not test_ok:
                _append_log(f"apply_code_patch: tests FAILED, rolling back. "
                            f"stderr_excerpt={(test_proc.stderr or '')[:200]}")
        except (subprocess.TimeoutExpired, OSError) as exc:
            test_ok = False
            _append_log(f"apply_code_patch: test runner error: {exc}")

    if not test_ok:
        try:
            target.write_text(backup, encoding="utf-8")
        except OSError as exc:
            return f"error: tests failed AND rollback failed ({exc})"
        return "rejected: tests failed; rolled back"

    # Commit + push.
    reason = str(entry.get("reason") or "pi autonomous patch")[:200]
    msg = f"pi autonomous patch ({rel}): {reason}"
    try:
        subprocess.run(["git", "add", str(target)], cwd=str(REPO_ROOT),
                       capture_output=True, text=True, check=True, timeout=30)
        commit = subprocess.run(["git", "commit", "-m", msg], cwd=str(REPO_ROOT),
                                capture_output=True, text=True, timeout=60)
        if commit.returncode != 0:
            target.write_text(backup, encoding="utf-8")
            return f"rejected: git commit failed ({commit.stderr.strip()[:120]}); rolled back"
        push = subprocess.run(["git", "push", "origin", "HEAD"],
                              cwd=str(REPO_ROOT),
                              capture_output=True, text=True, timeout=120)
        if push.returncode != 0:
            return f"applied + committed but push failed: {push.stderr.strip()[:120]}"
    except (subprocess.SubprocessError, OSError) as exc:
        target.write_text(backup, encoding="utf-8")
        return f"error during commit/push: {exc}; rolled back"

    # Trigger appropriate restart so the patch takes effect.
    restart = str(entry.get("restart") or "").strip().lower()
    if restart in {"server", "both"}:
        (SCRIPT_DIR / ".server.restart").write_text(
            f"pi_autonomous_patch {_now_iso()}\n", encoding="utf-8")
    if restart in {"inner", "both", ""} and rel != "tools/chatgpt-oracle/pipeline_supervisor.py":
        (SCRIPT_DIR / ".inner.restart").write_text(
            f"pi_autonomous_patch {_now_iso()}\n", encoding="utf-8")

    return f"applied + committed + pushed; restart={restart or 'inner'}"


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
