#!/usr/bin/env python3
"""outreach_task_runner — drains the typed-task queue and lands drafts for review.

Spawned as a daemon by outreach_supervisor.py (`--loop`), or run once on a
single task for testing (`--once --task-id <id>`). Companion to
outreach_research_loop.py:

  research_loop  : open-problem research over RESEARCH_BOARD T-NN entries
  task_runner    : specific operator commitments with structured gates

For each pending task it:

  1. Acquires a claim marker:  outreach_state/task_claims/<id>/.in_progress
  2. Sets task.status = "in_progress" and saves it.
  3. Dispatches a typed worker:
       - issue_reply_draft / email_reply_draft / experimental
           single claude_exec call producing one markdown draft
       - paper_trade
           multi-step: download external artifact (best-effort) →
           summarize → generate annotated questions → generate library
           pointers; each step is its own claude_exec
       - code_pr_response
           hard-blocked unless external repo checked out locally
  4. Runs outreach_gates.evaluate(task).
  5. On pass: task.status = "gated_ready"; deliverables already on disk
     under drafts/.
     On fail (retries < max): task.status = "pending" for retry.
     On fail (retries == max) or escalate: task.status = "rejected".
     On blocked: task.status = "blocked".
  6. Releases claim.

Hard rules carried from project conventions:
  - never sends anything externally; deliverables are drafts/ files only
  - never edits other tasks' deliverables
  - never edits OUTREACH_LOG / RESEARCH_BOARD content
  - never runs Lean / lake / elan / mathlib4
  - skips tasks marked requires_lean=True (see feedback memory 2026-05-08)

Stop the daemon by sending SIGINT/SIGTERM. The supervisor manages the
process; on supervisor shutdown the daemon receives SIGTERM and exits.
"""

from __future__ import annotations

import argparse
import os
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_DIR = SCRIPT_DIR / "outreach_state"
TASK_CLAIMS_DIR = STATE_DIR / "task_claims"
TASK_RUNNER_LOG_DIR = STATE_DIR / "task_runner_logs"
DRAFTS_DIR = SCRIPT_DIR / "drafts"

DEFAULT_POLL_INTERVAL = 180
DEFAULT_CLAIM_STALE_HOURS = 4
DEFAULT_MAX_TASK_TIMEOUT_S = 5400  # 90 min hard cap per task

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_task_spec import (  # noqa: E402
    TASK_QUEUE_DIR,
    TaskSpec,
    list_tasks,
    load_task,
    save_task,
    select_workable,
)
import outreach_gates  # noqa: E402


# ---------------------------------------------------------------------------
# logging
# ---------------------------------------------------------------------------


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def runner_log(msg: str) -> None:
    TASK_RUNNER_LOG_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {msg}"
    print(line, flush=True)
    with open(TASK_RUNNER_LOG_DIR / "task_runner.log", "a", encoding="utf-8") as f:
        f.write(line + "\n")


# ---------------------------------------------------------------------------
# claim semantics (pid-aware, matches research_loop)
# ---------------------------------------------------------------------------


def _claim_dir(task_id: str) -> Path:
    return TASK_CLAIMS_DIR / task_id


def _claim_marker(task_id: str) -> Path:
    return _claim_dir(task_id) / ".in_progress"


def _claim_pid_file(task_id: str) -> Path:
    return _claim_dir(task_id) / ".pid"


def claim(task_id: str) -> bool:
    d = _claim_dir(task_id)
    d.mkdir(parents=True, exist_ok=True)
    marker = _claim_marker(task_id)
    if marker.exists():
        return False
    try:
        fd = os.open(str(marker), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        os.write(fd, f"claimed_at={_now_iso()}\npid={os.getpid()}\n".encode())
        os.close(fd)
    except FileExistsError:
        return False
    except OSError as exc:
        runner_log(f"claim({task_id}) failed: {exc}")
        return False
    try:
        _claim_pid_file(task_id).write_text(str(os.getpid()), encoding="utf-8")
    except OSError:
        pass
    return True


def release(task_id: str) -> None:
    for p in (_claim_marker(task_id), _claim_pid_file(task_id)):
        try:
            p.unlink()
        except FileNotFoundError:
            pass


def _pid_alive(pid: int) -> bool:
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
        return True
    except (ProcessLookupError, OSError):
        return False


def cleanup_stale_claims(stale_hours: float = DEFAULT_CLAIM_STALE_HOURS) -> int:
    if not TASK_CLAIMS_DIR.exists():
        return 0
    released = 0
    cutoff = time.time() - stale_hours * 3600
    for d in TASK_CLAIMS_DIR.iterdir():
        if not d.is_dir():
            continue
        marker = d / ".in_progress"
        if not marker.exists():
            continue
        try:
            mtime = marker.stat().st_mtime
        except OSError:
            continue
        pid = 0
        pid_file = d / ".pid"
        if pid_file.exists():
            try:
                pid = int((pid_file.read_text(encoding="utf-8").strip() or "0"))
            except (OSError, ValueError):
                pid = 0
        if mtime > cutoff and _pid_alive(pid):
            continue
        try:
            marker.unlink()
        except OSError:
            pass
        try:
            pid_file.unlink()
        except (FileNotFoundError, OSError):
            pass
        released += 1
    return released


# ---------------------------------------------------------------------------
# workers per task type
#
# Author allocation (per operator decision 2026-05-08):
#   - codex_track: primary deep-reasoning + drafting (codex authors,
#     codex self-audits, claude does redline hygiene only)
#   - oracle (ChatGPT Project): codex_track escalations + tasks pre-flagged
#     with context.use_oracle=True (need Project-attached files like
#     main.pdf / READMEs / PROGRAM_BOARD.md as deep context)
#   - claude: gate auditor (claude_review) + writeback skill (/killo-golden,
#     handled by outreach_writeback_loop). NOT used as primary author here.
# ---------------------------------------------------------------------------


def _abs(rel: str) -> Path:
    p = Path(rel)
    return p if p.is_absolute() else (REPO_ROOT / p)


def _ensure_parent(p: Path) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)


def _infer_source_type(task: TaskSpec) -> str:
    """Map TaskSpec.type → outreach_codex_track source_type."""
    mapping = {
        "issue_reply_draft": "gh_issue",
        "email_reply_draft": "email",
        "experimental": "email",
    }
    return mapping.get(task.type, "email")


def _build_retry_context(task: TaskSpec, prev_deliverable: Path) -> str:
    """Assemble the retry-feedback block for codex_track / paper_trade.

    On the first attempt this returns "" so the prompt template just says
    "(no prior task-level failures)". On retry attempts this synthesizes:
      - the gate's last_reason verbatim (which file failed, why)
      - retries count vs max_retries
      - the actual previous deliverable text (truncated) so codex sees
        what it produced and can target the gap directly
    """
    if task.retries <= 0 or not (task.last_reason or task.last_verdict):
        return ""
    parts = [
        f"This is task-level retry #{task.retries} of {task.max_retries}.",
        "",
        f"Previous gate verdict: {task.last_verdict or 'fail'}",
        f"Previous gate reason: {task.last_reason or '(none recorded)'}",
        "",
        "Address the specific failure above. If the gate said the previous draft was undersize, EXPAND on the under-treated points named in the reason; do not shorten existing material. If the gate flagged missing terms, weave them in naturally.",
    ]
    try:
        if prev_deliverable.exists():
            prev_body = prev_deliverable.read_text(encoding="utf-8", errors="replace")
            if prev_body.strip():
                parts.append("")
                parts.append("Previous draft body (full text — improve, do not paste back unchanged):")
                parts.append("```")
                parts.append(prev_body[:25000])
                parts.append("```")
    except OSError:
        pass
    return "\n".join(parts)


def _run_oracle_drafting_task(task: TaskSpec) -> tuple[bool, str]:
    """Drafting via ChatGPT Project oracle (deep reasoning).

    For tasks where context.use_oracle=True the deliverable benefits from the
    Project's attached files (main.pdf + READMEs + PROGRAM_BOARD). Routes
    through OracleConsultant.deep_reasoning — multi-turn driver that opens
    a fresh conversation with the framing prompt + drives DEFAULT_DEEPENING
    follow-ups until BREAKTHROUGH / STUCK / EXHAUSTED. Reuses the same
    pattern dispatch_worktree --supervise --oracle-deep already uses for
    T-NN entries.

    Saves the final response (and oracle-authored LaTeX if produced) to
    deliverable_paths[0]. Operator + claude_review gate audits afterwards.
    """
    if not task.deliverable_paths:
        return False, "no deliverable_paths configured"
    target = _abs(task.deliverable_paths[0])
    _ensure_parent(target)

    try:
        from oracle_consultant import (  # noqa: PLC0415
            OracleConsultant,
            DEFAULT_WRITE_PAPER_LATEX_PROMPT,
            codex_driven_prompt_generator,
        )
    except Exception as exc:
        return False, f"oracle_consultant import failed: {exc}"

    consultant = OracleConsultant()
    if not consultant.is_alive():
        return False, f"oracle server unreachable at {consultant.server_url}; aborting (will retry next cycle)"

    ctx = task.context or {}
    constraints = ctx.get("operator_constraints") or []
    if not isinstance(constraints, list):
        constraints = [str(constraints)]
    constraints_block = "\n".join(f"- {c}" for c in constraints) or "(none beyond context fidelity)"

    import json as _json
    initial_prompt = (
        f"You are the deep-reasoning oracle for the Omega Outreach project. "
        f"Operator-curated commitment task: {task.title}\n\n"
        f"# Context (do not invent facts beyond what is stated here)\n\n"
        f"```\n{_json.dumps(ctx, ensure_ascii=False, indent=2)}\n```\n\n"
        f"# Hard constraints\n\n{constraints_block}\n\n"
        f"# Required deliverable — output discipline (CRITICAL)\n\n"
        f"Produce the final draft suitable for {ctx.get('thread', 'the named external party')}.\n\n"
        f"OUTPUT THE COMPLETE DELIVERABLE AS INLINE MESSAGE TEXT. Treat your\n"
        f"response body itself as the deliverable file we will copy verbatim.\n\n"
        f"Forbidden response shapes:\n"
        f"  - Saying 'I have written this to <path>' or referencing a file you 'saved'\n"
        f"  - Returning only file paths, links, or pointers in lieu of content\n"
        f"  - Splitting the deliverable into a separate document and only summarising it\n"
        f"  - Wrapping the deliverable in scaffolding ('Here is the draft:'); just emit it\n\n"
        f"The Project's attached files (main.pdf, MAIN_PAPER_INDEX.md, READMEs,\n"
        f"PROGRAM_BOARD.md) are available — cite them inline where relevant for\n"
        f"fidelity, but the cited content must be paraphrased into the body text.\n\n"
        f"# Termination signal\n\n"
        f"When your inline draft satisfies every operator constraint AND every\n"
        f"`scope_ledger_items_to_pin` item is reproduced AND the Bridge Schema /\n"
        f"central claim is stated, append the literal token BREAKTHROUGH on its\n"
        f"own line at the end of the same response. The framework reads the\n"
        f"BREAKTHROUGH marker and stops driving more turns.\n\n"
        f"If you cannot complete the deliverable in this turn, do NOT emit\n"
        f"BREAKTHROUGH. Output the strongest partial draft you can, and the\n"
        f"framework will follow up with a deepening question."
    )

    # Build a TodoSpec-shaped stub so OracleConsultant's logging/state code works.
    class _TaskTodoStub:
        todo_id = task.id
        title = task.title
        def slug(self_inner): return task.id

    todo_stub = _TaskTodoStub()
    max_turns = int(ctx.get("max_turns", 6))
    per_turn_timeout = int(ctx.get("per_turn_timeout_s", 3600))
    use_codex_driver = bool(ctx.get("use_codex_driver", False))
    runner_log(
        f"{task.id}: oracle deep_reasoning max_turns={max_turns} "
        f"per_turn={per_turn_timeout}s codex_driver={use_codex_driver}"
    )
    run = consultant.deep_reasoning(
        todo_stub, initial_prompt,
        max_turns=max_turns,
        prompt_generator=codex_driven_prompt_generator if use_codex_driver else None,
        per_turn_timeout=per_turn_timeout,
        slug=task.id,
    )
    verdict = run.get("final_verdict", "FAILED")
    runner_log(
        f"{task.id}: oracle verdict={verdict} turns={len(run.get('turns') or [])} "
        f"elapsed={run.get('total_elapsed_seconds', 0)}s"
    )
    if verdict == "FAILED":
        return False, f"oracle deep_reasoning FAILED: {run.get('error','(no error message)')}"

    # Pick the response body to land as the deliverable.
    # NB: oracle_consultant.deep_reasoning stores `response_log_path` (a FILE
    # PATH on disk) in turns[].response, NOT the response text itself. We must
    # read the file to get the actual content. Earlier code wrote the path
    # string into the deliverable, which is exactly what triggered the
    # "Deliverable is only a pair of file paths" gate failure on retry.
    turns = run.get("turns") or []
    body = ""
    chosen_path = ""
    for t in reversed(turns):
        resp_path = (t.get("response") or "").strip()
        if not resp_path:
            continue
        try:
            p = Path(resp_path)
            if p.exists() and p.is_file():
                text = p.read_text(encoding="utf-8", errors="replace").strip()
                if text:
                    body = text
                    chosen_path = resp_path
                    break
        except OSError:
            continue
    if not body:
        return False, f"oracle returned no usable response (verdict={verdict})"
    target.write_text(body + "\n", encoding="utf-8")
    return True, (
        f"wrote {target.relative_to(REPO_ROOT)} ({len(body)} chars) "
        f"via oracle [verdict={verdict}, {len(turns)} turns, src={Path(chosen_path).name}]"
    )


def _run_drafting_task(task: TaskSpec) -> tuple[bool, str]:
    """Codex-first single-deliverable drafting.

    Routing rule:
      - context.use_oracle=True → straight to ChatGPT Project oracle (the
        operator pre-decided this task needs Project-attached files like
        main.pdf / READMEs as deep-reasoning context).
      - else → outreach_codex_track.run_codex_track (codex authors + codex
        self-audits + claude redline hygiene check). On verdict=escalate,
        fall through to oracle deep_reasoning. On verdict=close, copy the
        codex-authored draft to the task's deliverable_paths[0] and let
        the claude_review gate audit it as final.

    Claude is no longer the primary author for any drafting task — its
    only roles in this loop are the redline hygiene check inside
    codex_track and the claude_review gate after the worker returns.
    """
    if (task.context or {}).get("use_oracle"):
        return _run_oracle_drafting_task(task)

    if not task.deliverable_paths:
        return False, "no deliverable_paths configured"
    target = _abs(task.deliverable_paths[0])
    _ensure_parent(target)

    try:
        from outreach_codex_track import run_codex_track  # noqa: PLC0415
    except Exception as exc:
        return False, f"outreach_codex_track import failed: {exc}"

    ctx = task.context or {}
    target_payload = {
        "target_id": task.id,
        "title": task.title,
        "source_type": _infer_source_type(task),
        "source_url": ctx.get("thread") or ctx.get("source_url") or "",
        "summary": ctx.get("summary") or task.title,
        "fields": ctx,
    }

    max_rounds = int(ctx.get("max_rounds", 6))
    wall_clock_s = int(ctx.get("wall_clock_s", 1800))
    runner_log(
        f"{task.id}: codex_track max_rounds={max_rounds} wall_clock={wall_clock_s}s "
        f"(retry={task.retries})"
    )
    retry_ctx = _build_retry_context(task, target)
    result = run_codex_track(
        target_payload,
        max_rounds=max_rounds,
        wall_clock_s=wall_clock_s,
        drafts_dir=DRAFTS_DIR,
        retry_context=retry_ctx,
    )
    runner_log(
        f"{task.id}: codex_track verdict={result.verdict} rounds={result.rounds} "
        f"audit_score={result.audit_score} redline_pass={result.redline_pass} "
        f"transcript={result.transcript_path}"
    )

    if result.verdict == "close" and result.draft_path and result.draft_path.exists():
        body = result.draft_path.read_text(encoding="utf-8")
        target.write_text(body, encoding="utf-8")
        return True, (
            f"wrote {target.relative_to(REPO_ROOT)} ({len(body)} chars) "
            f"via codex_track [score={result.audit_score} rounds={result.rounds}]"
        )

    if result.verdict == "escalate":
        runner_log(
            f"{task.id}: codex_track escalated → oracle deep_reasoning "
            f"(reason={result.obstruction_reason[:200]})"
        )
        return _run_oracle_drafting_task(task)

    return False, (
        f"codex_track verdict={result.verdict}: "
        f"{result.obstruction_reason or 'no draft produced'}"
    )


def _codex_oneshot(prompt: str, *, timeout: int, log_tag: str) -> tuple[bool, str]:
    """Single-shot codex exec returning plain stdout text.

    Used by _run_paper_trade for each step (summary / questions / pointers).
    Returns (ok, body_text). body_text falls back to raw codex stdout when
    the response is not JSON-wrapped, since paper-trade steps don't carry
    a verdict envelope.
    """
    try:
        from outreach_codex_track import codex_exec  # noqa: PLC0415
    except Exception as exc:
        return False, f"codex_exec import failed: {exc}"
    res = codex_exec(prompt, timeout=timeout, log_tag=log_tag)
    if not res.ok:
        return False, f"codex rc={res.rc} err={res.error or '(none)'}"
    body = ""
    if isinstance(res.parsed, dict):
        for key in ("text", "body", "draft", "draft_text", "content", "message", "summary"):
            v = res.parsed.get(key)
            if isinstance(v, str) and v.strip():
                body = v.strip()
                break
    if not body:
        body = (res.raw_output or "").strip()
    if not body:
        return False, "codex returned empty body"
    return True, body


def _run_paper_trade(task: TaskSpec) -> tuple[bool, str]:
    """Paper-trade pipeline: PDF download → summary → annotated questions → library pointers."""
    ctx = task.context or {}
    zenodo_url = (ctx.get("zenodo_url") or "").strip()
    pdf_local = ctx.get("zenodo_local_pdf") or ""
    if not zenodo_url:
        return False, "context.zenodo_url not set"
    if not pdf_local:
        return False, "context.zenodo_local_pdf not set"

    # Step 1: download PDF if missing
    pdf_path = _abs(pdf_local)
    _ensure_parent(pdf_path)
    if not pdf_path.exists() or pdf_path.stat().st_size < 50000:
        # Use Zenodo API to find file URL
        record_id = zenodo_url.rstrip("/").split("/")[-1]
        api_url = f"https://zenodo.org/api/records/{record_id}"
        try:
            cp = subprocess.run(
                ["curl", "-fsSL", api_url],
                capture_output=True, text=True, timeout=60,
            )
        except Exception as exc:
            return False, f"zenodo api fetch failed: {exc}"
        if cp.returncode != 0:
            return False, f"zenodo api rc={cp.returncode}: {cp.stderr.strip()[:200]}"
        import json as _json
        try:
            meta = _json.loads(cp.stdout)
        except _json.JSONDecodeError as exc:
            return False, f"zenodo api returned non-JSON: {exc}"
        files = meta.get("files") or []
        pdf_link = ""
        for f in files:
            link = (f.get("links") or {}).get("self") or ""
            if link.lower().endswith(".pdf"):
                pdf_link = link
                break
        if not pdf_link and files:
            # Fallback: first file
            pdf_link = ((files[0].get("links") or {}).get("self") or "")
        if not pdf_link:
            return False, "no file link in zenodo record"
        try:
            cp = subprocess.run(
                ["curl", "-fsSL", "-o", str(pdf_path), pdf_link],
                capture_output=True, text=True, timeout=300,
            )
        except Exception as exc:
            return False, f"pdf download failed: {exc}"
        if cp.returncode != 0:
            return False, f"pdf download rc={cp.returncode}: {cp.stderr.strip()[:200]}"
        runner_log(f"{task.id}: downloaded {pdf_path} ({pdf_path.stat().st_size} bytes)")

    # Step 2: summarize PDF (claude reads via @ syntax)
    deliverables = list(task.deliverable_paths)
    summary_rel = next((d for d in deliverables if "summary" in d.lower()), "")
    questions_rel = next((d for d in deliverables if "question" in d.lower()), "")
    pointers_rel = next((d for d in deliverables if "pointer" in d.lower()), "")
    if not (summary_rel and questions_rel and pointers_rel):
        return False, "deliverable_paths missing summary/questions/pointers entries"

    pdf_text = _extract_pdf_text(pdf_path)
    if not pdf_text:
        return False, "pdf text extraction returned empty"

    constraints = ctx.get("operator_constraints") or []
    constraints_block = "\n".join(f"- {c}" for c in constraints)

    # On retry, give each step the gate's prior failure reason + the file's
    # previous body so codex can target the exact undersize / missing-term gap.
    summary_path = _abs(summary_rel)
    questions_path = _abs(questions_rel)
    pointers_path = _abs(pointers_rel)
    retry_summary = _build_retry_context(task, summary_path)
    retry_questions = _build_retry_context(task, questions_path)
    retry_pointers = _build_retry_context(task, pointers_path)

    def retry_block(hint: str) -> str:
        return f"\n\n# Prior task-level retry feedback\n\n{hint}\n" if hint else ""

    summary_prompt = (
        f"Read the SAIR paper text below and write a concise (1500-3000 char) reading summary "
        f"of the protocol — what Israel measures, the ceiling effect's empirical signature, "
        f"the Wilson CI choice, the saturation-region detection method, and any same-conversation "
        f"axis he treats. Output the summary text directly, plain prose, no preamble, no JSON wrapper.\n\n"
        f"# Constraints\n\n{constraints_block}\n\n"
        f"# Paper text (truncated)\n\n```\n{pdf_text[:60000]}\n```\n"
        f"{retry_block(retry_summary)}"
    )
    ok, body = _codex_oneshot(summary_prompt, timeout=1500, log_tag=f"israel_summary_{task.id}")
    if not ok:
        return False, f"summary step failed: {body}"
    _ensure_parent(summary_path)
    summary_path.write_text(body + "\n", encoding="utf-8")
    runner_log(f"{task.id}: wrote {summary_rel}")

    # Step 3: annotated questions
    q_prompt = (
        f"Based on the SAIR paper summary below, draft annotated questions for the author. "
        f"Each question should reference a specific section / page of his paper and be precise "
        f"enough to be useful, not generic 'I have questions about your protocol'. "
        f"Required topical coverage: Wilson CI choice (pick one or two specific places to ask), "
        f"saturation-region detection (ask about thresholds / how to draw the saturation boundary), "
        f"same-conversation different-prompting-strategy axis (the meta-prompt 40→9100 char observation we shared — "
        f"ask how his framework treats this). Write 600-1500 char total. Output plain text only, no JSON wrapper.\n\n"
        f"# Constraints\n\n{constraints_block}\n\n"
        f"# Summary\n\n{summary_path.read_text(encoding='utf-8')}\n"
        f"{retry_block(retry_questions)}"
    )
    ok, body = _codex_oneshot(q_prompt, timeout=1500, log_tag=f"israel_questions_{task.id}")
    if not ok:
        return False, f"questions step failed: {body}"
    _ensure_parent(questions_path)
    questions_path.write_text(body + "\n", encoding="utf-8")
    runner_log(f"{task.id}: wrote {questions_rel}")

    # Step 4: Lean library pointers (line-anchored, no Lean execution)
    targets_dict = ctx.get("lean_pointer_targets") or {}
    grep_dump = _grep_lean_for_pointers(targets_dict)
    p_prompt = (
        f"Compose a concise document of line-anchored Lean library pointers for Israel. "
        f"Each pointer must be in `path:line:declaration_name` format with one-line context. "
        f"Cover three sections matching `lean_pointer_targets`: Z/21Z CRT split, integer-affine closure / "
        f"non-affine witness, and Sym²/Λ² near-misses. Group by section. Write 1500-3500 char. "
        f"Output plain text only, no JSON wrapper.\n\n"
        f"# Constraints\n\n{constraints_block}\n\n"
        f"# Per-section grep extracts (use these as the source of file:line evidence)\n\n"
        f"```\n{grep_dump[:50000]}\n```\n"
        f"{retry_block(retry_pointers)}"
    )
    ok, body = _codex_oneshot(p_prompt, timeout=1500, log_tag=f"israel_pointers_{task.id}")
    if not ok:
        return False, f"pointers step failed: {body}"
    _ensure_parent(pointers_path)
    pointers_path.write_text(body + "\n", encoding="utf-8")
    runner_log(f"{task.id}: wrote {pointers_rel}")

    return True, "all 4 paper-trade deliverables written (codex)"


def _extract_pdf_text(pdf_path: Path) -> str:
    """Best-effort PDF → text using whichever tool is available. No-op fallback."""
    for tool in (["pdftotext", "-layout", str(pdf_path), "-"],
                 ["pdftotext", str(pdf_path), "-"]):
        try:
            cp = subprocess.run(tool, capture_output=True, text=True, timeout=120)
            if cp.returncode == 0 and cp.stdout.strip():
                return cp.stdout
        except FileNotFoundError:
            continue
        except Exception:
            continue
    return ""


def _grep_lean_for_pointers(targets: dict) -> str:
    """Run grep over the listed lean4 paths and return file:line:line-content lines."""
    out: list[str] = []
    for section, paths in (targets or {}).items():
        out.append(f"### {section}")
        for path in paths:
            base = REPO_ROOT / path
            if base.is_dir():
                # Limited glob — recent files only, keyword-broad search of theorem-like patterns
                try:
                    cp = subprocess.run(
                        ["grep", "-rn", "-E",
                         r"^\s*(theorem|lemma|def|abbrev|structure)\s+\w+",
                         str(base)],
                        capture_output=True, text=True, timeout=60,
                    )
                    if cp.returncode == 0:
                        out.extend(cp.stdout.splitlines()[:80])
                except Exception:
                    pass
            elif base.is_file():
                try:
                    cp = subprocess.run(
                        ["grep", "-n", "-E",
                         r"^\s*(theorem|lemma|def|abbrev|structure)\s+\w+",
                         str(base)],
                        capture_output=True, text=True, timeout=30,
                    )
                    if cp.returncode == 0:
                        out.extend(cp.stdout.splitlines()[:40])
                except Exception:
                    pass
            else:
                out.append(f"  (path missing: {path})")
        out.append("")
    return "\n".join(out)


def _run_code_pr_response(task: TaskSpec) -> tuple[bool, str]:
    """Cannot land code locally without external repo checkout. Mark blocked."""
    return False, (
        f"requires external repo {task.requires_external_repo!r}; "
        f"cannot land code from this host"
    )


_WORKERS = {
    "issue_reply_draft": _run_drafting_task,
    "email_reply_draft": _run_drafting_task,
    "experimental": _run_drafting_task,
    "paper_trade": _run_paper_trade,
    "code_pr_response": _run_code_pr_response,
}


# ---------------------------------------------------------------------------
# orchestrator
# ---------------------------------------------------------------------------


def process_one(task: TaskSpec) -> dict:
    """Claim → run worker → run gate → save status → release."""
    started = time.time()
    if not claim(task.id):
        return {"task_id": task.id, "skipped": "already_claimed"}

    try:
        # Mark in_progress
        task.status = "in_progress"
        task.last_run_iso = _now_iso()
        save_task(task)

        worker = _WORKERS.get(task.type)
        if worker is None:
            return _settle_failure(task, f"no worker for type {task.type!r}", "rejected")

        runner_log(f"{task.id}: running worker {task.type}")
        ok, msg = worker(task)
        if not ok:
            # code_pr_response → blocked, others → retry/rejected
            if task.type == "code_pr_response":
                return _settle_failure(task, msg, "blocked")
            return _settle_failure(task, f"worker failed: {msg}", None)

        runner_log(f"{task.id}: worker ok ({msg}); evaluating gate {task.gate.kind}")
        verdict = outreach_gates.evaluate(task)
        runner_log(
            f"{task.id}: gate verdict passed={verdict.passed} score={verdict.score} "
            f"next={verdict.next_action} reasons={verdict.reasons[:3]}"
        )
        if verdict.passed:
            task.status = "gated_ready"
            task.last_verdict = "pass"
            task.last_reason = "; ".join(verdict.reasons[:3])
            save_task(task)
            return {
                "task_id": task.id,
                "verdict": "pass",
                "score": verdict.score,
                "elapsed_s": round(time.time() - started, 1),
            }
        # Gate failed
        return _settle_failure(
            task,
            f"gate fail: {'; '.join(verdict.reasons[:3])}",
            verdict.next_action,
        )
    finally:
        release(task.id)


def _settle_failure(task: TaskSpec, reason: str, next_action: Optional[str]) -> dict:
    task.last_verdict = "fail"
    task.last_reason = reason
    if next_action == "blocked":
        task.status = "blocked"
    elif next_action == "escalate":
        task.status = "rejected"
    else:
        task.retries += 1
        task.status = "rejected" if task.retries >= task.max_retries else "pending"
    save_task(task)
    runner_log(f"{task.id}: settled status={task.status} retries={task.retries} reason={reason}")
    return {"task_id": task.id, "verdict": "fail", "status": task.status, "reason": reason}


# ---------------------------------------------------------------------------
# selection
# ---------------------------------------------------------------------------


def select_next(*, lean_available: bool = False, allow_external_repo: bool = False) -> Optional[TaskSpec]:
    tasks = list_tasks()
    workable = select_workable(
        tasks, lean_available=lean_available, allow_external_repo=allow_external_repo,
    )
    if not workable:
        return None
    # Skip tasks currently claimed
    for t in workable:
        if not _claim_marker(t.id).exists():
            return t
    return None


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def _install_signal_handlers(stop: dict) -> None:
    def _h(signum, frame):
        stop["stop"] = True

    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            signal.signal(sig, _h)
        except (OSError, ValueError):
            pass


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--loop", action="store_true",
                   help="continuous polling daemon")
    p.add_argument("--once", action="store_true",
                   help="select one workable task, run it, exit")
    p.add_argument("--task-id", default="",
                   help="explicit task id to process (use with --once)")
    p.add_argument("--poll-interval", type=int, default=DEFAULT_POLL_INTERVAL,
                   help=f"seconds between polls when no workable task (default {DEFAULT_POLL_INTERVAL})")
    p.add_argument("--cleanup-only", action="store_true",
                   help="sweep stale claims and exit")
    p.add_argument("--lean-available", action="store_true",
                   help="this host CAN run Lean; un-skip requires_lean tasks")
    p.add_argument("--allow-external-repo", action="store_true",
                   help="this host has external repos checked out; un-block requires_external_repo tasks")
    args = p.parse_args(argv)

    if args.cleanup_only:
        n = cleanup_stale_claims()
        print(f"released {n} stale claim(s)")
        return 0

    if not args.loop and not args.once:
        p.error("specify --loop or --once")

    stop: dict = {"stop": False}
    _install_signal_handlers(stop)

    runner_log(
        f"task_runner starting (loop={args.loop} once={args.once} "
        f"task_id={args.task_id or 'auto'} lean_available={args.lean_available} "
        f"allow_external_repo={args.allow_external_repo})"
    )

    while not stop["stop"]:
        cleanup_stale_claims()

        picked: Optional[TaskSpec] = None
        if args.task_id:
            picked = load_task(args.task_id)
            if picked is None:
                runner_log(f"--task-id {args.task_id} not found, exiting")
                return 1
            ok, why = picked.is_workable_locally(
                lean_available=args.lean_available,
                allow_external_repo=args.allow_external_repo,
            )
            if not ok:
                runner_log(f"--task-id {args.task_id} not workable: {why}; exiting")
                return 1
        else:
            picked = select_next(
                lean_available=args.lean_available,
                allow_external_repo=args.allow_external_repo,
            )

        if picked is None:
            runner_log("no workable task this poll")
            if args.once:
                return 0
            time.sleep(args.poll_interval)
            continue

        result = process_one(picked)
        runner_log(f"result: {result}")

        if args.once:
            return 0

        if args.task_id:
            args.task_id = ""

    runner_log("task_runner exiting (stop signal)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
