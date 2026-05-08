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
# claude exec helper
# ---------------------------------------------------------------------------


def _claude(prompt: str, *, timeout: int, log_tag: str) -> tuple[bool, str, int]:
    try:
        from outreach_claude_exec import claude_exec  # noqa: PLC0415
    except Exception as exc:
        runner_log(f"outreach_claude_exec import failed: {exc}")
        return False, str(exc), -1
    return claude_exec(
        prompt,
        timeout=timeout,
        log_tag=log_tag,
        log_dir=TASK_RUNNER_LOG_DIR,
        repo_root=REPO_ROOT,
    )


# ---------------------------------------------------------------------------
# workers per task type
# ---------------------------------------------------------------------------


def _abs(rel: str) -> Path:
    p = Path(rel)
    return p if p.is_absolute() else (REPO_ROOT / p)


def _ensure_parent(p: Path) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)


_DRAFTING_PROMPT = """You are drafting a single deliverable for a specific operator commitment. Output ONLY the deliverable contents — no surrounding commentary, no markdown fence around the whole document, no "Here is the draft" preamble.

# Task

{title}

# Context (do not invent facts beyond what is stated here)

```
{context_json}
```

# Hard constraints

{constraints}

# Required deliverable

Write to `{deliverable_path}`.

The constraints are not suggestions. The output must be ready for the operator to review, copy-paste, and send. Audience is the named external party in `context.thread` or `context.external_party` (if any) — write to them directly.

Begin the deliverable now. Do not preface.
"""


_DRAFTING_RETRY_PROMPT = """You previously produced a draft for this task that did NOT pass the gate review. Below is the gate's verdict (specific reasons it failed) and your previous draft. Produce a NEW draft that fixes the failures while keeping the parts that were OK. Do NOT repeat the same mistake.

# Task

{title}

# Context (do not invent facts beyond what is stated here)

```
{context_json}
```

# Hard constraints

{constraints}

# Previous gate verdict (this is what failed last time — fix THESE)

```
{prev_gate_reason}
```

# Previous draft (full text — for reference; do not paste back unchanged)

```
{prev_draft}
```

# Required deliverable

Write to `{deliverable_path}`. Output ONLY the new draft, no preamble.
"""


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
        f"# Required deliverable\n\n"
        f"Produce the final draft suitable for {ctx.get('thread', 'the named external party')}.\n"
        f"Output the deliverable as the response body (no preamble). The Project's "
        f"attached files (main.pdf, MAIN_PAPER_INDEX.md, READMEs, PROGRAM_BOARD.md) "
        f"are available — cite them where relevant for fidelity.\n\n"
        f"When you have a substantive result, mark it with the literal token "
        f"BREAKTHROUGH on its own line; the framework uses that to stop multi-turn "
        f"driving."
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

    # Pick the response body to land as the deliverable. Prefer the BREAKTHROUGH
    # turn's response; fall back to last non-empty turn.
    turns = run.get("turns") or []
    body = ""
    for t in reversed(turns):
        resp = (t.get("response") or "").strip()
        if resp:
            body = resp
            break
    if not body:
        return False, f"oracle returned no usable response (verdict={verdict})"
    target.write_text(body + "\n", encoding="utf-8")
    return True, (
        f"wrote {target.relative_to(REPO_ROOT)} ({len(body)} chars) "
        f"via oracle [verdict={verdict}, {len(turns)} turns]"
    )


def _run_drafting_task(task: TaskSpec) -> tuple[bool, str]:
    """Single-deliverable drafting tasks.

    Routing rule:
      - context.use_oracle=True → ChatGPT Project oracle (deep reasoning)
        delegated to _run_oracle_drafting_task above.
      - else → local claude (with retry-aware feedback prompt when retrying).
    """
    if (task.context or {}).get("use_oracle"):
        return _run_oracle_drafting_task(task)

    if not task.deliverable_paths:
        return False, "no deliverable_paths configured"
    target = _abs(task.deliverable_paths[0])
    _ensure_parent(target)

    constraints = task.context.get("operator_constraints") or []
    if not isinstance(constraints, list):
        constraints = [str(constraints)]
    constraints_block = "\n".join(f"- {c}" for c in constraints) or "(none beyond context fidelity)"

    import json as _json

    is_retry = task.retries > 0 and target.exists() and bool(task.last_reason)
    if is_retry:
        try:
            prev_draft = target.read_text(encoding="utf-8")
        except OSError:
            prev_draft = ""
        prompt = _DRAFTING_RETRY_PROMPT.format(
            title=task.title,
            context_json=_json.dumps(task.context, ensure_ascii=False, indent=2),
            constraints=constraints_block,
            prev_gate_reason=task.last_reason or "(no recorded reason)",
            prev_draft=prev_draft[:25000],
            deliverable_path=task.deliverable_paths[0],
        )
        log_tag = f"draft_retry{task.retries}_{task.id}"
        runner_log(f"{task.id}: retry #{task.retries} — feeding prior draft + gate reason back to claude")
    else:
        prompt = _DRAFTING_PROMPT.format(
            title=task.title,
            context_json=_json.dumps(task.context, ensure_ascii=False, indent=2),
            constraints=constraints_block,
            deliverable_path=task.deliverable_paths[0],
        )
        log_tag = f"draft_{task.id}"

    ok, stdout, rc = _claude(prompt, timeout=2400, log_tag=log_tag)
    if not ok:
        return False, f"claude exec rc={rc} output_head={(stdout or '')[:200]}"

    body = (stdout or "").strip()
    if not body:
        return False, "claude returned empty body"
    target.write_text(body + "\n", encoding="utf-8")
    return True, f"wrote {target.relative_to(REPO_ROOT)} ({len(body)} chars){' [retry]' if is_retry else ''}"


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

    summary_prompt = (
        f"Read the SAIR paper text below and write a concise (1500-3000 char) reading summary "
        f"of the protocol — what Israel measures, the ceiling effect's empirical signature, "
        f"the Wilson CI choice, the saturation-region detection method, and any same-conversation "
        f"axis he treats. Output the summary directly, no preamble.\n\n"
        f"# Constraints\n\n{constraints_block}\n\n"
        f"# Paper text (truncated)\n\n```\n{pdf_text[:60000]}\n```\n"
    )
    ok, stdout, _ = _claude(summary_prompt, timeout=1500, log_tag=f"israel_summary_{task.id}")
    if not ok or not stdout.strip():
        return False, f"summary step failed: ok={ok}"
    summary_path = _abs(summary_rel)
    _ensure_parent(summary_path)
    summary_path.write_text(stdout.strip() + "\n", encoding="utf-8")
    runner_log(f"{task.id}: wrote {summary_rel}")

    # Step 3: annotated questions
    q_prompt = (
        f"Based on the SAIR paper summary below, draft annotated questions for the author. "
        f"Each question should reference a specific section / page of his paper and be precise "
        f"enough to be useful, not generic 'I have questions about your protocol'. "
        f"Required topical coverage: Wilson CI choice (pick one or two specific places to ask), "
        f"saturation-region detection (ask about thresholds / how to draw the saturation boundary), "
        f"same-conversation different-prompting-strategy axis (the meta-prompt 40→9100 char observation we shared — "
        f"ask how his framework treats this). Write 600-1500 char total. Output text only.\n\n"
        f"# Constraints\n\n{constraints_block}\n\n"
        f"# Summary\n\n{summary_path.read_text(encoding='utf-8')}\n"
    )
    ok, stdout, _ = _claude(q_prompt, timeout=1500, log_tag=f"israel_questions_{task.id}")
    if not ok or not stdout.strip():
        return False, f"questions step failed: ok={ok}"
    q_path = _abs(questions_rel)
    _ensure_parent(q_path)
    q_path.write_text(stdout.strip() + "\n", encoding="utf-8")
    runner_log(f"{task.id}: wrote {questions_rel}")

    # Step 4: Lean library pointers (line-anchored, no Lean execution)
    targets_dict = ctx.get("lean_pointer_targets") or {}
    grep_dump = _grep_lean_for_pointers(targets_dict)
    p_prompt = (
        f"Compose a concise document of line-anchored Lean library pointers for Israel. "
        f"Each pointer must be in `path:line:declaration_name` format with one-line context. "
        f"Cover three sections matching `lean_pointer_targets`: Z/21Z CRT split, integer-affine closure / "
        f"non-affine witness, and Sym²/Λ² near-misses. Group by section. Write 1500-3500 char.\n\n"
        f"# Constraints\n\n{constraints_block}\n\n"
        f"# Per-section grep extracts (use these as the source of file:line evidence)\n\n"
        f"```\n{grep_dump[:50000]}\n```\n"
    )
    ok, stdout, _ = _claude(p_prompt, timeout=1500, log_tag=f"israel_pointers_{task.id}")
    if not ok or not stdout.strip():
        return False, f"pointers step failed: ok={ok}"
    p_path = _abs(pointers_rel)
    _ensure_parent(p_path)
    p_path.write_text(stdout.strip() + "\n", encoding="utf-8")
    runner_log(f"{task.id}: wrote {pointers_rel}")

    return True, "all 4 paper-trade deliverables written"


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
