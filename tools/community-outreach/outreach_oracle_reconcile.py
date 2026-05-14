#!/usr/bin/env python3
"""Reconcile saved Oracle results back into local gate artifacts.

The browser bridge and the CLI process that submitted a task are intentionally
decoupled. If the submitter times out, is cancelled, or exits after the browser
eventually posts a result, the saved Oracle response should still be consumed
by the pipeline. This reconciler scans durable Oracle sessions/results and
writes recognized freshness-judge verdicts into targets/<slug>/freshness_judge.json.

Deep-research Oracle turns need the same durable handoff. A browser tab may
finish after the Python submitter timed out or was cancelled; in that case the
saved response must still be consumed by Codex/local gates instead of being
left as an orphaned Markdown file. The deep reconciler therefore:

* finds saved Oracle responses for a board target;
* materializes any valid FILE blocks;
* otherwise records the Oracle text as an unverified claim packet;
* appends a synthetic oracle_deep run to outreach_state/<slug>.json so the
  science gate and next prompt generator can continue from the actual result.

It deliberately does not create expected evidence files from prose claims. If
Oracle says "results.json is on disk" but did not return a FILE block, the
science gate remains blocked until a real artifact is produced.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
ORACLE_DIR = SCRIPT_DIR / "outreach_oracle"
SESSIONS_DIR = ORACLE_DIR / "sessions"
RESULTS_DIR = ORACLE_DIR / "results"

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_board_parser import parse_board  # noqa: E402
from outreach_candidate_inbox import add_candidate  # noqa: E402
from outreach_freshness_judge import judge_path, load_judge, record  # noqa: E402
from oracle_consultant import _materialize_file_blocks  # noqa: E402


def _extract_urls(text: str) -> list[str]:
    seen: set[str] = set()
    urls: list[str] = []
    for raw in re.findall(r"https?://[^\s\]\)>,\"']+", text or ""):
        url = raw.rstrip(".,;:")
        if url and url not in seen:
            seen.add(url)
            urls.append(url)
    return urls


def _extract_judge_payload(text: str) -> dict | None:
    text = (text or "").strip()
    if not text:
        return None
    fence = re.search(r"```(?:json)?\s*(.*?)\s*```", text, re.DOTALL | re.IGNORECASE)
    candidates: list[str] = []
    if fence:
        candidates.append(fence.group(1).strip())
    first = text.find("{")
    last = text.rfind("}")
    if first >= 0 and last > first:
        candidates.append(text[first:last + 1])
    decoder = json.JSONDecoder()
    for candidate in candidates:
        try:
            obj = json.loads(candidate)
            if isinstance(obj, dict):
                return obj
        except json.JSONDecodeError:
            pass
    for i, ch in enumerate(text):
        if ch != "{":
            continue
        try:
            obj, _ = decoder.raw_decode(text[i:])
        except json.JSONDecodeError:
            continue
        if isinstance(obj, dict):
            return obj

    lines = [ln.strip().strip("*`#:- ") for ln in text.splitlines() if ln.strip()]
    head = "\n".join(lines[:8])
    verdict = ""
    for line in lines[:8]:
        low = line.lower()
        m = re.match(r"^(verdict\s*[:=-]\s*)?(pass|fail|uncertain)\b", low)
        if m:
            verdict = m.group(2)
            break
        if re.search(r"\bdecision\s*:\s*safe to run\b", low):
            verdict = "pass"
            break
        if re.search(r"\bdecision\s*:\s*not safe to run\b", low):
            verdict = "fail"
            break
        if re.search(r"\bdecision\s*:\s*uncertain\b", low):
            verdict = "uncertain"
            break
        if re.search(r"\b(safe to run|safe for run|safe to enter|safe for automated deep reasoning)\b.*\b(yes|pass|safe)\b", low):
            verdict = "pass"
            break
        if re.search(r"\b(not safe to run|unsafe|do not run|blocked|overtaken|solved|misframed)\b", low):
            verdict = "fail"
            break
        if re.search(r"\b(uncertain|cannot determine|not enough evidence|ambiguous)\b", low):
            verdict = "uncertain"
            break
    if not verdict:
        low_head = head.lower()
        if re.search(r"\b(verdict|decision)\s*[:=-]\s*pass\b", low_head):
            verdict = "pass"
        elif re.search(r"\b(verdict|decision)\s*[:=-]\s*fail\b", low_head):
            verdict = "fail"
        elif re.search(r"\b(verdict|decision)\s*[:=-]\s*uncertain\b", low_head):
            verdict = "uncertain"
        elif re.search(r"\bdecision\s*:\s*safe to run\b", low_head):
            verdict = "pass"
        elif re.search(r"\bdecision\s*:\s*not safe to run\b", low_head):
            verdict = "fail"
        elif re.search(r"\bsafe to run\b.*\b(yes|safe)\b", low_head):
            verdict = "pass"
        elif re.search(r"\b(no public solution|no obvious public solution|no visible public solution|found no public solution|found no visible public solution|no later solution|not resolved)\b", low_head):
            verdict = "pass"
        elif re.search(r"\b(public solution|has been solved|already solved|overtaken|misframed)\b", low_head):
            verdict = "fail"
    if not verdict:
        return None

    summary_lines = [
        ln for ln in lines
        if not re.match(r"^(verdict\s*[:=-]\s*)?(pass|fail|uncertain)\b", ln.lower())
    ]
    summary = " ".join(summary_lines[:4]).strip()
    if len(summary) > 800:
        summary = summary[:797].rstrip() + "..."
    return {
        "verdict": verdict,
        "summary": summary or "(oracle returned a verdict without prose summary)",
        "evidence_urls": _extract_urls(text),
        "notes": "parsed from flexible oracle response",
    }


def _extract_json(text: str) -> dict | None:
    return _extract_judge_payload(text)
    return None


def _iter_session_turns() -> list[dict]:
    rows: list[dict] = []
    for path in sorted(SESSIONS_DIR.glob("*.json")):
        try:
            sess = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        tag = str(sess.get("tag") or "")
        for turn in sess.get("turns") or []:
            if isinstance(turn, dict):
                rows.append({
                    "source_path": path,
                    "conversation_id": sess.get("conversation_id") or path.stem,
                    "tag": tag,
                    "task_id": turn.get("task_id"),
                    "prompt": turn.get("prompt") or "",
                    "response": turn.get("response") or "",
                    "completed_at": turn.get("completed_at") or "",
                    "chatgpt_url": turn.get("chatgpt_url") or "",
                })
    return rows


def _iter_result_files() -> list[dict]:
    rows: list[dict] = []
    for path in sorted(RESULTS_DIR.glob("*.md")):
        text = path.read_text(encoding="utf-8", errors="ignore")
        meta: dict = {}
        response = text
        if text.startswith("<!-- outreach-oracle:"):
            end = text.find("-->")
            if end >= 0:
                raw = text[len("<!-- outreach-oracle:"):end].strip()
                try:
                    meta = json.loads(raw)
                except json.JSONDecodeError:
                    meta = {}
                response = text[end + 3 :].strip()
        rows.append({
            "source_path": path,
            "conversation_id": meta.get("conversation_id") or "",
            "tag": str(meta.get("tag") or ""),
            "task_id": meta.get("task_id") or path.stem,
            "prompt": "",
            "response": response,
            "completed_at": meta.get("completed_at") or "",
            "chatgpt_url": meta.get("chatgpt_url") or "",
        })
    return rows


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _target_dir(slug: str) -> Path:
    return SCRIPT_DIR / "targets" / slug


def _state_path(slug: str) -> Path:
    return SCRIPT_DIR / "outreach_state" / f"{slug}.json"


def _load_state(slug: str) -> dict:
    try:
        return json.loads(_state_path(slug).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def _write_state(slug: str, state: dict) -> None:
    path = _state_path(slug)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    tmp.replace(path)


def _compact(text: str, limit: int = 1800) -> str:
    text = re.sub(r"\s+", " ", text or "").strip()
    if len(text) <= limit:
        return text
    return text[: limit - 3].rstrip() + "..."


def _slug_for_todo_id(todo_id: str) -> str:
    todo = parse_board(SCRIPT_DIR / "RESEARCH_BOARD.md").get(todo_id)
    return todo.slug() if todo else ""


def _row_mentions_todo(row: dict, todo_id: str, slug: str) -> bool:
    haystack = "\n".join(str(row.get(k) or "") for k in ("tag", "task_id", "source_path"))
    if todo_id and re.search(rf"\b{re.escape(todo_id)}\b", haystack):
        return True
    if slug and slug in haystack:
        return True
    # Retry result files often only have conversation_id. Map that back through
    # outreach_state/conv_*.json or target state parent_task_id.
    conv = str(row.get("conversation_id") or "")
    if conv:
        conv_state_path = SCRIPT_DIR / "outreach_state" / f"{conv}.json"
        try:
            conv_state = conv_state_path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            conv_state = ""
        if todo_id and todo_id in conv_state:
            return True
        if slug and slug in conv_state:
            return True
    return False


def _deep_tag_to_todo_id(row: dict) -> str:
    tag = str(row.get("tag") or "")
    m = re.search(r"\b(T-\d+)\s*:\s*deep\b", tag)
    if m:
        return m.group(1)
    task_id = str(row.get("task_id") or "")
    for text in (tag, task_id):
        m = re.search(r"\b(T-\d+)\b", text)
        if m:
            return m.group(1)
    conv = str(row.get("conversation_id") or "")
    if conv:
        conv_state_path = SCRIPT_DIR / "outreach_state" / f"{conv}.json"
        try:
            conv_state = json.loads(conv_state_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            conv_state = {}
        for task in conv_state.get("pending_review_tasks") or []:
            if not isinstance(task, dict):
                continue
            parent = str(task.get("parent_task_id") or "")
            m = re.search(r"deep_([a-z0-9_]+)_t\d+", parent)
            if not m:
                continue
            parent_slug = m.group(1)
            for tid, todo in parse_board(SCRIPT_DIR / "RESEARCH_BOARD.md").items():
                if todo.slug() == parent_slug:
                    return tid
    return ""


def _extract_claimed_artifact_names(text: str) -> list[str]:
    names: list[str] = []
    seen: set[str] = set()
    for name in re.findall(r"\b[A-Za-z0-9_./-]+\.(?:json|csv|py|md|tex|lean)\b", text or ""):
        clean = name.strip().strip("`.,;:")
        if not clean or clean in seen:
            continue
        seen.add(clean)
        names.append(clean)
    return names[:40]


def _write_oracle_claim_packet(
    todo_id: str,
    slug: str,
    row: dict,
    *,
    append_to_research: bool = True,
) -> str:
    target_dir = _target_dir(slug)
    target_dir.mkdir(parents=True, exist_ok=True)
    response = str(row.get("response") or "").strip()
    digest = hashlib.sha256(response.encode("utf-8")).hexdigest()[:12]
    packet_path = target_dir / f"oracle_claim_packet_{digest}.md"
    claimed = _extract_claimed_artifact_names(response)
    missing_claims: list[str] = []
    for name in claimed:
        p = Path(name)
        if not p.is_absolute():
            if "/" in name:
                p = SCRIPT_DIR.parents[1] / p
            else:
                p = target_dir / name
        if not p.exists():
            missing_claims.append(name)
    body = "\n".join([
        f"# Unverified Oracle Claim Packet - {todo_id} ({slug})",
        "",
        f"Reconciled: {_now_iso()}",
        f"Source result: {row.get('source_path')}",
        f"Conversation: {row.get('conversation_id') or '(unknown)'}",
        f"Task: {row.get('task_id') or '(unknown)'}",
        f"ChatGPT URL: {row.get('chatgpt_url') or '(unknown)'}",
        "",
        "## Gate Status",
        "",
        "This packet preserves a late Oracle response for Codex/local-gate processing.",
        "It is not accepted as evidence unless the referenced artifacts exist on disk or are supplied as valid FILE blocks.",
        "",
        "## Claimed Artifacts",
        "",
        *(f"- {name}" for name in (claimed or ["(none detected)"])),
        "",
        "## Claimed Artifacts Missing On Disk",
        "",
        *(f"- {name}" for name in (missing_claims or ["(none detected)"])),
        "",
        "## Oracle Response",
        "",
        response,
        "",
    ])
    packet_path.write_text(body, encoding="utf-8")

    if append_to_research:
        research_md = target_dir / "research.md"
        section = "\n".join([
            "",
            "## Reconciled Late Oracle Result",
            "",
            f"Reconciled: {_now_iso()}",
            f"Claim packet: `{packet_path.relative_to(SCRIPT_DIR.parents[1])}`",
            f"Conversation: `{row.get('conversation_id') or '(unknown)'}`",
            "",
            "Codex/gate note: this late Oracle result is preserved as an unverified claim packet. Do not treat prose claims of created files as evidence; require real disk artifacts or valid FILE blocks.",
            "",
            "Summary:",
            "",
            _compact(response, 2200),
            "",
        ])
        if research_md.exists():
            prior = research_md.read_text(encoding="utf-8", errors="replace")
            if str(packet_path.relative_to(SCRIPT_DIR.parents[1])) not in prior:
                research_md.write_text(prior.rstrip() + "\n" + section, encoding="utf-8")
        else:
            research_md.write_text(
                f"# Reconciled Oracle Research - {todo_id} ({slug})\n" + section,
                encoding="utf-8",
            )
    return str(packet_path.relative_to(SCRIPT_DIR.parents[1]))


def _is_transport_stub_response(text: str) -> bool:
    stripped = (text or "").strip()
    if not stripped:
        return True
    lowered = stripped.lower()
    markers = (
        "error: task cancelled by server",
        "error (re-extract):",
        "error: empty response",
        "error: no assistant output after",
        "empty response (timeout or extraction failure)",
        "no assistant output after",
        "re-extract: nothing meaningful",
        "re-extract: empty response",
        "server unreachable",
    )
    if any(lowered.startswith(marker) for marker in markers):
        return True
    return len(stripped) < 80 and "cancelled" in lowered and "server" in lowered


def _append_deep_run_state(todo_id: str, slug: str, row: dict, *, artifacts: list[str], packet_path: str) -> None:
    state = _load_state(slug)
    state.setdefault("schema_version", "community-outreach-state-v3-research-board")
    state.setdefault("todo_id", todo_id)
    state.setdefault("slug", slug)
    runs = state.get("oracle_deep_runs")
    if not isinstance(runs, list):
        runs = []
    response_path = str(row.get("source_path") or "")
    run_id = f"reconciled_{slug}_{int(time.time())}"
    marker = {
        "run_id": run_id,
        "todo_id": todo_id,
        "conversation_id": row.get("conversation_id") or "",
        "chatgpt_url": row.get("chatgpt_url") or "",
        "turns": [
            {
                "turn": 0,
                "prompt": "(late Oracle result reconciled from durable browser output)",
                "response": response_path,
                "response_chars": len(str(row.get("response") or "")),
                "elapsed_seconds": 0,
                "task_id": row.get("task_id") or "",
                "error": "",
                "prompt_source": "reconcile",
                "materialized_artifacts": artifacts,
                "claim_packet": packet_path,
                "contribution": "Late Oracle output reconciled for Codex/local-gate processing. Prose claims remain unverified unless backed by disk artifacts.",
                "evaluator_verdict": "continue",
                "evaluator_reason": "Reconciled output needs artifact materialization or repair follow-up.",
            }
        ],
        "final_verdict": "RECONCILED",
        "total_elapsed_seconds": 0,
        "stopped_at_turn": 0,
        "run_started_at": row.get("completed_at") or _now_iso(),
        "run_completed_at": _now_iso(),
        "max_turns": 0,
    }
    existing_keys = {
        (str(run.get("conversation_id") or ""), str(((run.get("turns") or [{}])[0] or {}).get("task_id") or ""))
        for run in runs
        if isinstance(run, dict)
    }
    key = (str(marker["conversation_id"] or ""), str(row.get("task_id") or ""))
    if key not in existing_keys:
        runs.append(marker)
    state["oracle_deep_runs"] = runs
    state["latest_oracle_deep_verdict"] = "RECONCILED"
    state["latest_oracle_deep_turns"] = 1
    state["latest_oracle_deep_at"] = _now_iso()
    state["latest_oracle_deep_conversation_id"] = row.get("conversation_id") or ""
    state["latest_oracle_deep_url"] = row.get("chatgpt_url") or ""
    history = state.get("action_history")
    if not isinstance(history, list):
        history = []
    history.append({
        "timestamp": _now_iso(),
        "stage": "B-oracle-deep-reconcile",
        "round": len(runs),
        "action": "reconcile late oracle deep result",
        "detail": f"task={row.get('task_id') or ''} artifacts={len(artifacts)} packet={packet_path}",
    })
    state["action_history"] = history[-100:]
    _write_state(slug, state)


def _maybe_add_side_result_candidate(todo_id: str, slug: str, row: dict) -> dict | None:
    response = str(row.get("response") or "")
    low = response.lower()
    if "collision-free subslab" not in low and "collision-free linear subfamily" not in low:
        return None
    todos = parse_board(SCRIPT_DIR / "RESEARCH_BOARD.md")
    todo = todos.get(todo_id)
    if not todo:
        return None
    candidate = {
        "title": f"Corrected bridge lemma for {todo.title}",
        "source_url": todo.source,
        "type": "OBSTRUCTION",
        "statement": (
            "Find and prove a collision-free linear subfamily or corrected Myhill-Nerode bridge after "
            f"the full consecutive-slab bridge for {todo.title} was reported to fail in Oracle deep reasoning."
        ),
        "rationale": (
            "The late Oracle result appears to refute an over-strong bridge lemma while identifying a useful "
            "next target: a corrected linear subslab or alternative residual family. This should be gated as a "
            "follow-up mathematical target, not silently discarded."
        ),
        "untouched_evidence": (
            "Generated internally from an unverified Oracle claim packet while the parent arXiv problem remains "
            "open/current as the tracked public source. This is fresh internal follow-up evidence, not an external "
            "closure claim; source audit must be rechecked before writeback."
        ),
        "omega_fit_detail": (
            "Finite-state Myhill-Nerode certificates, residual minimization, and explicit suffix witnesses fit "
            "Automath/Omega's auditable computation style; any bridge to the main paper can be decided after a "
            "verified subfamily is found."
        ),
        "first_attack_step": (
            "Materialize and verify the reported counterexample, then search for the largest collision-free "
            "linear slab and emit reproducible suffix certificates."
        ),
        "final_display_form": "short research note or author email after operator approval",
        "success_gate": (
            "A verified counterexample packet or corrected linear bridge lemma must exist on disk with results.json, "
            "verifier code, and a research.md explanation before any outreach."
        ),
        "fit_score": 8,
        "topic_score": 8,
        "effort_estimate_days": 7,
        "risk_level": "medium",
    }
    return add_candidate(candidate, source=f"oracle_side_result:{todo_id}:{slug}")


def reconcile_deep(*, todo_id: str = "", force: bool = False, add_side_candidates: bool = True) -> dict:
    todos = parse_board(SCRIPT_DIR / "RESEARCH_BOARD.md")
    rows = _iter_session_turns() + _iter_result_files()
    rows.sort(key=lambda r: str(r.get("completed_at") or ""))
    written: list[dict] = []
    skipped: list[dict] = []
    target_ids = [todo_id] if todo_id else list(todos)
    for tid in target_ids:
        todo = todos.get(tid)
        if not todo:
            skipped.append({"todo_id": tid, "reason": "todo not found"})
            continue
        slug = todo.slug()
        matched = []
        for r in rows:
            direct_tid = _deep_tag_to_todo_id(r)
            if direct_tid == tid:
                matched.append(r)
                continue
            if todo_id and not direct_tid and _row_mentions_todo(r, tid, slug):
                matched.append(r)
        matched = [
            r for r in matched
            if str(r.get("response") or "").strip()
            and not _is_transport_stub_response(str(r.get("response") or ""))
        ]
        if not matched:
            skipped.append({"todo_id": tid, "reason": "no non-transport deep oracle rows found"})
            continue
        row = matched[-1]
        target_dir = _target_dir(slug)
        already = sorted(target_dir.glob("oracle_claim_packet_*.md"))
        if already and not force:
            latest = max(already, key=lambda p: p.stat().st_mtime)
            existing_text = latest.read_text(encoding="utf-8", errors="replace")
            if str(row.get("task_id") or "") and str(row.get("task_id") or "") in existing_text:
                skipped.append({"todo_id": tid, "reason": "latest deep row already reconciled", "source": str(row["source_path"])})
                continue
        artifacts = _materialize_file_blocks(str(row.get("response") or ""))
        target_research = f"tools/community-outreach/targets/{slug}/research.md"
        packet_path = _write_oracle_claim_packet(
            tid,
            slug,
            row,
            append_to_research=target_research not in set(artifacts),
        )
        _append_deep_run_state(tid, slug, row, artifacts=artifacts, packet_path=packet_path)
        side = None
        if add_side_candidates:
            try:
                side = _maybe_add_side_result_candidate(tid, slug, row)
            except Exception as exc:  # noqa: BLE001
                side = {"error": str(exc)}
        written.append({
            "todo_id": tid,
            "slug": slug,
            "source": str(row["source_path"]),
            "conversation_id": row.get("conversation_id") or "",
            "task_id": row.get("task_id") or "",
            "materialized_artifacts": artifacts,
            "claim_packet": packet_path,
            "side_candidate_id": (side or {}).get("candidate_id") if isinstance(side, dict) else "",
            "side_candidate_status": (side or {}).get("status") if isinstance(side, dict) else "",
        })
    return {"written": written, "skipped": skipped}


def _freshness_tag_to_todo_id(row: dict) -> str:
    tag = str(row.get("tag") or "")
    m = re.search(r"freshness-judge-(T-\d+)", tag)
    if m:
        return m.group(1)
    task_id = str(row.get("task_id") or "")
    if "freshness" in task_id:
        m = re.search(r"(T-\d+)", task_id)
        if m:
            return m.group(1)
    return ""


def reconcile_freshness(*, force: bool = False) -> dict:
    todos = parse_board(SCRIPT_DIR / "RESEARCH_BOARD.md")
    rows = _iter_session_turns() + _iter_result_files()
    rows.sort(key=lambda r: str(r.get("completed_at") or ""))
    written: list[dict] = []
    skipped: list[dict] = []
    for row in rows:
        todo_id = _freshness_tag_to_todo_id(row)
        if not todo_id:
            continue
        todo = todos.get(todo_id)
        if not todo:
            skipped.append({"todo_id": todo_id, "reason": "todo not found", "source": str(row["source_path"])})
            continue
        obj = _extract_json(str(row.get("response") or ""))
        if not obj:
            skipped.append({"todo_id": todo_id, "reason": "no json", "source": str(row["source_path"])})
            continue
        verdict = str(obj.get("verdict") or "").strip().lower()
        if verdict not in {"pass", "fail", "uncertain"}:
            skipped.append({"todo_id": todo_id, "reason": f"bad verdict {verdict!r}", "source": str(row["source_path"])})
            continue
        existing, errors = load_judge(todo.slug())
        if existing and not force:
            skipped.append({"todo_id": todo_id, "reason": "judge exists", "source": str(row["source_path"])})
            continue
        evidence = obj.get("evidence_urls") or []
        if not isinstance(evidence, list):
            evidence = []
        path = record(
            todo.slug(),
            verdict=verdict,
            judge="oracle_reconcile",
            summary=str(obj.get("summary") or "(oracle returned no summary)"),
            evidence_urls=[str(u) for u in evidence],
            notes=str(obj.get("notes") or ""),
        )
        written.append({
            "todo_id": todo_id,
            "slug": todo.slug(),
            "verdict": verdict,
            "path": str(path.relative_to(SCRIPT_DIR)),
            "source": str(row["source_path"]),
        })
    return {"written": written, "skipped": skipped}


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--freshness", action="store_true", help="reconcile freshness judge results")
    p.add_argument("--deep", action="store_true", help="reconcile deep-research Oracle results")
    p.add_argument("--todo-id", default="", help="limit deep reconciliation to one T-NN")
    p.add_argument("--no-side-candidates", action="store_true", help="do not add follow-up candidates for side results")
    p.add_argument("--force", action="store_true", help="overwrite existing judge files")
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)
    if args.deep:
        payload = reconcile_deep(
            todo_id=args.todo_id,
            force=args.force,
            add_side_candidates=not args.no_side_candidates,
        )
    else:
        payload = reconcile_freshness(force=args.force)
    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        for row in payload["written"]:
            if args.deep:
                print(f"reconciled {row['todo_id']} -> {row['claim_packet']}")
                if row.get("materialized_artifacts"):
                    print(f"  materialized: {', '.join(row['materialized_artifacts'])}")
                if row.get("side_candidate_id"):
                    print(f"  side candidate: {row['side_candidate_id']} ({row.get('side_candidate_status')})")
            else:
                print(f"wrote {row['todo_id']} {row['verdict']} -> {row['path']}")
        for row in payload["skipped"][:20]:
            print(f"skip {row.get('todo_id')}: {row.get('reason')}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
