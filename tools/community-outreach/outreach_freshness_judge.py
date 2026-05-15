#!/usr/bin/env python3
"""Freshness/currentness gate for outreach targets.

Preflight requires targets with profile.freshness_required or
profile.oracle_judge_required to have targets/<slug>/freshness_judge.json with
verdict=pass before the research loop may spend deep-reasoning cycles.

This module is deliberately conservative. By default it only reports missing
judges. Recording a pass/fail is an explicit operator action, or a future Oracle
judge can write the same schema after checking current literature/source state.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import time
import urllib.request
import sys
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
TARGETS_DIR = SCRIPT_DIR / "targets"
BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_board_parser import parse_board  # noqa: E402
from outreach_profile import load_profile  # noqa: E402
from outreach_preflight import judge_board  # noqa: E402

ORACLE_SERVER_URL = os.environ.get("OUTREACH_ORACLE_SERVER_URL", "http://127.0.0.1:8766")


ORACLE_PROMPT = """You are doing a short source audit for an automated math-research supervisor.

Task: decide whether the target below is suitable to start internal research work now.
Do not solve the math problem. Only check public/current source status:
source exists, statement is inspectable, and no obvious public update already solves or invalidates it.

Write a brief memo in normal prose. Include source URLs you checked.
End with one clear line:
Decision: safe to run
or
Decision: not safe to run
or
Decision: uncertain

Target:
{target_json}
"""


def _clip(text: str, limit: int) -> str:
    text = " ".join(str(text or "").split())
    if len(text) <= limit:
        return text
    return text[: max(0, limit - 3)].rstrip() + "..."


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def judge_path(slug: str) -> Path:
    return TARGETS_DIR / slug / "freshness_judge.json"


def load_judge(slug: str) -> tuple[dict | None, list[str]]:
    path = judge_path(slug)
    if not path.exists():
        return None, [f"missing {path.relative_to(SCRIPT_DIR)}"]
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return None, [f"unreadable {path.relative_to(SCRIPT_DIR)}: {exc}"]
    errors = []
    if data.get("verdict") not in {"pass", "fail", "uncertain"}:
        errors.append("verdict must be pass|fail|uncertain")
    elif data.get("verdict") != "pass":
        errors.append(f"verdict is {data.get('verdict')!r}, expected pass")
    if not data.get("checked_at"):
        errors.append("missing checked_at")
    if not data.get("judge"):
        errors.append("missing judge")
    if not data.get("summary"):
        errors.append("missing summary")
    return data, errors


def required_targets() -> list[dict]:
    todos = parse_board(BOARD_PATH)
    out = []
    for todo in todos.values():
        profile, errors = load_profile(todo.slug())
        if profile is None or errors:
            continue
        if not (profile.freshness_required or profile.oracle_judge_required):
            continue
        judge, judge_errors = load_judge(todo.slug())
        out.append({
            "todo_id": todo.todo_id,
            "slug": todo.slug(),
            "title": todo.title,
            "source_url": todo.source,
            "required": True,
            "ok": judge is not None and not judge_errors and judge.get("verdict") == "pass",
            "judge": judge,
            "errors": judge_errors,
        })
    return out


def auto_judge(*, top: int, timeout_s: int, retry_uncertain: bool = False) -> dict:
    scores = {r.todo_id: r.score for r in judge_board()}
    rows = []
    for r in required_targets():
        if r.get("ok"):
            continue
        judge = r.get("judge")
        errors = r.get("errors") or []
        # Do not repeatedly spend Oracle budget on targets that already have a
        # fail/uncertain verdict. Those are deliberate gates for operator/PI
        # review, not missing data. Supervisor harness mode may opt in to
        # retrying `uncertain` when the whole board is otherwise blocked.
        if isinstance(judge, dict) and judge.get("verdict") == "fail":
            continue
        if (
            isinstance(judge, dict)
            and judge.get("verdict") == "uncertain"
            and not retry_uncertain
        ):
            continue
        if errors and not any("missing" in str(e).lower() or "unreadable" in str(e).lower() for e in errors):
            continue
        rows.append(r)
    rows.sort(key=lambda r: (-(scores.get(str(r.get("todo_id")), 0)), str(r.get("todo_id"))))
    results = []
    for row in rows[:top]:
        todo_id = str(row.get("todo_id") or "")
        ok, msg = judge_with_oracle(todo_id, timeout_s=timeout_s)
        results.append({
            "todo_id": todo_id,
            "slug": row.get("slug"),
            "ok": ok,
            "message": msg,
        })
    return {"processed": len(results), "retry_uncertain": retry_uncertain, "results": results}


def record(
    slug: str,
    *,
    verdict: str,
    judge: str,
    summary: str,
    evidence_urls: list[str],
    notes: str = "",
) -> Path:
    if verdict not in {"pass", "fail", "uncertain"}:
        raise ValueError("verdict must be pass|fail|uncertain")
    path = judge_path(slug)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema_version": "outreach-freshness-judge-v1",
        "slug": slug,
        "verdict": verdict,
        "judge": judge,
        "checked_at": _now_iso(),
        "summary": summary,
        "evidence_urls": evidence_urls,
        "notes": notes,
    }
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return path


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


def _poll_oracle_result(task_id: str, *, timeout_s: int) -> tuple[dict | None, str]:
    started = time.time()
    while time.time() - started < timeout_s:
        try:
            result = _http_get(f"{ORACLE_SERVER_URL}/result/{task_id}", timeout=10)
        except Exception:
            time.sleep(5)
            continue
        if result.get("status") == "cancelled":
            return result, f"oracle task cancelled: {task_id}"
        if result.get("response"):
            return result, ""
        time.sleep(5)
    return None, f"oracle timeout after {timeout_s}s for {task_id}"


def _retry_oracle_result(*, task_id: str, conversation_id: str, timeout_s: int) -> tuple[dict | None, str]:
    if not conversation_id:
        return None, "oracle retry unavailable: no conversation_id"
    try:
        retry = _http_post(
            f"{ORACLE_SERVER_URL}/retry",
            {"task_id": task_id, "conversation_id": conversation_id, "tag": "freshness-retry"},
            timeout=15,
        )
    except Exception as exc:
        return None, f"oracle retry submit failed: {exc}"
    retry_task_id = str(retry.get("task_id") or "")
    if not retry_task_id:
        return None, f"oracle retry returned no task_id: {retry}"
    return _poll_oracle_result(retry_task_id, timeout_s=timeout_s)


def _submit_freshness_prompt(prompt: str, *, todo_id: str, retry_index: int = 0) -> tuple[str, str, str]:
    tag = f"freshness-judge-{todo_id}" if retry_index <= 0 else f"freshness-judge-{todo_id}-fresh-retry-{retry_index}"
    resp = _http_post(f"{ORACLE_SERVER_URL}/submit", {
        "prompt": prompt,
        "tag": tag,
    }, timeout=15)
    task_id = str(resp.get("task_id") or "")
    conv_id = str(resp.get("conversation_id") or "")
    if not task_id:
        raise RuntimeError(f"oracle returned no task_id: {resp}")
    return task_id, conv_id, tag


def _record_payload(todo, obj: dict, *, judge: str) -> tuple[bool, str]:
    verdict = str(obj.get("verdict") or "uncertain")
    summary = str(obj.get("summary") or "")
    evidence = obj.get("evidence_urls") or []
    if not isinstance(evidence, list):
        evidence = []
    notes = str(obj.get("notes") or "")
    path = record(
        todo.slug(),
        verdict=verdict if verdict in {"pass", "fail", "uncertain"} else "uncertain",
        judge=judge,
        summary=summary or "(oracle returned no summary)",
        evidence_urls=[str(u) for u in evidence],
        notes=notes,
    )
    return verdict == "pass", str(path.relative_to(SCRIPT_DIR))


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
    first = text.find("{")
    last = text.rfind("}")
    if first >= 0 and last > first:
        try:
            obj = json.loads(text[first:last + 1])
            if isinstance(obj, dict):
                return obj
        except json.JSONDecodeError:
            pass

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


def judge_with_oracle(todo_id: str, *, timeout_s: int = 900) -> tuple[bool, str]:
    todos = parse_board(BOARD_PATH)
    todo = todos.get(todo_id)
    if not todo:
        return False, f"{todo_id} not found"
    profile, errors = load_profile(todo.slug())
    if profile is None:
        return False, "profile missing: " + "; ".join(errors)
    target_summary = {
        "todo_id": todo.todo_id,
        "slug": todo.slug(),
        "title": _clip(todo.title, 180),
        "source_url": _clip(todo.source or profile.source_url, 240),
        "type": _clip(todo.type_, 80),
        "statement": _clip(todo.statement, 520),
        "prior_freshness_claim": _clip(todo.prior or todo.untouched, 520),
        "final_display_form": _clip(profile.final_display_form, 180),
        "success_gate": _clip(profile.success_gate, 420),
    }
    prompt = ORACLE_PROMPT.format(
        target_json=json.dumps(target_summary, ensure_ascii=False, separators=(",", ":")),
    )
    errors: list[str] = []
    for fresh_attempt in range(2):
        try:
            task_id, conv_id, _tag = _submit_freshness_prompt(
                prompt,
                todo_id=todo_id,
                retry_index=fresh_attempt,
            )
        except Exception as exc:
            return False, f"oracle submit failed: {exc}"
        result, error = _poll_oracle_result(task_id, timeout_s=timeout_s)
        if result and result.get("response"):
            obj = _extract_judge_payload(str(result.get("response") or ""))
            if obj:
                return _record_payload(todo, obj, judge="oracle" if fresh_attempt == 0 else "oracle_fresh_retry")
            errors.append(f"{task_id}: unparseable response")
            conv_id = str(result.get("conversation_id") or conv_id)
            retry_result, retry_error = _retry_oracle_result(
                task_id=task_id,
                conversation_id=conv_id,
                timeout_s=timeout_s,
            )
            if retry_result and retry_result.get("response"):
                obj = _extract_judge_payload(str(retry_result.get("response") or ""))
                if obj:
                    return _record_payload(todo, obj, judge="oracle_retry")
                errors.append("re-extract response unparseable")
            elif retry_error:
                errors.append(retry_error)
        elif result and result.get("status") == "cancelled":
            errors.append(error)
        else:
            errors.append(error or f"{task_id}: no response")
            retry_result, retry_error = _retry_oracle_result(
                task_id=task_id,
                conversation_id=conv_id,
                timeout_s=timeout_s,
            )
            if retry_result and retry_result.get("response"):
                obj = _extract_judge_payload(str(retry_result.get("response") or ""))
                if obj:
                    return _record_payload(todo, obj, judge="oracle_retry")
                errors.append("re-extract response unparseable")
            elif retry_error:
                errors.append(retry_error)
    return False, "; ".join(e for e in errors if e) or "oracle produced no parseable freshness verdict"


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("list", help="list targets requiring freshness judge")
    rec = sub.add_parser("record", help="record explicit freshness/currentness verdict")
    rec.add_argument("--slug", required=True)
    rec.add_argument("--verdict", required=True, choices=["pass", "fail", "uncertain"])
    rec.add_argument("--judge", required=True, help="human|oracle|chatgpt|codex+human")
    rec.add_argument("--summary", required=True)
    rec.add_argument("--evidence-url", action="append", default=[])
    rec.add_argument("--notes", default="")
    ora = sub.add_parser("oracle", help="ask outreach Oracle/ChatGPT to judge one board target")
    ora.add_argument("--todo-id", required=True)
    ora.add_argument("--timeout-s", type=int, default=900)
    auto = sub.add_parser("auto", help="judge top missing/uncertain freshness targets")
    auto.add_argument("--top", type=int, default=2)
    auto.add_argument("--timeout-s", type=int, default=900)
    auto.add_argument(
        "--retry-uncertain",
        action="store_true",
        help="allow auto mode to re-judge existing uncertain verdicts",
    )
    args = p.parse_args(argv)
    if args.cmd == "list":
        print(json.dumps(required_targets(), ensure_ascii=False, indent=2))
        return 0
    if args.cmd == "record":
        path = record(
            args.slug,
            verdict=args.verdict,
            judge=args.judge,
            summary=args.summary,
            evidence_urls=args.evidence_url,
            notes=args.notes,
        )
        print(str(path.relative_to(SCRIPT_DIR)))
        return 0
    if args.cmd == "oracle":
        ok, msg = judge_with_oracle(args.todo_id, timeout_s=args.timeout_s)
        print(json.dumps({"ok": ok, "message": msg}, ensure_ascii=False, indent=2))
        return 0 if ok else 1
    if args.cmd == "auto":
        payload = auto_judge(
            top=args.top,
            timeout_s=args.timeout_s,
            retry_uncertain=args.retry_uncertain,
        )
        print(json.dumps(payload, ensure_ascii=False, indent=2))
        return 0 if all(r.get("ok") for r in payload["results"]) else 1
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
