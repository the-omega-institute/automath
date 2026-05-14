#!/usr/bin/env python3
"""Offline status report for the outreach pipeline.

This command does not start the supervisor, agents, Oracle server, or browser
bridge. It inspects local state and preflight judgments so the operator can see
why the pipeline would run, idle, or block before enabling it.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
STATE_DIR = SCRIPT_DIR / "outreach_state"
TASK_QUEUE_DIR = STATE_DIR / "task_queue"
TASK_CLAIMS_DIR = STATE_DIR / "task_claims"
RESEARCH_CLAIMS_DIR = STATE_DIR / "research_claims"
SUPERVISOR_LOG = STATE_DIR / "supervisor_logs" / "supervisor.log"
PI_JOURNAL = STATE_DIR / "pi_journal.jsonl"
BOARD_REFILL_STATUS = STATE_DIR / "board_refill.status.json"
RESEARCH_LOOP_STATUS = STATE_DIR / "research_loop.status.json"
CONTEXT_REFRESH_STATUS = STATE_DIR / "context_refresh.json"
X_OPENPROBLEM_STATUS = STATE_DIR / "x_openproblem_watch.status.json"
X_OPENPROBLEM_RECENT = STATE_DIR / "x_openproblem_recent.json"

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_preflight import ACTIONABLE_VERDICTS, judge_board  # noqa: E402
from outreach_science_gate import audit_board as science_gate_audit, evaluate as science_gate_evaluate, ledger_path  # noqa: E402
from outreach_board_parser import parse_board  # noqa: E402
from outreach_task_spec import list_tasks  # noqa: E402
import outreach_task_runner  # noqa: E402
from outreach_review_queue import build_queue as build_review_queue  # noqa: E402
from outreach_impact_gate import evaluate as impact_gate_evaluate  # noqa: E402


HIGH_VALUE_RESULT_STATUSES = {"IMPACT_PLAN_READY"}


def _clean_inline(s: str, *, limit: int = 260) -> str:
    """Compact mail/forum snippets for operator-facing status."""
    text = " ".join(str(s or "").replace("\u2028", " ").replace("\r", " ").split())
    text = text.replace("- External Email -", "").strip()
    if len(text) <= limit:
        return text
    return text[: max(0, limit - 1)].rstrip() + "..."


def _friendly_status(status: str) -> str:
    return {
        "pending": "待处理",
        "in_progress": "处理中",
        "gated_ready": "已过 gate，等待你审阅/批准",
        "rejected": "退回重做",
        "blocked": "阻塞",
        "writeback_pending": "等待写回",
        "writeback_in_progress": "写回中",
        "writeback_done": "写回完成",
        "writeback_failed": "写回失败",
        "waiting_external_reply": "已发出，等待对方回复",
    }.get(status, status)


def _task_public_group(task) -> str:
    raw = " ".join(
        [
            task.id,
            task.title,
            str((task.context or {}).get("external_party", "")),
            str((task.context or {}).get("thread", "")),
        ]
    ).lower()
    if "israel" in raw or "bytepro" in raw:
        return "Israel Cazares / bytepro.ai"
    if "tolmetes" in raw or "tolmeton" in raw or "hegemonikon" in raw:
        return "Tolmetes / Bridge Schema #38"
    if task.type == "code_pr_response" or task.requires_external_repo or "nyxid" in raw:
        return "工程外部阻塞"
    return (task.context or {}).get("external_party") or task.title or task.id


def _task_focus(task) -> str:
    tid = task.id.lower()
    title = task.title
    if "israel-bytepro-paper-trade" in tid:
        return "读 Israel 的 SAIR/Zenodo 文章，整理可讨论的问题和 Automath/Lean 指针"
    if "israel-frontier-subset" in tid:
        return "根据他最新建议整理 Set A/B/C frontier subset 和回复草稿"
    if "tolmetes" in tid or "tolmeton" in tid:
        return "Bridge Schema standalone short note：确认 §1/§4/§5 的合作边界和下一步"
    if "nyxid" in tid:
        return "NyxID PR #592 的工程修复跟踪，不是数学合作任务"
    return title


def _task_next(task) -> str:
    if task.status == "gated_ready":
        return "等你审阅；你批准前不会发送"
    if task.status == "waiting_external_reply":
        return "不用继续催；等对方回复"
    if task.status == "blocked":
        if task.requires_external_repo:
            return f"需要外部 repo checkout：{task.requires_external_repo}"
        return task.last_reason or "需要解除阻塞"
    if task.status in {"pending", "rejected"}:
        return "等待 task_runner 处理或重做"
    if task.status == "in_progress":
        return "正在生成/检查草稿"
    return task.last_reason or ""


def _collaboration_ready_reason(group: dict) -> str:
    progress = str(group.get("progress") or "合作/邮件草稿已过 gate")
    subject = str(group.get("latest_reply_subject") or "").strip()
    date = str(group.get("latest_reply_date") or "").strip()
    summary = str(group.get("latest_reply_summary") or "").strip()
    details: list[str] = []
    if subject or date:
        details.append(f"latest mail: {date} {subject}".strip())
    if summary:
        details.append(f"summary: {summary}")
    if details:
        return progress + " | " + " | ".join(details)
    return progress


def _research_name(row: dict) -> str:
    title = str(row.get("title") or "").strip()
    if title:
        return title
    slug = str(row.get("slug") or "").replace("_", " ")
    return slug or str(row.get("todo_id") or "")


def _research_line(row: dict) -> str:
    name = _research_name(row)
    kind = str(row.get("display") or row.get("contribution_type") or "").strip()
    if kind:
        return f"{name}: {kind}"
    return name


def _row_key(*, title: str = "", slug: str = "", todo_id: str = "") -> str:
    base = title or slug or todo_id
    return " ".join(str(base).lower().replace("_", " ").split())


def _add_unique(rows: list[dict], row: dict) -> None:
    key = _row_key(
        title=str(row.get("title") or row.get("name") or ""),
        slug=str(row.get("slug") or ""),
        todo_id=str(row.get("todo_id") or ""),
    )
    if not key:
        return
    for old in rows:
        old_key = _row_key(
            title=str(old.get("title") or old.get("name") or ""),
            slug=str(old.get("slug") or ""),
            todo_id=str(old.get("todo_id") or ""),
        )
        if old_key == key:
            return
    rows.append(row)


def _build_readable_task_groups(tasks) -> dict:
    grouped: dict[str, list] = {}
    for task in tasks:
        grouped.setdefault(_task_public_group(task), []).append(task)

    collaborations: list[dict] = []
    engineering: list[dict] = []
    for group, rows in sorted(grouped.items()):
        statuses = sorted({t.status for t in rows})
        latest_dates = [
            str((t.context or {}).get("latest_reply_date", ""))
            for t in rows
            if (t.context or {}).get("latest_reply_date")
        ]
        latest_summaries = [
            str((t.context or {}).get("latest_reply_summary", ""))
            for t in rows
            if (t.context or {}).get("latest_reply_summary")
        ]
        latest_subjects = [
            str(((t.context or {}).get("latest_registered_reply") or {}).get("subject") or "")
            for t in rows
            if ((t.context or {}).get("latest_registered_reply") or {}).get("subject")
        ]
        focuses = [_task_focus(t) for t in rows]
        next_steps = sorted({_task_next(t) for t in rows if _task_next(t)})
        entry = {
            "name": group,
            "status": " / ".join(_friendly_status(s) for s in statuses),
            "latest_reply_date": latest_dates[-1] if latest_dates else "",
            "latest_reply_subject": latest_subjects[-1] if latest_subjects else "",
            "latest_reply_summary": _clean_inline(latest_summaries[-1], limit=360) if latest_summaries else "",
            "progress": "; ".join(dict.fromkeys(focuses)),
            "next": "; ".join(next_steps),
            "task_count": len(rows),
        }
        if group == "工程外部阻塞":
            engineering.append(entry)
        else:
            collaborations.append(entry)
    return {"collaborations": collaborations, "engineering": engineering}


def _build_decision_view(report: dict, *, tasks: list, todos: dict, science_rows: list) -> dict:
    running: list[dict] = []
    ready: list[dict] = []
    reconsider: list[dict] = []

    active = ((report.get("recent_status_files") or {}).get("research_loop") or {}).get("active") or []
    for row in active:
        todo_id = str(row.get("todo_id") or "")
        slug = str(row.get("slug") or "")
        todo = todos.get(todo_id)
        _add_unique(
            running,
            {
                "name": todo.title if todo else slug or todo_id,
                "kind": "research",
                "why": "research loop 正在处理",
            },
        )

    oracle = report.get("oracle_server") or {}
    for agent in (oracle.get("agents") or {}).values():
        task_id = str(agent.get("task_id") or "")
        if task_id.startswith("deep_"):
            slugish = task_id.removeprefix("deep_").split("_t", 1)[0]
            title = ""
            for todo in todos.values():
                if todo.slug() == slugish:
                    title = todo.title
                    break
            _add_unique(
                running,
                {
                    "name": title or slugish.replace("_", " "),
                    "kind": "oracle",
                    "why": "Oracle deep turn 正在生成/抽取",
                },
            )
        elif "board" in task_id or task_id.startswith("outreach_"):
            _add_unique(
                running,
                {
                    "name": "Board refill / open-problem discovery",
                    "kind": "oracle",
                    "why": "Oracle 正在找新候选或修复候选输入",
                },
            )

    for group in (report.get("readable_task_groups") or {}).get("collaborations") or []:
        status_text = str(group.get("status") or "")
        next_text = str(group.get("next") or "")
        is_waiting = "等待对方回复" in status_text or "不用继续催" in next_text
        has_unfinished_followup = any(
            token in status_text
            for token in ("待处理", "处理中", "退回重做", "写回失败", "阻塞")
        )
        if "等待你审阅/批准" in status_text and not is_waiting and not has_unfinished_followup:
            _add_unique(
                ready,
                {
                    "name": str(group.get("name") or ""),
                    "kind": "collaboration",
                    "why": _collaboration_ready_reason(group),
                    "next": next_text or "等你审阅；批准前不会发送",
                },
            )

    sg = report.get("science_gate") or {}
    close_names = {
        _row_key(title=str(row.get("title") or ""), slug=str(row.get("slug") or ""), todo_id=str(row.get("todo_id") or ""))
        for row in sg.get("close_ready") or []
    }
    impact_by_todo = {}
    for todo in todos.values():
        try:
            impact_by_todo[todo.todo_id] = impact_gate_evaluate(todo)
        except Exception:
            pass

    for row in sg.get("writeback_ready") or []:
        impact = impact_by_todo.get(str(row.get("todo_id") or ""))
        if impact is not None and getattr(impact, "status", "") not in HIGH_VALUE_RESULT_STATUSES:
            continue
        key = _row_key(title=str(row.get("title") or ""), slug=str(row.get("slug") or ""), todo_id=str(row.get("todo_id") or ""))
        next_text = "可进入 operator review；批准后再决定论文/邮件/评论/X 的宣发形式"
        if key in close_names:
            next_text = "已接近 close-ready；下一步是人类审阅是否宣发/写回"
        _add_unique(
            ready,
            {
                "name": _research_name(row),
                "kind": row.get("contribution_type") or "research",
                "why": "通过 science gate 和 impact gate；可作为真实数学结果审阅",
                "next": next_text,
            },
        )

    active_keys = {
        _row_key(title=str(row.get("name") or ""), slug=str(row.get("slug") or ""), todo_id=str(row.get("todo_id") or ""))
        for row in running
    }
    ready_keys = {
        _row_key(title=str(row.get("name") or ""), slug=str(row.get("slug") or ""), todo_id=str(row.get("todo_id") or ""))
        for row in ready
    }
    for sci in science_rows:
        todo = todos.get(sci.todo_id)
        title = todo.title if todo else sci.slug
        key = _row_key(title=title, slug=sci.slug, todo_id=sci.todo_id)
        if key in active_keys or key in ready_keys:
            continue
        loop_state = _read_json(STATE_DIR / f"{sci.slug}.research_loop.json")
        no_progress = int(loop_state.get("no_progress_batches") or 0)
        reasons: list[str] = []
        if no_progress >= 20:
            reasons.append(f"已深入多轮但无新增 gate 进展（no_progress_batches={no_progress}）")
        if sci.failure_kind in {"low_value", "stale", "misframed", "closed"}:
            reasons.append(f"gate failure={sci.failure_kind}")
        if sci.status == "BOARD_SKIPPED" and no_progress > 0:
            reasons.append("曾经进入研究循环，后来被 board/science gate 标记为 skip/closed/handoff")
        if reasons:
            _add_unique(
                reconsider,
                {
                    "name": title,
                    "kind": sci.status,
                    "why": "; ".join(reasons),
                    "next": "等人类判断：删除、归档、还是改题后继续",
                },
            )

    return {
        "running": running,
        "ready_next": ready,
        "reconsider_delete": reconsider,
    }


def _server_status() -> dict:
    url = os.environ.get("OUTREACH_ORACLE_SERVER_URL", "http://127.0.0.1:8766") + "/status"
    try:
        with urllib.request.urlopen(url, timeout=2) as r:
            return json.loads(r.read().decode("utf-8"), strict=False)
    except Exception as urllib_exc:  # noqa: BLE001
        try:
            proc = subprocess.run(
                ["curl", "-fsS", "--max-time", "2", url],
                capture_output=True,
                text=True,
                timeout=4,
                check=False,
            )
            if proc.returncode == 0:
                return json.loads(proc.stdout, strict=False)
            curl_error = (proc.stderr or "").strip() or f"curl exited {proc.returncode}"
        except Exception as curl_exc:  # noqa: BLE001
            curl_error = str(curl_exc)
        return {"alive": False, "error": f"urllib={urllib_exc}; curl={curl_error}"}


def _matching_processes(pattern: str) -> list[dict]:
    try:
        proc = subprocess.run(
            ["ps", "-axo", "pid=,ppid=,%cpu=,%mem=,rss=,args="],
            capture_output=True,
            text=True,
            timeout=5,
            check=False,
        )
    except Exception:
        return []
    rows: list[dict] = []
    for line in (proc.stdout or "").splitlines():
        if pattern not in line:
            continue
        if "/bin/zsh -c" in line or "python3 -c" in line or "outreach_status.py" in line:
            continue
        parts = line.strip().split(None, 5)
        if len(parts) < 6:
            continue
        try:
            pid = int(parts[0])
            ppid = int(parts[1])
            cpu = float(parts[2])
            mem = float(parts[3])
            rss_kb = int(parts[4])
        except ValueError:
            continue
        rows.append({
            "pid": pid,
            "ppid": ppid,
            "cpu": cpu,
            "mem": mem,
            "rss_mb": round(rss_kb / 1024, 1),
            "args": parts[5],
        })
    return rows


def _process_health() -> dict:
    supervisor = _matching_processes("outreach_supervisor.py")
    research = _matching_processes("outreach_research_loop.py")
    oracle = _matching_processes("outreach_oracle_server.py")
    return {
        "supervisor": supervisor,
        "research_loop": research,
        "oracle_server": oracle,
        "supervisor_alive": bool(supervisor),
        "research_loop_count": len(research),
        "oracle_server_count": len(oracle),
    }


def _pi_status() -> dict:
    if not PI_JOURNAL.exists():
        return {"available": False, "reason": "no pi_journal.jsonl yet"}
    try:
        lines = [ln for ln in PI_JOURNAL.read_text(encoding="utf-8", errors="replace").splitlines() if ln.strip()]
    except OSError as exc:
        return {"available": False, "reason": str(exc)}
    if not lines:
        return {"available": False, "reason": "empty pi_journal.jsonl"}
    try:
        row = json.loads(lines[-1])
    except json.JSONDecodeError:
        return {"available": False, "reason": "last PI journal row is not JSON"}
    stdout = str(row.get("claude_stdout_truncated") or "")
    ts = str(row.get("ts") or "")
    age_minutes = None
    if ts:
        try:
            dt = datetime.fromisoformat(ts.replace("Z", "+00:00"))
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            age_minutes = round((datetime.now(timezone.utc) - dt).total_seconds() / 60, 1)
        except ValueError:
            pass
    reason = ""
    if not row.get("ok"):
        if "hit your limit" in stdout.lower():
            reason = "Claude limit hit"
        else:
            reason = stdout.strip().splitlines()[0][:160] if stdout.strip() else "PI backend failed"
    elif not row.get("plan"):
        reason = "PI backend returned no parseable JSON plan"
    return {
        "available": bool(row.get("ok") and row.get("plan")),
        "last_ts": ts,
        "age_minutes": age_minutes,
        "ok": bool(row.get("ok")),
        "rc": row.get("rc"),
        "backend": row.get("backend"),
        "plan_health": (row.get("plan") or {}).get("loop_health") if isinstance(row.get("plan"), dict) else None,
        "reason": reason,
    }


def _read_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}


def _tail(path: Path, n: int = 12) -> list[str]:
    if not path.exists():
        return []
    try:
        return path.read_text(encoding="utf-8", errors="replace").splitlines()[-n:]
    except OSError:
        return []


def _claim_files(root: Path) -> list[str]:
    if not root.exists():
        return []
    return sorted(str(p.relative_to(SCRIPT_DIR)) for p in root.glob("*/*") if p.is_file())


def build_report() -> dict:
    tasks = list_tasks()
    task_hist: dict[str, int] = {}
    for t in tasks:
        task_hist[t.status] = task_hist.get(t.status, 0) + 1

    preflight = judge_board()
    preflight_hist: dict[str, int] = {}
    for row in preflight:
        preflight_hist[row.verdict] = preflight_hist.get(row.verdict, 0) + 1

    stale_task_rows = outreach_task_runner.cleanup_stale_in_progress_tasks(dry_run=True)
    review_queue = build_review_queue()
    todos = parse_board(SCRIPT_DIR / "RESEARCH_BOARD.md")
    science_rows = [science_gate_evaluate(todo) for todo in todos.values()]
    science_hist: dict[str, int] = {}
    science_action_hist: dict[str, int] = {}
    science_failure_hist: dict[str, int] = {}
    science_lane_hist: dict[str, int] = {}
    quality_scores: list[int] = []
    for row in science_rows:
        science_hist[row.status] = science_hist.get(row.status, 0) + 1
        science_action_hist[row.next_action] = science_action_hist.get(row.next_action, 0) + 1
        science_failure_hist[row.failure_kind] = science_failure_hist.get(row.failure_kind, 0) + 1
        lane = row.target_lane or "none"
        science_lane_hist[lane] = science_lane_hist.get(lane, 0) + 1
        q = row.contract_quality or {}
        if isinstance(q.get("score"), int):
            quality_scores.append(q["score"])
    science_audit_rc, science_audit_diagnostics, _ = science_gate_audit(SCRIPT_DIR / "RESEARCH_BOARD.md")
    ledgers_present = [row.slug for row in science_rows if ledger_path(row.slug).exists()]

    report = {
        "oracle_server": _server_status(),
        "process_health": _process_health(),
        "pi_status": _pi_status(),
        "task_queue": {
            "count": len(tasks),
            "status_histogram": task_hist,
            "gated_ready": [t.id for t in tasks if t.status == "gated_ready"],
            "blocked": [{"id": t.id, "reason": t.last_reason} for t in tasks if t.status == "blocked"],
            "stale_in_progress": stale_task_rows,
        },
        "readable_task_groups": _build_readable_task_groups(tasks),
        "board_preflight": {
            "count": len(preflight),
            "histogram": preflight_hist,
            "actionable": [
                {
                    "todo_id": r.todo_id,
                    "title": r.title,
                    "display": r.display.kind,
                    "artifact": r.display.artifact,
                    "score": r.score,
                }
                for r in preflight
                if r.verdict in ACTIONABLE_VERDICTS
            ],
            "blocked_sample": [
                {
                    "todo_id": r.todo_id,
                    "verdict": r.verdict,
                    "title": r.title,
                    "missing": r.missing,
                    "reasons": r.reasons,
                }
                for r in preflight
                if r.verdict not in ACTIONABLE_VERDICTS
            ][:20],
        },
        "science_gate": {
            "audit_ok": science_audit_rc == 0,
            "audit_diagnostics": science_audit_diagnostics,
            "histogram": science_hist,
            "next_action_histogram": science_action_hist,
            "failure_kind_histogram": science_failure_hist,
            "target_lane_histogram": science_lane_hist,
            "contract_quality": {
                "count": len(quality_scores),
                "min": min(quality_scores) if quality_scores else None,
                "max": max(quality_scores) if quality_scores else None,
                "avg": round(sum(quality_scores) / len(quality_scores), 2) if quality_scores else None,
            },
            "ledger_count": len(ledgers_present),
            "ledger_slugs": ledgers_present,
            "writeback_ready": [
                {
                    "todo_id": r.todo_id,
                    "slug": r.slug,
                    "title": todos[r.todo_id].title if r.todo_id in todos else r.slug,
                    "contribution_type": r.contribution_type,
                    "artifact": r.terminal_artifact,
                    "reasons": r.reasons,
                }
                for r in science_rows
                if r.writeback_ready
            ],
            "close_ready": [
                {
                    "todo_id": r.todo_id,
                    "slug": r.slug,
                    "title": todos[r.todo_id].title if r.todo_id in todos else r.slug,
                    "reasons": r.reasons,
                }
                for r in science_rows
                if r.close_ready
            ],
        },
        "claims": {
            "task": _claim_files(TASK_CLAIMS_DIR),
            "research": _claim_files(RESEARCH_CLAIMS_DIR),
        },
        "recent_status_files": {
            "research_loop": _read_json(RESEARCH_LOOP_STATUS),
            "board_refill": _read_json(BOARD_REFILL_STATUS),
            "context_refresh": _read_json(CONTEXT_REFRESH_STATUS),
            "x_openproblem_watch": _read_json(X_OPENPROBLEM_STATUS),
            "x_openproblem_recent": _read_json(X_OPENPROBLEM_RECENT),
        },
        "supervisor_tail": _tail(SUPERVISOR_LOG),
        "review_queue": {
            "ready_count": len(review_queue["ready_for_operator"]),
            "waiting_external_reply_count": len(review_queue.get("waiting_external_reply") or []),
            "needs_refresh_count": len(review_queue.get("needs_refresh") or []),
            "blocked_or_stale_count": len(review_queue["blocked_tasks"]) + len(review_queue["stale_in_progress"]),
            "profile_candidate_count": len(review_queue["profile_candidates"]),
            "candidate_inbox": review_queue.get("candidate_inbox", {}),
            "freshness_judges": review_queue.get("freshness_judges", {}),
        },
    }
    report["decision_view"] = _build_decision_view(
        report, tasks=tasks, todos=todos, science_rows=science_rows
    )
    return report


def _print_text(report: dict) -> None:
    oracle = report["oracle_server"]
    alive = oracle.get("port") == 8766 or oracle.get("alive") is True
    print(f"Oracle server: {'alive' if alive else 'down'}")
    if not alive:
        print(f"  {oracle.get('error', 'no status')}")
    proc = report.get("process_health") or {}
    print(
        "Processes: "
        f"supervisor={'alive' if proc.get('supervisor_alive') else 'down'} "
        f"research_loop={proc.get('research_loop_count', 0)} "
        f"oracle_server={proc.get('oracle_server_count', 0)}"
    )
    pi = report.get("pi_status") or {}
    if pi:
        pi_line = "available" if pi.get("available") else "unavailable"
        reason = pi.get("reason") or pi.get("plan_health") or ""
        backend = pi.get("backend") or {}
        backend_text = ""
        if isinstance(backend, dict) and backend.get("backend"):
            backend_text = f" backend={backend.get('backend')}"
            if backend.get("fallback_used"):
                backend_text += f" fallback={backend.get('fallback_reason', '')}"
        age = pi.get("age_minutes")
        age_text = f", age={age}m" if age is not None else ""
        print(f"PI: {pi_line}{age_text}{backend_text} {reason}".rstrip())
    decision = report.get("decision_view") or {}

    print("1. 还在跑")
    rows = decision.get("running") or []
    if rows:
        for row in rows:
            print(f"  - {row.get('name')}: {row.get('why')}")
    else:
        print("  - none")

    print("2. ready to 宣发 / 下一步")
    rows = decision.get("ready_next") or []
    if rows:
        for row in rows:
            print(f"  - {row.get('name')}: {row.get('why')}")
            if row.get("next"):
                print(f"    next: {row.get('next')}")
    else:
        print("  - none")

    print("3. 深入后可能不值得继续，等人判断是否删/归档")
    rows = decision.get("reconsider_delete") or []
    if rows:
        for row in rows:
            print(f"  - {row.get('name')}: {row.get('why')}")
            if row.get("next"):
                print(f"    next: {row.get('next')}")
    else:
        print("  - none")

    refill = report["recent_status_files"].get("board_refill") or {}
    if refill:
        print(f"Board refill last: {refill.get('verdict')} at {refill.get('ran_at')} ({refill.get('reason', '')})")
    ctx = report["recent_status_files"].get("context_refresh") or {}
    if ctx:
        reg = ctx.get("registered") or {}
        print(
            f"Context refresh last: {ctx.get('generated_at')} "
            f"gh={len(reg.get('github_threads') or [])} mail={len(reg.get('mail_threads') or [])}"
        )
    xwatch = report["recent_status_files"].get("x_openproblem_watch") or {}
    if xwatch:
        print(
            f"X openproblem watch last: {xwatch.get('verdict')} "
            f"estimate=${xwatch.get('estimated_cost_usd')} cooldown={xwatch.get('cooldown_reason', '')}"
        )
    rq = report.get("review_queue") or {}
    if rq:
        fresh = rq.get("freshness_judges") or {}
        print(
            f"Queue summary: ready={rq.get('ready_count')} "
            f"waiting_external={rq.get('waiting_external_reply_count', 0)} "
            f"needs_refresh={rq.get('needs_refresh_count')} "
            f"blocked_or_stale={rq.get('blocked_or_stale_count')} "
            f"profile_candidates={rq.get('profile_candidate_count')} "
            f"candidate_inbox={((rq.get('candidate_inbox') or {}).get('total'))} "
            f"freshness={fresh.get('passing', 0)}/{fresh.get('required', 0)}"
        )


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--json", action="store_true", help="emit full JSON report")
    args = p.parse_args(argv)
    report = build_report()
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        _print_text(report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
