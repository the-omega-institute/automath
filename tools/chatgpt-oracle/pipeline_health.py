#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Read-only health summary for the ChatGPT Oracle publication pipeline."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
SUPERVISOR_LOG = SCRIPT_DIR / "supervisor_logs" / "supervisor.log"
HEALTH_SNAPSHOT_LOG = SCRIPT_DIR / "supervisor_logs" / "health.jsonl"
SUPERVISOR_PID_FILE = SCRIPT_DIR / ".pipeline_supervisor.pid"
REFILL_QUEUE = REPO_ROOT / "papers" / "publication" / "_refill_queue.json"
PROGRAM_BOARD = REPO_ROOT / "papers" / "publication" / "PROGRAM_BOARD.md"
ORACLE_STATUS_URL = "http://127.0.0.1:8765/status"


def _python() -> str:
    return sys.executable or "python"


def read_oracle_status(timeout: int = 8) -> dict[str, Any]:
    try:
        with urllib.request.urlopen(ORACLE_STATUS_URL, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except Exception:
        return {}


def read_supervisor_tail(limit: int = 40) -> list[str]:
    try:
        return SUPERVISOR_LOG.read_text(encoding="utf-8", errors="replace").splitlines()[-limit:]
    except OSError:
        return []


def read_supervisor_log_lines(limit: int = 2000) -> list[str]:
    return read_supervisor_tail(limit=limit)


def supervisor_log_mtime() -> float:
    try:
        return SUPERVISOR_LOG.stat().st_mtime
    except OSError:
        return 0.0


def file_mtime(path: Path) -> float:
    try:
        return path.stat().st_mtime
    except OSError:
        return 0.0


def read_supervisor_pid_record(path: Path = SUPERVISOR_PID_FILE) -> dict[str, Any]:
    try:
        raw = path.read_text(encoding="utf-8").strip()
    except OSError:
        return {"pid": None, "started_ts": None, "script": ""}
    if not raw:
        return {"pid": None, "started_ts": None, "script": ""}
    if raw.startswith("{"):
        try:
            data = json.loads(raw)
        except json.JSONDecodeError:
            return {"pid": None, "started_ts": None, "script": ""}
        pid = data.get("pid")
        try:
            pid = int(pid)
        except (TypeError, ValueError):
            pid = None
        if pid is not None and pid <= 0:
            pid = None
        started_ts = data.get("started_ts")
        try:
            started_ts = float(started_ts) if started_ts is not None else None
        except (TypeError, ValueError):
            started_ts = None
        return {
            "pid": pid,
            "started_ts": started_ts,
            "script": str(data.get("script") or ""),
        }
    try:
        pid = int(raw)
    except ValueError:
        pid = None
    if pid is not None and pid <= 0:
        pid = None
    return {"pid": pid, "started_ts": None, "script": ""}


def read_supervisor_pid(path: Path = SUPERVISOR_PID_FILE) -> int | None:
    return read_supervisor_pid_record(path).get("pid")


def process_alive(
    pid: int | None,
    *,
    platform: str = sys.platform,
    run=subprocess.run,
) -> bool:
    if not pid:
        return False
    if platform == "win32":
        proc = run(
            [
                "powershell",
                "-NoProfile",
                "-Command",
                f"Get-Process -Id {pid} -ErrorAction SilentlyContinue | Select-Object -First 1",
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=5,
            check=False,
        )
        return proc.returncode == 0 and bool((proc.stdout or "").strip())
    try:
        os.kill(pid, 0)
    except OSError:
        return False
    return True


def latest_supervisor_start_ts(lines: list[str]) -> float:
    return latest_supervisor_event_ts(lines, "supervisor starting")


def latest_supervisor_exit_ts(lines: list[str]) -> float:
    return latest_supervisor_event_ts(lines, "supervisor exiting")


def latest_supervisor_log_ts(lines: list[str]) -> float:
    latest = 0.0
    for line in lines:
        match = re.search(r"\[(\d{4}-\d{2}-\d{2}T[^]]+)\]", line)
        if not match:
            continue
        try:
            latest = max(latest, _parse_iso_ts(match.group(1)))
        except ValueError:
            continue
    return latest


def latest_supervisor_poll_s(lines: list[str]) -> int | None:
    for line in reversed(lines):
        if "supervisor starting" not in line:
            continue
        match = re.search(r"\bpoll=(\d+)s\b", line)
        if not match:
            continue
        try:
            poll_s = int(match.group(1))
        except ValueError:
            return None
        return poll_s if poll_s > 0 else None
    return None


def latest_supervisor_event_ts(lines: list[str], marker: str) -> float:
    latest = 0.0
    for line in lines:
        if marker not in line:
            continue
        match = re.search(r"\[(\d{4}-\d{2}-\d{2}T[^]]+)\]", line)
        if not match:
            continue
        raw = match.group(1)
        try:
            latest = max(latest, _parse_iso_ts(raw))
        except ValueError:
            continue
    return latest


def _parse_iso_ts(raw: str) -> float:
    from datetime import datetime

    if raw.endswith("Z"):
        raw = raw[:-1] + "+00:00"
    return datetime.fromisoformat(raw).timestamp()


def parse_manual_submission_queue(board_text: str) -> list[dict[str, str]]:
    queue: list[dict[str, str]] = []
    seen_three_column_table = False
    for raw_line in board_text.splitlines():
        line = raw_line.strip()
        if line.startswith("## "):
            if seen_three_column_table:
                break
            continue
        if not line.startswith("|"):
            continue
        parts = [part.strip() for part in line.strip("|").split("|")]
        if len(parts) == 3:
            seen_three_column_table = True
        if not seen_three_column_table or len(parts) < 3 or not parts[0].startswith("`"):
            continue
        paper = parts[0].strip("` ")
        if not paper:
            continue
        queue.append({
            "paper": paper,
            "journal": parts[1],
            "note": parts[2],
        })
    return queue


def parse_ready_submission_entries(board_text: str) -> list[dict[str, str]]:
    ready: list[dict[str, str]] = []
    seen_full_table = False
    for raw_line in board_text.splitlines():
        line = raw_line.strip()
        if line.startswith("## "):
            if seen_full_table:
                break
            continue
        if not line.startswith("|"):
            continue
        parts = [part.strip() for part in line.strip("|").split("|")]
        if len(parts) >= 4:
            seen_full_table = True
        if not seen_full_table or len(parts) < 4 or not parts[0].startswith("`"):
            continue
        status = parts[2]
        status_lower = status.lower()
        if "c-done" not in status_lower and "可投稿" not in status:
            continue
        paper = parts[0].strip("` ")
        if not paper:
            continue
        ready.append({
            "paper": paper,
            "journal": parts[1],
            "status": status,
            "note": parts[3],
        })
    return ready


def read_manual_submission_queue() -> list[dict[str, str]]:
    try:
        text = PROGRAM_BOARD.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []
    return parse_manual_submission_queue(text)


def read_ready_submission_entries() -> list[dict[str, str]]:
    try:
        text = PROGRAM_BOARD.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []
    return parse_ready_submission_entries(text)


def discovery_summary() -> dict[str, Any]:
    code = (
        "import json, sys; "
        f"sys.path.insert(0, {str(SCRIPT_DIR)!r}); "
        "import oracle_pipeline; "
        "summary = oracle_pipeline.discover_paper_summary("
        "None, respect_assignment=False, log=False); "
        "print(json.dumps(summary, ensure_ascii=True))"
    )
    proc = subprocess.run(
        [_python(), "-c", code],
        cwd=str(REPO_ROOT),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=30,
        check=False,
    )
    if proc.returncode != 0:
        return {"diagnosis": "discovery_failed", "error": (proc.stderr or proc.stdout).strip()[:500]}
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        return {"diagnosis": "discovery_failed", "error": str(exc)}


def categorize_skipped_status_entries(entries: list[str]) -> dict[str, int]:
    categories = {
        "submitted": 0,
        "archive_or_parked": 0,
        "overlap_needs_human_resolution": 0,
        "overlap_deferred": 0,
        "stuck_needs_review": 0,
        "fake_extension": 0,
        "publication_ready": 0,
        "stage_a_blocked_other": 0,
        "other": 0,
    }
    for entry in entries:
        text = entry.strip()
        lower = text.lower()
        if "✅" in text or "可投稿" in text or "c-done" in lower:
            categories["publication_ready"] += 1
        elif "needs_human_resolution" in lower:
            categories["overlap_needs_human_resolution"] += 1
        elif "overlap deferred" in lower:
            categories["overlap_deferred"] += 1
        elif "fake extension" in lower:
            categories["fake_extension"] += 1
        elif "c-stuck" in lower or "b-stuck" in lower:
            categories["stuck_needs_review"] += 1
        elif "归档" in text or "parked" in lower or "archive" in lower:
            categories["archive_or_parked"] += 1
        elif "已投" in text or "submitted" in lower or "under review" in lower or "peer review" in lower:
            categories["submitted"] += 1
        elif "a-blocked" in lower or "stage a" in lower:
            categories["stage_a_blocked_other"] += 1
        else:
            categories["other"] += 1
    return {key: count for key, count in categories.items() if count}


def build_health_report(
    *,
    oracle_status: dict[str, Any],
    discovery_summary: dict[str, Any],
    supervisor_tail: list[str],
    now_ts: float,
    supervisor_log_mtime: float,
    refill_queue_exists: bool,
    refill_project_url: str,
    manual_submission_queue: list[dict[str, str]],
    ready_submission_entries: list[dict[str, str]] | None = None,
    supervisor_code_mtime: float,
    supervisor_started_ts: float,
    supervisor_exited_ts: float,
    supervisor_last_log_ts: float,
    supervisor_poll_s: int | None,
    supervisor_pid: int | None,
    supervisor_pid_started_ts: float | None,
    supervisor_pid_script: str,
    supervisor_pid_alive: bool,
) -> dict[str, Any]:
    stale_supervisor = not supervisor_log_mtime or now_ts - supervisor_log_mtime > 900
    supervisor_code_changed = (
        bool(supervisor_code_mtime)
        and bool(supervisor_started_ts)
        and supervisor_code_mtime > supervisor_started_ts + 1.0
    )
    supervisor_pid_stale = (
        bool(supervisor_pid)
        and supervisor_pid_started_ts is not None
        and bool(supervisor_started_ts)
        and abs(supervisor_pid_started_ts - supervisor_started_ts) > 1.0
    )
    supervisor_pid_script_mismatch = (
        bool(supervisor_pid)
        and bool(supervisor_pid_script)
        and supervisor_pid_script != "pipeline_supervisor.py"
    )
    next_tick_eta_s: int | None = None
    if supervisor_last_log_ts and supervisor_poll_s:
        next_tick_eta_s = max(0, int(supervisor_last_log_ts + supervisor_poll_s - now_ts))
    ready_submission_entries = ready_submission_entries or []
    manual_papers = {item["paper"] for item in manual_submission_queue}
    ready_not_in_manual = [
        item for item in ready_submission_entries
        if item["paper"] not in manual_papers
    ]
    if not oracle_status:
        health = "blocked"
        reason = "oracle_down"
    elif stale_supervisor:
        health = "attention"
        reason = "supervisor_log_stale"
    elif supervisor_exited_ts > supervisor_started_ts:
        health = "attention"
        reason = "supervisor_not_running"
    elif supervisor_started_ts and supervisor_pid is None:
        health = "attention"
        reason = "supervisor_pid_missing"
    elif supervisor_pid is not None and not supervisor_pid_alive:
        health = "attention"
        reason = "supervisor_process_dead"
    elif supervisor_pid_stale:
        health = "attention"
        reason = "supervisor_pid_stale"
    elif supervisor_pid_script_mismatch:
        health = "attention"
        reason = "supervisor_pid_script_mismatch"
    elif supervisor_code_changed:
        health = "attention"
        reason = "supervisor_code_changed"
    elif discovery_summary.get("diagnosis") == "gate_exhausted" and ready_not_in_manual:
        health = "attention"
        reason = "ready_not_in_manual_queue"
    elif discovery_summary.get("diagnosis") == "gate_exhausted":
        health = "healthy_idle"
        reason = "gate_exhausted"
    elif int(discovery_summary.get("runnable_count") or 0) > 0:
        health = "running_or_ready"
        reason = "runnable_backlog"
    else:
        health = "attention"
        reason = str(discovery_summary.get("diagnosis") or "unknown")

    actions: list[str] = []
    if reason == "gate_exhausted" and not refill_queue_exists:
        if refill_project_url:
            actions.append("refill producer may run after cooldown")
        else:
            actions.append("refill local-context producer may run after cooldown")
    if reason == "gate_exhausted" and manual_submission_queue:
        first = manual_submission_queue[0]
        actions.append(
            "manual submission candidate: "
            f"{first['paper']} -> {first['journal']}"
        )
    if reason in {"gate_exhausted", "ready_not_in_manual_queue"} and ready_not_in_manual:
        first = ready_not_in_manual[0]
        actions.append(
            "ready not in manual queue: "
            f"{first['paper']} -> {first['journal']}"
        )
        actions.append(
            "triage ready-not-manual: add to manual queue, mark submitted, "
            "or park explicitly"
        )
    if reason == "supervisor_log_stale":
        actions.append("inspect or restart pipeline_supervisor.py")
    if reason == "supervisor_process_dead":
        actions.append("restart pipeline_supervisor.py")
    if reason == "supervisor_not_running":
        actions.append("restart pipeline_supervisor.py")
    if reason == "supervisor_pid_missing":
        actions.append("restart pipeline_supervisor.py")
    if reason == "supervisor_pid_stale":
        actions.append("restart pipeline_supervisor.py")
    if reason == "supervisor_pid_script_mismatch":
        actions.append("restart pipeline_supervisor.py")
    if reason == "supervisor_code_changed":
        actions.append("restart supervisor at a safe boundary to load updated code")
    if reason == "oracle_down":
        actions.append("start or restart oracle_server.py")

    return {
        "health": health,
        "reason": reason,
        "oracle": {
            "diagnosis": oracle_status.get("diagnosis", "down"),
            "queue_length": oracle_status.get("queue_length"),
            "agents_busy": oracle_status.get("agents_busy"),
            "max_agents": oracle_status.get("max_agents"),
            "source_sha": oracle_status.get("source_sha", ""),
            "completed": oracle_status.get("completed"),
            "active_sessions": oracle_status.get("active_sessions"),
            "queued_count": len(oracle_status.get("queued") or []),
            "queued_tasks_count": len(oracle_status.get("queued_tasks") or []),
            "registered_agents": len(oracle_status.get("agents") or {}),
            "active_recent_agents": len(oracle_status.get("active_recent_agents") or []),
        },
        "discovery": {
            "diagnosis": discovery_summary.get("diagnosis", "unknown"),
            "candidates": discovery_summary.get("candidate_count", 0),
            "runnable": discovery_summary.get("runnable_count", 0),
            "status_skipped": discovery_summary.get("skipped_status_count", 0),
            "done_skipped": discovery_summary.get("skipped_done_count", 0),
            "unregistered_skipped": discovery_summary.get("skipped_unregistered_count", 0),
            "assignment_skipped": discovery_summary.get("skipped_assignment_count", 0),
            "skip_categories": categorize_skipped_status_entries(
                list(discovery_summary.get("skipped_status") or [])
            ),
        },
        "supervisor": {
            "log_age_s": int(now_ts - supervisor_log_mtime) if supervisor_log_mtime else None,
            "last_line": supervisor_tail[-1] if supervisor_tail else "",
            "started_ts": supervisor_started_ts or None,
            "exited_ts": supervisor_exited_ts or None,
            "pid": supervisor_pid,
            "pid_started_ts": supervisor_pid_started_ts,
            "pid_script": supervisor_pid_script,
            "pid_alive": supervisor_pid_alive if supervisor_pid is not None else None,
            "code_mtime": supervisor_code_mtime or None,
            "code_changed_since_start": supervisor_code_changed,
            "poll_s": supervisor_poll_s,
            "last_log_ts": supervisor_last_log_ts or None,
            "next_tick_eta_s": next_tick_eta_s,
        },
        "refill": {
            "queue_exists": refill_queue_exists,
            "project_url_set": bool(refill_project_url),
        },
        "manual_submission_count": len(manual_submission_queue),
        "manual_submission_queue": manual_submission_queue,
        "ready_submission_count": len(ready_submission_entries),
        "ready_submission_entries": ready_submission_entries,
        "ready_not_in_manual_count": len(ready_not_in_manual),
        "ready_not_in_manual_queue": ready_not_in_manual,
        "actions": actions,
    }


def exit_code_for_report(report: dict[str, Any]) -> int:
    health = report.get("health")
    if health == "blocked":
        return 2
    if int(report.get("ready_not_in_manual_count") or 0) > 0:
        return 1
    if health in {"healthy_idle", "running_or_ready"}:
        return 0
    if health == "attention":
        return 1
    if health == "blocked":
        return 2
    return 1


def exit_code_for_history(
    snapshots: list[dict[str, Any]],
    *,
    now_ts: float | None = None,
    max_age_s: int = 0,
) -> int:
    if not snapshots:
        return 1
    if max_age_s > 0:
        captured_ts = snapshots[-1].get("captured_ts")
        try:
            captured_ts_float = float(captured_ts)
        except (TypeError, ValueError):
            return 1
        now = time.time() if now_ts is None else now_ts
        if now - captured_ts_float > max_age_s:
            return 1
    return exit_code_for_report(snapshots[-1])


def append_health_snapshot(
    report: dict[str, Any],
    *,
    path: Path = HEALTH_SNAPSHOT_LOG,
) -> None:
    captured_ts = time.time()
    snapshot = {
        "captured_ts": captured_ts,
        "captured_iso": datetime.fromtimestamp(captured_ts, timezone.utc).isoformat(),
        **report,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8", newline="\n") as handle:
        handle.write(json.dumps(snapshot, ensure_ascii=False, sort_keys=True))
        handle.write("\n")


def read_health_snapshots(
    *,
    path: Path = HEALTH_SNAPSHOT_LOG,
    limit: int = 10,
) -> list[dict[str, Any]]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return []
    snapshots: list[dict[str, Any]] = []
    for line in lines:
        if not line.strip():
            continue
        try:
            snapshot = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(snapshot, dict):
            snapshots.append(snapshot)
    if limit <= 0:
        return snapshots
    return snapshots[-limit:]


def format_history_report(
    snapshots: list[dict[str, Any]],
    *,
    now_ts: float | None = None,
) -> str:
    if not snapshots:
        return "history_count=0"
    counts: dict[str, int] = {}
    reason_counts: dict[str, int] = {}
    for snapshot in snapshots:
        health = str(snapshot.get("health") or "unknown")
        counts[health] = counts.get(health, 0) + 1
        reason = str(snapshot.get("reason") or "unknown")
        reason_counts[reason] = reason_counts.get(reason, 0) + 1
    latest = snapshots[-1]
    latest_age_s: int | None = None
    captured_ts = latest.get("captured_ts")
    try:
        captured_ts_float = float(captured_ts)
    except (TypeError, ValueError):
        captured_ts_float = 0.0
    if captured_ts_float:
        latest_age_s = int((time.time() if now_ts is None else now_ts) - captured_ts_float)
    latest_oracle = latest.get("oracle") or {}
    latest_discovery = latest.get("discovery") or {}
    latest_supervisor = latest.get("supervisor") or {}
    lines = [f"history_count={len(snapshots)}"]
    lines.append(
        "health_counts="
        + " ".join(f"{health}={count}" for health, count in sorted(counts.items()))
    )
    lines.append(
        "reason_counts="
        + " ".join(
            f"{reason}={count}" for reason, count in sorted(reason_counts.items())
        )
    )
    lines.append(
        "latest="
        f"{latest.get('captured_iso', 'unknown')} "
        f"{latest.get('health', 'unknown')}/{latest.get('reason', 'unknown')} "
        f"queue={latest_oracle.get('queue_length')} "
        f"busy={latest_oracle.get('agents_busy')} "
        f"runnable={latest_discovery.get('runnable')} "
        f"log_age_s={latest_supervisor.get('log_age_s')} "
        f"next_tick_eta_s={latest_supervisor.get('next_tick_eta_s')} "
        f"ready_not_manual={latest.get('ready_not_in_manual_count', 0)} "
        f"latest_age_s={latest_age_s}"
    )
    return "\n".join(lines)


def format_text_report(report: dict[str, Any]) -> str:
    lines = [f"health={report['health']} reason={report['reason']}"]
    lines.append(
        "oracle="
        f"{report['oracle']['diagnosis']} "
        f"queue={report['oracle']['queue_length']} "
        f"busy={report['oracle']['agents_busy']}/{report['oracle']['max_agents']}"
    )
    lines.append(
        "oracle_activity="
        f"completed={report['oracle'].get('completed')} "
        f"sessions={report['oracle'].get('active_sessions')} "
        f"registered_agents={report['oracle'].get('registered_agents')} "
        f"recent_agents={report['oracle'].get('active_recent_agents')} "
        f"queued_tasks={report['oracle'].get('queued_tasks_count')}"
    )
    d = report["discovery"]
    lines.append(
        "discovery="
        f"{d['diagnosis']} candidates={d['candidates']} runnable={d['runnable']} "
        f"status_skipped={d['status_skipped']}"
    )
    skip_categories = d.get("skip_categories") or {}
    if skip_categories:
        lines.append(
            "skip_categories="
            + " ".join(
                f"{category}={count}"
                for category, count in sorted(skip_categories.items())
            )
        )
    supervisor = report["supervisor"]
    lines.append(f"supervisor_log_age_s={supervisor['log_age_s']}")
    if supervisor.get("next_tick_eta_s") is not None:
        lines.append(f"supervisor_next_tick_eta_s={supervisor['next_tick_eta_s']}")
    if supervisor.get("pid") is not None:
        lines.append(
            "supervisor_pid="
            f"{supervisor['pid']} "
            f"alive={str(supervisor.get('pid_alive')).lower()} "
            f"script={supervisor.get('pid_script') or 'unknown'}"
        )
    else:
        lines.append("supervisor_pid=none alive=unknown")
    lines.append(
        "supervisor_code_changed_since_start="
        f"{str(supervisor['code_changed_since_start']).lower()}"
    )
    lines.append(f"manual_submission_count={report['manual_submission_count']}")
    for item in report["manual_submission_queue"][:5]:
        lines.append(
            "manual: "
            f"{item['paper']} -> {item['journal']} | {item['note']}"
        )
    if report.get("ready_not_in_manual_count"):
        lines.append(f"ready_not_in_manual_count={report['ready_not_in_manual_count']}")
        for item in report["ready_not_in_manual_queue"][:5]:
            lines.append(
                "ready_not_manual: "
                f"{item['paper']} -> {item['journal']} | {item['status']}"
            )
    for action in report["actions"]:
        lines.append(f"action: {action}")
    return "\n".join(lines)


def build_current_report(
    *,
    refill_project_url: str = "",
    oracle_status_reader=read_oracle_status,
    discovery_reader=discovery_summary,
    supervisor_log_reader=read_supervisor_log_lines,
    now_ts: float | None = None,
    supervisor_log_mtime_reader=supervisor_log_mtime,
    refill_queue_exists_reader=REFILL_QUEUE.exists,
    manual_submission_reader=read_manual_submission_queue,
    ready_submission_reader=read_ready_submission_entries,
    supervisor_code_mtime_reader=lambda: file_mtime(SCRIPT_DIR / "pipeline_supervisor.py"),
    supervisor_pid_record_reader=read_supervisor_pid_record,
    process_alive_reader=process_alive,
) -> dict[str, Any]:
    supervisor_log_lines = supervisor_log_reader()
    supervisor_tail = supervisor_log_lines[-40:]
    supervisor_pid_record = supervisor_pid_record_reader()
    supervisor_pid = supervisor_pid_record.get("pid")
    return build_health_report(
        oracle_status=oracle_status_reader(),
        discovery_summary=discovery_reader(),
        supervisor_tail=supervisor_tail,
        now_ts=time.time() if now_ts is None else now_ts,
        supervisor_log_mtime=supervisor_log_mtime_reader(),
        refill_queue_exists=refill_queue_exists_reader(),
        refill_project_url=refill_project_url,
        manual_submission_queue=manual_submission_reader(),
        ready_submission_entries=ready_submission_reader(),
        supervisor_code_mtime=supervisor_code_mtime_reader(),
        supervisor_started_ts=latest_supervisor_start_ts(supervisor_log_lines),
        supervisor_exited_ts=latest_supervisor_exit_ts(supervisor_log_lines),
        supervisor_last_log_ts=latest_supervisor_log_ts(supervisor_log_lines),
        supervisor_poll_s=latest_supervisor_poll_s(supervisor_log_lines),
        supervisor_pid=supervisor_pid,
        supervisor_pid_started_ts=supervisor_pid_record.get("started_ts"),
        supervisor_pid_script=str(supervisor_pid_record.get("script") or ""),
        supervisor_pid_alive=process_alive_reader(supervisor_pid),
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Emit JSON only")
    parser.add_argument("--check", action="store_true",
                        help="Return 0 for healthy/runnable, 1 for attention, 2 for blocked")
    parser.add_argument("--snapshot", action="store_true",
                        help=f"Append one JSONL snapshot to {HEALTH_SNAPSHOT_LOG}")
    parser.add_argument("--history", type=int, default=0,
                        help=f"Show the last N snapshots from {HEALTH_SNAPSHOT_LOG}")
    parser.add_argument("--max-snapshot-age-s", type=int, default=0,
                        help="With --history --check, fail if the latest snapshot is older than this")
    parser.add_argument("--refill-project-url", default="")
    args = parser.parse_args()

    report: dict[str, Any] | None = None
    if args.snapshot or not args.history:
        report = build_current_report(refill_project_url=args.refill_project_url)
    if args.snapshot:
        assert report is not None
        append_health_snapshot(report)
    if args.history:
        snapshots = read_health_snapshots(limit=args.history)
        print(format_history_report(snapshots))
        if args.check:
            return exit_code_for_history(
                snapshots,
                max_age_s=args.max_snapshot_age_s,
            )
        return 0
    assert report is not None
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(format_text_report(report))
    if args.check:
        return exit_code_for_report(report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
