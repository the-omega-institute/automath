#!/usr/bin/env python3
"""Lightweight watchdog for the Omega Outreach research harness.

This sits outside outreach_supervisor.py. Its job is operational, not
mathematical: keep the server/supervisor alive, report named active targets,
and trigger cheap reconciliation when browser/Oracle work completes late.

It never sends external email/posts/PRs. It also does not ask the operator to
refresh the userscript; refresh is a last-resort human action, not a watchdog
default.
"""

from __future__ import annotations

import argparse
import json
import os
import signal
import subprocess
import sys
import time
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_DIR = SCRIPT_DIR / "outreach_state"
WATCHDOG_LOG = STATE_DIR / "watchdog.log"
WATCHDOG_STATUS = STATE_DIR / "watchdog.status.json"
SUPERVISOR_LOG_DIR = STATE_DIR / "supervisor_logs"
SUPERVISOR_DAEMON_LOG = SUPERVISOR_LOG_DIR / "supervisor_daemon_current.log"
SUPERVISOR_RUNTIME = STATE_DIR / "supervisor.runtime.json"
RESEARCH_STATUS = STATE_DIR / "research_loop.status.json"
STOP_FILE = SCRIPT_DIR / ".outreach_stop"

ORACLE_SERVER_URL = os.environ.get("OUTREACH_ORACLE_SERVER_URL", "http://127.0.0.1:8766")
ORACLE_SERVER = SCRIPT_DIR / "outreach_oracle_server.py"
SUPERVISOR = SCRIPT_DIR / "outreach_supervisor.py"
ORACLE_RECONCILE = SCRIPT_DIR / "outreach_oracle_reconcile.py"
RESEARCH_BOARD = SCRIPT_DIR / "RESEARCH_BOARD.md"

DEFAULT_SUPERVISOR_ARGS = [
    "--poll-interval",
    "90",
    "--frontier-low-water",
    "3",
    "--parallel",
    "2",
    "--no-freshness-judge",
    "--auto-commit",
]

_PS_LAST_ERROR = ""


def _now() -> float:
    return time.time()


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def log(msg: str) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {msg}"
    print(line, flush=True)
    with WATCHDOG_LOG.open("a", encoding="utf-8") as f:
        f.write(line + "\n")


def _read_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def _write_status(payload: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    WATCHDOG_STATUS.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _ps_rows() -> list[dict]:
    global _PS_LAST_ERROR
    try:
        proc = subprocess.run(
            ["ps", "-axo", "pid,ppid,pgid,etime,stat,command"],
            capture_output=True,
            text=True,
            timeout=5,
            check=False,
        )
    except Exception as exc:  # noqa: BLE001
        _PS_LAST_ERROR = str(exc)
        return []
    if proc.returncode != 0:
        _PS_LAST_ERROR = (proc.stderr or proc.stdout or f"ps rc={proc.returncode}")[:500]
        return []
    _PS_LAST_ERROR = ""
    rows: list[dict] = []
    for line in (proc.stdout or "").splitlines()[1:]:
        parts = line.strip().split(None, 5)
        if len(parts) < 6:
            continue
        try:
            pid = int(parts[0])
            ppid = int(parts[1])
            pgid = int(parts[2])
        except ValueError:
            continue
        rows.append({
            "pid": pid,
            "ppid": ppid,
            "pgid": pgid,
            "etime": parts[3],
            "stat": parts[4],
            "command": parts[5],
        })
    return rows


def _ps_available() -> bool:
    return not _PS_LAST_ERROR


def _script_rows(script_name: str) -> list[dict]:
    needle1 = f"tools/community-outreach/{script_name}"
    needle2 = f"/{script_name}"
    return [
        r for r in _ps_rows()
        if needle1 in r["command"] or needle2 in r["command"]
    ]


def _git_head() -> str:
    try:
        proc = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
    except Exception:
        return ""
    if proc.returncode != 0:
        return ""
    return proc.stdout.strip()


def _server_status(timeout: int = 5) -> dict:
    try:
        with urllib.request.urlopen(f"{ORACLE_SERVER_URL}/status", timeout=timeout) as r:
            return json.loads(r.read().decode("utf-8"), strict=False)
    except Exception:
        try:
            proc = subprocess.run(
                ["curl", "-fsS", "--max-time", str(max(1, int(timeout))), f"{ORACLE_SERVER_URL}/status"],
                cwd=str(REPO_ROOT),
                capture_output=True,
                text=True,
                timeout=timeout + 2,
                check=False,
            )
            if proc.returncode == 0:
                return json.loads(proc.stdout or "{}", strict=False)
        except Exception:
            pass
        return {}


def _spawn_server() -> int | None:
    if not ORACLE_SERVER.exists():
        log("oracle_server: script missing; cannot spawn")
        return None
    existing = _script_rows("outreach_oracle_server.py")
    if existing:
        log("oracle_server: status endpoint unavailable but process exists; not spawning duplicate")
        return None
    proc = subprocess.Popen(
        ["python3", str(ORACLE_SERVER)],
        cwd=str(REPO_ROOT),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )
    log(f"oracle_server: spawned pid={proc.pid}")
    return proc.pid


def _server_process_exists() -> bool:
    return bool(_script_rows("outreach_oracle_server.py"))


def _spawn_supervisor(supervisor_args: list[str]) -> int | None:
    if not SUPERVISOR.exists():
        log("supervisor: script missing; cannot spawn")
        return None
    try:
        STOP_FILE.unlink()
        log("supervisor: removed stale .outreach_stop before spawn")
    except FileNotFoundError:
        pass
    except OSError as exc:
        log(f"supervisor: could not remove .outreach_stop: {exc}")
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    logf = SUPERVISOR_DAEMON_LOG.open("ab")
    logf.write(f"\n=== watchdog supervisor spawn at {_now_iso()} ===\n".encode())
    logf.flush()
    proc = subprocess.Popen(
        ["python3", "-u", str(SUPERVISOR), *supervisor_args],
        cwd=str(REPO_ROOT),
        stdout=logf,
        stderr=subprocess.STDOUT,
        start_new_session=True,
    )
    log(f"supervisor: spawned pid={proc.pid} args={' '.join(supervisor_args)}")
    return proc.pid


def _pid_alive(pid: int) -> bool:
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
        return True
    except (ProcessLookupError, OSError):
        return False


def _runtime_supervisor_alive() -> bool:
    runtime = _read_json(SUPERVISOR_RUNTIME)
    try:
        pid = int(runtime.get("pid") or 0)
    except (TypeError, ValueError):
        pid = 0
    return _pid_alive(pid)


def _reconcile_deep() -> dict:
    if not ORACLE_RECONCILE.exists():
        return {}
    try:
        proc = subprocess.run(
            ["python3", str(ORACLE_RECONCILE), "--deep", "--json"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )
    except Exception as exc:
        return {"error": str(exc)}
    if proc.returncode != 0:
        return {"rc": proc.returncode, "error": (proc.stderr or proc.stdout or "")[:500]}
    try:
        return json.loads(proc.stdout or "{}")
    except json.JSONDecodeError:
        return {"error": "invalid json", "stdout": (proc.stdout or "")[:500]}


def _load_titles() -> dict[str, str]:
    titles: dict[str, str] = {}
    try:
        text = RESEARCH_BOARD.read_text(encoding="utf-8")
    except OSError:
        return titles
    for line in text.splitlines():
        if not line.startswith("### T-"):
            continue
        # Format: ### T-07 · OPG · Pierce ...
        parts = line[4:].split(" · ", 1)
        if len(parts) == 2:
            titles[parts[0].strip()] = parts[1].strip()
    return titles


def _active_named_targets() -> list[dict]:
    status = _read_json(RESEARCH_STATUS)
    titles = _load_titles()
    out = []
    for row in status.get("active") or []:
        if not isinstance(row, dict):
            continue
        tid = str(row.get("todo_id") or "")
        out.append({
            "todo_id": tid,
            "slug": row.get("slug"),
            "title": titles.get(tid, tid),
        })
    return out


def _kill_orphan_inner_dedup(dry_run: bool = False) -> list[int]:
    """Remove old orphan task/writeback daemons whose supervisor is gone.

    We do not touch dispatch_worktree here because it may hold active
    mathematical work.  We do clean orphan outreach_research_loop daemons once
    a supervisor exists: a parentless research loop keeps selecting new board
    targets and can duplicate the supervised harness.
    """
    killed: list[int] = []
    rows = _ps_rows()
    supervisor_pids = {
        r["pid"] for r in rows
        if "outreach_supervisor.py" in r["command"] and "outreach_watchdog.py" not in r["command"]
    }
    for script in (
        "outreach_research_loop.py",
        "outreach_task_runner.py",
        "outreach_writeback_loop.py",
    ):
        for row in rows:
            if script not in row["command"]:
                continue
            if row["ppid"] in supervisor_pids:
                continue
            # Keep one orphan if no supervisor exists; otherwise it is duplicate noise.
            if not supervisor_pids:
                continue
            killed.append(row["pid"])
            if not dry_run:
                try:
                    os.killpg(row["pgid"], signal.SIGTERM)
                except (ProcessLookupError, OSError):
                    try:
                        os.kill(row["pid"], signal.SIGTERM)
                    except (ProcessLookupError, OSError):
                        pass
    return killed


def _has_active_pipeline_work(server: dict) -> bool:
    if int(server.get("agents_busy") or 0) > 0:
        return True
    if int(server.get("queue_length") or 0) > 0:
        return True
    for script in ("dispatch_worktree.py", "outreach_board_refill.py", "outreach_local_repair.py"):
        if _script_rows(script):
            return True
    return False


def _observer_unreliable(server: dict) -> bool:
    """True when watchdog cannot safely decide process/browser idleness."""
    if _PS_LAST_ERROR:
        return True
    if server.get("port") != 8766:
        return True
    return False


def _request_safe_supervisor_restart_if_code_changed(server: dict) -> str:
    """Ask the supervisor to restart after a commit, but only at an idle boundary.

    Python daemons keep the module code they imported at process start.  After a
    pipeline architecture commit, a live supervisor/research loop can otherwise
    keep running old prompt/gate logic for hours.  The watchdog records the HEAD
    used by the current supervisor and writes .outreach_stop only once all
    browser/dispatch work is idle, so active Oracle reasoning is not cut off.
    """
    runtime = _read_json(SUPERVISOR_RUNTIME)
    runtime_head = str(runtime.get("git_head") or "").strip()
    current_head = _git_head()
    if not runtime_head or not current_head or runtime_head == current_head:
        return ""
    if _observer_unreliable(server):
        return f"restart_deferred_observer_unreliable:{runtime_head[:9]}->{current_head[:9]}"
    if _has_active_pipeline_work(server):
        return f"restart_deferred_code_changed:{runtime_head[:9]}->{current_head[:9]}"
    try:
        STOP_FILE.write_text(
            f"watchdog requested safe restart at {_now_iso()}: "
            f"{runtime_head} -> {current_head}\n",
            encoding="utf-8",
        )
    except OSError as exc:
        return f"restart_request_failed:{exc}"
    return f"restart_supervisor_code_changed:{runtime_head[:9]}->{current_head[:9]}"


def _supervisor_code_status(server: dict) -> dict:
    """Expose whether the live supervisor predates the checked-out code.

    The watchdog may correctly defer a restart while Oracle/dispatch work is
    active.  That deferment needs to be visible in status reports; otherwise an
    operator cannot tell whether new harness code is already running or merely
    waiting for a safe idle boundary.
    """
    runtime = _read_json(SUPERVISOR_RUNTIME)
    runtime_head = str(runtime.get("git_head") or "").strip()
    current_head = _git_head()
    observer_unreliable = _observer_unreliable(server)
    active = True if observer_unreliable else _has_active_pipeline_work(server)
    stale = bool(runtime_head and current_head and runtime_head != current_head)
    return {
        "current_git_head": current_head,
        "supervisor_git_head": runtime_head,
        "supervisor_pid": runtime.get("pid"),
        "supervisor_code_stale": stale,
        "safe_restart_deferred": bool(stale and active),
        "safe_restart_blocker": (
            "observer_unreliable" if stale and observer_unreliable
            else "active_pipeline_work" if stale and active
            else ""
        ),
    }


def one_tick(*, supervisor_args: list[str], stale_reconcile_seconds: int, cleanup_orphans: bool) -> dict:
    rows = _ps_rows()
    ps_ok = _ps_available()
    server = _server_status()
    actions: list[str] = []

    if server.get("port") != 8766:
        if _server_process_exists():
            actions.append("oracle_server_status_unreachable_process_exists")
            log("oracle_server: status endpoint unavailable but process exists; deferring spawn")
            time.sleep(2)
            server = _server_status()
        elif not ps_ok:
            actions.append("oracle_server_unobservable_ps_failed")
            log(f"oracle_server: status unavailable and ps failed; not spawning duplicate ({_PS_LAST_ERROR})")
        else:
            _spawn_server()
            actions.append("spawn_oracle_server")
            time.sleep(3)
            server = _server_status()

    supervisor_rows = [
        r for r in rows
        if "outreach_supervisor.py" in r["command"] and "outreach_watchdog.py" not in r["command"]
    ]
    if not supervisor_rows:
        if _runtime_supervisor_alive():
            actions.append("supervisor_ps_missing_runtime_alive")
        elif not ps_ok:
            actions.append("supervisor_unobservable_ps_failed")
            log(f"supervisor: ps failed and no trusted runtime pid; not spawning duplicate ({_PS_LAST_ERROR})")
        else:
            _spawn_supervisor(supervisor_args)
            actions.append("spawn_supervisor")

    killed_orphans: list[int] = []
    if cleanup_orphans:
        killed_orphans = _kill_orphan_inner_dedup()
        if killed_orphans:
            actions.append(f"kill_orphan_inner:{','.join(map(str, killed_orphans))}")

    server = _server_status()
    code_status = _supervisor_code_status(server)
    restart_action = _request_safe_supervisor_restart_if_code_changed(server)
    if restart_action:
        actions.append(restart_action)
    active_named = _active_named_targets()
    stale_busy = server.get("stale_busy_agents") or []
    reconcile_payload: dict = {}
    # Cheap recovery: if the browser bridge thinks work may be stale, or no
    # target is active while Oracle has completed tasks, reconcile saved deep
    # output into target artifacts.
    if stale_busy or int(server.get("completed") or 0) > 0:
        last = _read_json(WATCHDOG_STATUS).get("last_reconcile_ts") or 0
        try:
            last_f = float(last)
        except (TypeError, ValueError):
            last_f = 0.0
        if _now() - last_f >= stale_reconcile_seconds:
            reconcile_payload = _reconcile_deep()
            actions.append("oracle_reconcile_deep")

    payload = {
        "checked_at": _now_iso(),
        "actions": actions,
        "oracle": {
            "ok": server.get("port") == 8766,
            "diagnosis": server.get("diagnosis"),
            "queue_length": server.get("queue_length"),
            "agents_busy": server.get("agents_busy"),
            "max_agents": server.get("max_agents"),
            "stale_busy_agents": stale_busy,
            "active_tasks": server.get("agents") or {},
            "recent_agents": {
                k: {
                    "idle_seconds": v.get("idle_seconds"),
                    "script_version": (v.get("metrics") or {}).get("script_version"),
                    "task_id": (v.get("metrics") or {}).get("task_id"),
                    "phase": (v.get("metrics") or {}).get("phase"),
                    "generating": ((v.get("metrics") or {}).get("generation") or {}).get("generating"),
                    "extracted_chars": (v.get("metrics") or {}).get("extracted_chars"),
                }
                for k, v in (server.get("recent_agents") or {}).items()
                if isinstance(v, dict)
            },
        },
        "processes": {
            "supervisor": _script_rows("outreach_supervisor.py"),
            "research_loop": _script_rows("outreach_research_loop.py"),
            "dispatch_worktree": _script_rows("dispatch_worktree.py"),
            "board_refill": _script_rows("outreach_board_refill.py"),
        },
        "process_observer": {
            "ps_ok": ps_ok,
            "ps_error": _PS_LAST_ERROR,
        },
        "code_status": code_status,
        "active_named_targets": active_named,
        "reconcile": reconcile_payload,
    }
    if reconcile_payload:
        payload["last_reconcile_ts"] = _now()
    else:
        previous = _read_json(WATCHDOG_STATUS).get("last_reconcile_ts")
        if previous is not None:
            payload["last_reconcile_ts"] = previous
    _write_status(payload)

    target_text = ", ".join(t["title"] for t in active_named) or "-"
    log(
        "health: "
        f"oracle={payload['oracle']['diagnosis']} "
        f"busy={payload['oracle']['agents_busy']}/{payload['oracle']['max_agents']} "
        f"active={target_text} "
        f"actions={','.join(actions) or '-'}"
    )
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description="Watchdog for the Omega Outreach harness")
    parser.add_argument("--loop", action="store_true", help="run continuously")
    parser.add_argument("--interval", type=int, default=60)
    parser.add_argument("--stale-reconcile-seconds", type=int, default=300)
    parser.add_argument("--cleanup-orphans", action="store_true")
    parser.add_argument(
        "--supervisor-arg",
        action="append",
        default=[],
        help="override supervisor args; pass multiple times, otherwise project defaults are used",
    )
    args = parser.parse_args()

    supervisor_args = args.supervisor_arg or DEFAULT_SUPERVISOR_ARGS
    log(
        f"watchdog starting loop={args.loop} interval={args.interval}s "
        f"cleanup_orphans={args.cleanup_orphans} supervisor_args={' '.join(supervisor_args)}"
    )

    while True:
        one_tick(
            supervisor_args=supervisor_args,
            stale_reconcile_seconds=args.stale_reconcile_seconds,
            cleanup_orphans=args.cleanup_orphans,
        )
        if not args.loop:
            return 0
        time.sleep(max(10, args.interval))


if __name__ == "__main__":
    raise SystemExit(main())
