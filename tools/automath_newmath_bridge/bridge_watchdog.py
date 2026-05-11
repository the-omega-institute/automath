#!/usr/bin/env python3
"""Independent watchdog for persistent Automath-NewMath bridge loops.

The bridge supervisor scans and gates. The heavy loop runs slower synthesis
and adapter dry-runs. The production loop turns eligible synthesis output into
durable receiving indexes. This watchdog supervises those loops without
becoming part of any work queue: it checks log freshness, stderr growth, stale
locks, Git branch drift, and optional safe pushes for local codex audit
branches.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_CONFIG = SCRIPT_DIR / "bridge_pipeline_config.json"
STOP_FILE = SCRIPT_DIR / ".bridge_watchdog.stop"
LOCK_FILE = SCRIPT_DIR / "state" / "bridge_watchdog.lock"
LOG_FILE = SCRIPT_DIR / "logs" / "bridge_watchdog.log"
STATUS_FILE = SCRIPT_DIR / "state" / "bridge_watchdog_status.json"

SUPERVISOR_STDOUT = SCRIPT_DIR / "logs" / "persistent_supervisor_stdout.log"
SUPERVISOR_STDERR = SCRIPT_DIR / "logs" / "persistent_supervisor_stderr.log"
HEAVY_LOG = SCRIPT_DIR / "logs" / "bridge_heavy_loop.log"
HEAVY_STDERR = SCRIPT_DIR / "logs" / "persistent_heavy_loop_stderr.log"
PRODUCTION_LOG = SCRIPT_DIR / "logs" / "bridge_production_loop.log"
PRODUCTION_STDERR = SCRIPT_DIR / "logs" / "persistent_production_loop_stderr.log"


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def _log(message: str) -> None:
    LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {message}"
    print(line, flush=True)
    with LOG_FILE.open("a", encoding="utf-8") as handle:
        handle.write(line + "\n")


def _git(args: list[str], *, timeout: int = 120) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", *args], cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=timeout, check=False)


def _git_stdout(args: list[str], *, timeout: int = 120) -> str:
    result = _git(args, timeout=timeout)
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout or "git command failed").strip())
    return result.stdout.strip()


def _git_dir() -> Path:
    path = Path(_git_stdout(["rev-parse", "--git-dir"], timeout=30))
    if not path.is_absolute():
        path = (REPO_ROOT / path).resolve()
    return path


def _load_config(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8-sig"))
    if not isinstance(data, dict):
        raise ValueError(f"Expected object JSON in {path}")
    return data


def _file_age_seconds(path: Path) -> float | None:
    try:
        return time.time() - path.stat().st_mtime
    except FileNotFoundError:
        return None


def _file_size(path: Path) -> int:
    try:
        return path.stat().st_size
    except FileNotFoundError:
        return 0


def _tail(path: Path, limit: int = 1200) -> str:
    try:
        data = path.read_bytes()
    except FileNotFoundError:
        return ""
    return data[-limit:].decode("utf-8", errors="replace")


def _json_dump(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _acquire_lock(*, stale_seconds: int) -> int | None:
    LOCK_FILE.parent.mkdir(parents=True, exist_ok=True)
    try:
        fd = os.open(str(LOCK_FILE), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        os.write(fd, f"pid={os.getpid()}\ncreated_at={_now_iso()}\n".encode("utf-8"))
        return fd
    except FileExistsError:
        try:
            if time.time() - LOCK_FILE.stat().st_mtime > stale_seconds:
                LOCK_FILE.unlink()
                return _acquire_lock(stale_seconds=stale_seconds)
        except FileNotFoundError:
            return _acquire_lock(stale_seconds=stale_seconds)
        return None


def _release_lock(fd: int | None) -> None:
    if fd is not None:
        os.close(fd)
    try:
        LOCK_FILE.unlink()
    except FileNotFoundError:
        pass


def _python_bridge_processes() -> list[dict[str, Any]]:
    if sys.platform.startswith("win"):
        return _windows_bridge_processes()
    return _posix_bridge_processes()


def _windows_bridge_processes() -> list[dict[str, Any]]:
    ps_script = (
        "Get-CimInstance Win32_Process | "
        "Where-Object { "
        "($_.CommandLine -like '*bridge_supervisor.py*' -or "
        "$_.CommandLine -like '*bridge_heavy_loop.py*' -or "
        "$_.CommandLine -like '*bridge_production_loop.py*' -or "
        "$_.CommandLine -like '*bridge_watchdog.py*') -and "
        "$_.ExecutablePath -like '*Python*' "
        "} | Select-Object ProcessId,ParentProcessId,CreationDate,CommandLine | ConvertTo-Json -Depth 3"
    )
    for shell in ("powershell", "pwsh"):
        try:
            result = subprocess.run([shell, "-NoProfile", "-Command", ps_script], capture_output=True, text=True, timeout=30, check=False)
        except FileNotFoundError:
            continue
        if result.returncode != 0 or not result.stdout.strip():
            continue
        data = json.loads(result.stdout)
        if isinstance(data, dict):
            data = [data]
        if not isinstance(data, list):
            return []
        return [item for item in data if isinstance(item, dict)]
    return []


def _posix_bridge_processes() -> list[dict[str, Any]]:
    result = subprocess.run(["ps", "-axo", "pid=,ppid=,command="], capture_output=True, text=True, timeout=30, check=False)
    if result.returncode != 0:
        return []
    needles = ("bridge_supervisor.py", "bridge_heavy_loop.py", "bridge_production_loop.py", "bridge_watchdog.py")
    processes: list[dict[str, Any]] = []
    for line in result.stdout.splitlines():
        parts = line.strip().split(None, 2)
        if len(parts) != 3:
            continue
        pid, ppid, command = parts
        if not any(needle in command for needle in needles):
            continue
        processes.append(
            {
                "ProcessId": pid,
                "ParentProcessId": ppid,
                "CreationDate": "",
                "CommandLine": command,
            }
        )
    return processes


def _count_processes(processes: list[dict[str, Any]], needle: str, repo_marker: str) -> int:
    count = 0
    for proc in processes:
        command = str(proc.get("CommandLine") or "").replace("\\", "/")
        if needle in command and (not repo_marker or repo_marker in command):
            count += 1
    return count


def _git_status(*, push_safe_current_branch: bool) -> dict[str, Any]:
    branch = _git_stdout(["branch", "--show-current"], timeout=30)
    porcelain = _git_stdout(["status", "--porcelain"], timeout=30)
    tracked = _git_stdout(["status", "--porcelain", "--untracked-files=no"], timeout=30)
    upstream = ""
    ahead = 0
    behind = 0
    push: dict[str, Any] = {"attempted": False}
    upstream_result = _git(["rev-parse", "--abbrev-ref", "--symbolic-full-name", "@{u}"], timeout=30)
    if upstream_result.returncode == 0:
        upstream = upstream_result.stdout.strip()
        counts = _git_stdout(["rev-list", "--left-right", "--count", f"{upstream}...HEAD"], timeout=60).split()
        if len(counts) == 2:
            behind = int(counts[0])
            ahead = int(counts[1])
    if push_safe_current_branch and ahead > 0:
        if not branch.startswith("codex/"):
            push = {"attempted": False, "blocked": f"current branch {branch!r} is not a codex/* audit branch"}
        elif tracked.strip():
            push = {"attempted": False, "blocked": "tracked worktree changes exist"}
        else:
            result = _git(["push", "origin", branch], timeout=300)
            push = {
                "attempted": True,
                "returncode": result.returncode,
                "status": "ok" if result.returncode == 0 else "failed",
                "stdout_tail": result.stdout[-1200:],
                "stderr_tail": result.stderr[-1200:],
            }
    return {
        "branch": branch,
        "upstream": upstream,
        "ahead": ahead,
        "behind": behind,
        "porcelain_lines": [line for line in porcelain.splitlines() if line.strip()],
        "tracked_lines": [line for line in tracked.splitlines() if line.strip()],
        "push": push,
    }


def _stale_lock_checks(stale_lock_seconds: int) -> list[dict[str, Any]]:
    locks = [
        SCRIPT_DIR / "state" / "bridge_heavy_loop.lock",
        _git_dir() / "omega_bridge_fetch.lock",
    ]
    checks = []
    for path in locks:
        age = _file_age_seconds(path)
        checks.append(
            {
                "path": str(path.relative_to(REPO_ROOT) if path.is_relative_to(REPO_ROOT) else path),
                "exists": age is not None,
                "age_seconds": None if age is None else round(age, 3),
                "stale": age is not None and age > stale_lock_seconds,
            }
        )
    return checks


def run_once(args: argparse.Namespace) -> bool:
    config = _load_config(Path(args.config).resolve())
    processes = _python_bridge_processes()
    git_status = _git_status(push_safe_current_branch=args.push_safe_current_branch)
    supervisor_age = _file_age_seconds(SUPERVISOR_STDOUT)
    heavy_age = _file_age_seconds(HEAVY_LOG)
    production_age = _file_age_seconds(PRODUCTION_LOG)
    supervisor_stderr_size = _file_size(SUPERVISOR_STDERR)
    heavy_stderr_size = _file_size(HEAVY_STDERR)
    production_stderr_size = _file_size(PRODUCTION_STDERR)
    locks = _stale_lock_checks(args.stale_lock_seconds)
    repo_marker = args.repo_marker.replace("\\", "/")
    status = {
        "checked_at": _now_iso(),
        "repo": str(REPO_ROOT),
        "configured_required_branch": config.get("required_branch"),
        "git": git_status,
        "process_count_scope": "repo-marker" if repo_marker else "global",
        "process_counts": {
            "bridge_supervisor": _count_processes(processes, "bridge_supervisor.py", repo_marker),
            "bridge_heavy_loop": _count_processes(processes, "bridge_heavy_loop.py", repo_marker),
            "bridge_production_loop": _count_processes(processes, "bridge_production_loop.py", repo_marker),
            "bridge_watchdog": _count_processes(processes, "bridge_watchdog.py", repo_marker),
        },
        "logs": {
            "supervisor_stdout_age_seconds": None if supervisor_age is None else round(supervisor_age, 3),
            "supervisor_stderr_size": supervisor_stderr_size,
            "supervisor_stderr_tail": _tail(SUPERVISOR_STDERR) if supervisor_stderr_size else "",
            "heavy_log_age_seconds": None if heavy_age is None else round(heavy_age, 3),
            "heavy_stderr_size": heavy_stderr_size,
            "heavy_stderr_tail": _tail(HEAVY_STDERR) if heavy_stderr_size else "",
            "production_log_age_seconds": None if production_age is None else round(production_age, 3),
            "production_stderr_size": production_stderr_size,
            "production_stderr_tail": _tail(PRODUCTION_STDERR) if production_stderr_size else "",
        },
        "locks": locks,
        "stop_files": {
            "supervisor": (SCRIPT_DIR / ".bridge_supervisor.stop").exists(),
            "heavy_loop": (SCRIPT_DIR / ".bridge_heavy_loop.stop").exists(),
            "production_loop": (SCRIPT_DIR / ".bridge_production_loop.stop").exists(),
            "watchdog": STOP_FILE.exists(),
        },
    }
    issues: list[str] = []
    if args.min_supervisor_processes > 0:
        if supervisor_age is None:
            issues.append("missing persistent supervisor stdout log")
        elif supervisor_age > args.max_supervisor_log_age:
            issues.append(f"supervisor log stale: {round(supervisor_age, 1)}s")
        if supervisor_stderr_size:
            issues.append(f"supervisor stderr is non-empty: {supervisor_stderr_size} bytes")
    if args.min_heavy_processes > 0:
        if heavy_age is None:
            issues.append("missing heavy loop log")
        elif heavy_age > args.max_heavy_log_age:
            issues.append(f"heavy loop log stale: {round(heavy_age, 1)}s")
        if heavy_stderr_size:
            issues.append(f"heavy loop stderr is non-empty: {heavy_stderr_size} bytes")
    if args.min_production_processes > 0:
        if production_age is None:
            issues.append("missing production loop log")
        elif production_age > args.max_production_log_age:
            issues.append(f"production loop log stale: {round(production_age, 1)}s")
        if production_stderr_size:
            issues.append(f"production loop stderr is non-empty: {production_stderr_size} bytes")
    if git_status["behind"]:
        issues.append(f"current branch is behind upstream by {git_status['behind']} commit(s)")
    if any(item["stale"] for item in locks):
        issues.append("one or more bridge lock files are stale")
    if status["process_counts"]["bridge_supervisor"] < args.min_supervisor_processes:
        issues.append("fewer bridge supervisor processes than expected")
    if status["process_counts"]["bridge_heavy_loop"] < args.min_heavy_processes:
        issues.append("fewer bridge heavy loop processes than expected")
    if status["process_counts"]["bridge_production_loop"] < args.min_production_processes:
        issues.append("fewer bridge production loop processes than expected")
    status["issues"] = issues
    status["ok"] = not issues
    _json_dump(STATUS_FILE, status)
    level = "ok" if status["ok"] else "issue"
    _log(f"{level}: {json.dumps(status, ensure_ascii=False, sort_keys=True)}")
    return bool(status["ok"])


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Supervise persistent bridge loops without joining the scan or heavy queues")
    parser.add_argument("--config", default=str(DEFAULT_CONFIG))
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--poll-interval", type=int, default=900)
    parser.add_argument("--max-supervisor-log-age", type=int, default=900)
    parser.add_argument("--max-heavy-log-age", type=int, default=2700)
    parser.add_argument("--max-production-log-age", type=int, default=2700)
    parser.add_argument("--stale-lock-seconds", type=int, default=1800)
    parser.add_argument("--repo-marker", default="")
    parser.add_argument("--min-supervisor-processes", type=int, default=2)
    parser.add_argument("--min-heavy-processes", type=int, default=2)
    parser.add_argument("--min-production-processes", type=int, default=0)
    parser.add_argument("--push-safe-current-branch", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    fd = _acquire_lock(stale_seconds=args.stale_lock_seconds)
    if fd is None:
        _log(f"skip: another watchdog owns {LOCK_FILE}")
        return 0
    try:
        while True:
            try:
                ok = run_once(args)
            except Exception as exc:
                _log(f"watchdog pass failed: {exc}")
                ok = False
            if args.once or STOP_FILE.exists():
                return 0 if ok else 1
            time.sleep(max(60, args.poll_interval))
    finally:
        _release_lock(fd)


if __name__ == "__main__":
    raise SystemExit(main())
