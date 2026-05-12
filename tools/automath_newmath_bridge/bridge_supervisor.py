#!/usr/bin/env python3
"""Periodic supervisor for the Automath-NewMath bridge.

The supervisor mirrors the local distillation/oracle pipeline style:

- require the expected branch;
- honor a stop file;
- fetch the latest refs for both repos;
- run the bridge discovery pipeline;
- run deterministic gates;
- optionally write local review packets;
- optionally invoke Automath-native Killo/golden distillation writeback;
- optionally push only the Automath bridge branch after successful writeback;
- keep runtime artifacts local-only and ignored by Git.

It never sends, publishes, submits, checks out dev, or writes outreach state.
Paper writes are only allowed through Automath-native distillation/Claude
writeback gates when explicitly requested.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from bridge_gates import gate_records, read_jsonl, write_jsonl
except ModuleNotFoundError:  # pragma: no cover
    from tools.automath_newmath_bridge.bridge_gates import gate_records, read_jsonl, write_jsonl


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_CONFIG = SCRIPT_DIR / "bridge_pipeline_config.json"
STOP_FILE = SCRIPT_DIR / ".bridge_supervisor.stop"
LOG_DIR = SCRIPT_DIR / "logs"
PACKET_DIR = SCRIPT_DIR / "inbox" / "writeback_packets"
WRITEBACK_LOG = LOG_DIR / "automath_writeback_background.log"


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def _log(message: str) -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {message}"
    print(line, flush=True)
    with (LOG_DIR / "bridge_supervisor.log").open("a", encoding="utf-8") as handle:
        handle.write(line + "\n")


def _git(repo: Path, args: list[str], *, timeout: int = 180) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=str(repo),
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )


def _git_stdout(repo: Path, args: list[str], *, timeout: int = 120) -> str:
    result = _git(repo, args, timeout=timeout)
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout or "git command failed").strip())
    return result.stdout.strip()


@contextmanager
def repo_fetch_lock(repo: Path, *, timeout: int = 600):
    """Serialize fetches against a local repo across bridge supervisors."""
    lock_path = repo / ".git" / "automath_newmath_bridge.fetch.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    deadline = time.monotonic() + timeout
    with lock_path.open("a+b") as handle:
        handle.seek(0, os.SEEK_END)
        if handle.tell() == 0:
            handle.write(b"\0")
            handle.flush()
        handle.seek(0)
        if os.name == "nt":
            import msvcrt

            while True:
                try:
                    msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                    break
                except OSError:
                    if time.monotonic() >= deadline:
                        raise TimeoutError(f"Timed out waiting for fetch lock {lock_path}")
                    time.sleep(1)
            try:
                yield
            finally:
                handle.seek(0)
                msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
        else:
            import fcntl

            while True:
                try:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    if time.monotonic() >= deadline:
                        raise TimeoutError(f"Timed out waiting for fetch lock {lock_path}")
                    time.sleep(1)
            try:
                yield
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


@contextmanager
def repo_git_write_lock(repo: Path, *, timeout: int = 900):
    """Serialize local git index writes across bridge loops in one repo."""
    lock_path = repo / ".git" / "automath_newmath_bridge.git_write.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    deadline = time.monotonic() + timeout
    with lock_path.open("a+b") as handle:
        handle.seek(0, os.SEEK_END)
        if handle.tell() == 0:
            handle.write(b"\0")
            handle.flush()
        handle.seek(0)
        if os.name == "nt":
            import msvcrt

            while True:
                try:
                    msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                    break
                except OSError:
                    if time.monotonic() >= deadline:
                        raise TimeoutError(f"Timed out waiting for git write lock {lock_path}")
                    time.sleep(1)
            try:
                yield
            finally:
                handle.seek(0)
                msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
        else:
            import fcntl

            while True:
                try:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    if time.monotonic() >= deadline:
                        raise TimeoutError(f"Timed out waiting for git write lock {lock_path}")
                    time.sleep(1)
            try:
                yield
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def current_branch(repo: Path) -> str:
    return _git_stdout(repo, ["branch", "--show-current"], timeout=30)


def ensure_branch(expected: str) -> None:
    branch = current_branch(REPO_ROOT)
    if branch != expected:
        raise RuntimeError(
            f"Refusing to run on branch {branch!r}; expected {expected!r}. "
            "The bridge supervisor never checks out dev or outreach branches."
        )


def expected_branch_from_config(config_path: Path, fallback: str) -> str:
    try:
        config = _load_config(config_path)
    except Exception:
        return fallback
    return str(config.get("required_branch") or fallback)


def tracked_dirty_lines(repo: Path) -> list[str]:
    output = _git_stdout(repo, ["status", "--porcelain", "--untracked-files=no"], timeout=30)
    return [line for line in output.splitlines() if line.strip()]


def _status_paths(repo: Path) -> list[str]:
    output = _git_stdout(repo, ["status", "--porcelain"], timeout=30)
    paths: list[str] = []
    for line in output.splitlines():
        if not line.strip():
            continue
        raw = line[3:] if len(line) > 3 and line[2] == " " else line[2:]
        if " -> " in raw:
            raw = raw.split(" -> ", 1)[1]
        path = raw.strip().strip('"')
        if path:
            paths.append(path.replace("\\", "/"))
    return paths


def _is_bridge_runtime_path(path: str) -> bool:
    blocked_prefixes = (
        "tools/automath_newmath_bridge/inbox/",
        "tools/automath_newmath_bridge/out/",
        "tools/automath_newmath_bridge/state/",
        "tools/automath_newmath_bridge/logs/",
        "papers/publication/backflow/.distillation/",
    )
    return path.startswith(blocked_prefixes)


def _allowed_durable_path(path: str) -> bool:
    if "__pycache__/" in path or path.endswith((".pyc", ".pyo")):
        return False
    if path.startswith("tools/automath_newmath_bridge/") and _is_bridge_runtime_path(path):
        return False
    if path.startswith(("docs/bridge/", "tools/automath_newmath_bridge/")):
        return True
    if path == "papers/publication/backflow/source_queue.json":
        return True
    return False


def commit_and_push_durable(repo: Path, *, message: str, push: bool) -> dict[str, Any]:
    with repo_git_write_lock(repo):
        branch = current_branch(repo)
        all_paths = _status_paths(repo)
        paths = [path for path in all_paths if _allowed_durable_path(path)]
        skipped = [path for path in all_paths if path not in paths]
        if not paths:
            return {"status": "nothing_to_commit", "branch": branch, "skipped": skipped[:20]}
        add = _git(repo, ["add", *paths], timeout=60)
        if add.returncode != 0:
            return {"status": "add_failed", "branch": branch, "stderr": add.stderr.strip()[:1000]}
        diff = _git(repo, ["diff", "--cached", "--quiet"], timeout=60)
        if diff.returncode == 0:
            return {"status": "nothing_to_commit", "branch": branch, "paths": paths, "skipped": skipped[:20]}
        commit = _git(repo, ["commit", "-m", message], timeout=180)
        if commit.returncode != 0:
            return {"status": "commit_failed", "branch": branch, "stderr": commit.stderr.strip()[:1000]}
        result: dict[str, Any] = {
            "status": "committed",
            "branch": branch,
            "paths": paths,
            "skipped": skipped[:20],
            "stdout": commit.stdout.strip()[:1000],
        }
        if push:
            if not branch.startswith(("bridge/", "codex/")):
                result["push"] = f"skipped branch {branch}"
            else:
                pushed = _git(repo, ["push", "origin", branch], timeout=300)
                result["push"] = "ok" if pushed.returncode == 0 else pushed.stderr.strip()[:1000]
        return result


def _load_config(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"Expected object JSON in {path}")
    return data


def _resolve_repo_path(raw: str, config_path: Path) -> Path:
    path = Path(raw)
    candidates = [path] if path.is_absolute() else [
        config_path.parent / path,
        REPO_ROOT / path,
        REPO_ROOT.parent / path,
    ]
    for candidate in candidates:
        resolved = candidate.resolve()
        if (resolved / ".git").exists():
            return resolved
    return candidates[-1].resolve()


def fetch_repo(repo_key: str, repo_cfg: dict[str, Any], config_path: Path) -> dict[str, Any]:
    repo_path = _resolve_repo_path(str(repo_cfg.get("local_path", "")), config_path)
    with repo_fetch_lock(repo_path):
        before = _git_stdout(repo_path, ["rev-parse", str(repo_cfg.get("default_ref") or "HEAD")], timeout=30)
        result = _git(repo_path, ["fetch", "origin"], timeout=300)
        if result.returncode != 0:
            return {
                "repo_key": repo_key,
                "status": "fetch_failed",
                "reason": (result.stderr or result.stdout).strip(),
            }
        after = _git_stdout(repo_path, ["rev-parse", str(repo_cfg.get("default_ref") or "HEAD")], timeout=30)
    return {
        "repo_key": repo_key,
        "status": "fetched",
        "repo": repo_cfg.get("repo"),
        "default_ref": repo_cfg.get("default_ref"),
        "before": before,
        "after": after,
        "changed": before != after,
    }


def fetch_repositories(config_path: Path) -> list[dict[str, Any]]:
    config = _load_config(config_path)
    repos = config.get("repositories")
    if not isinstance(repos, dict):
        raise ValueError("config.repositories must be an object")
    results = []
    for repo_key, repo_cfg in repos.items():
        if isinstance(repo_cfg, dict):
            results.append(fetch_repo(str(repo_key), repo_cfg, config_path))
    return results


def run_command(args: list[str], *, timeout: int = 600) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )


def run_pipeline(
    config_path: Path,
    *,
    include_unchanged: bool,
    update_state: bool,
    limit_per_rule: int,
    scan_limit_per_rule: int,
) -> None:
    cmd = [
        sys.executable,
        str(SCRIPT_DIR / "run_bridge_pipeline.py"),
        "--config",
        str(config_path),
        "--limit-per-rule",
        str(limit_per_rule),
        "--scan-limit-per-rule",
        str(scan_limit_per_rule),
    ]
    if include_unchanged:
        cmd.append("--include-unchanged")
    if update_state:
        cmd.append("--update-state")
    result = run_command(cmd)
    if result.stdout.strip():
        _log(result.stdout.strip())
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout or "bridge pipeline failed").strip())


def run_synthesis_report(config_path: Path, *, enabled: bool, timeout: int) -> None:
    if not enabled:
        _log("standalone synthesis report: skipped; run_bridge_pipeline already synthesizes records")
        return
    config = _load_config(config_path)
    inbox = REPO_ROOT / str(config.get("inbox_path"))
    output = SCRIPT_DIR / "out" / "bridge_synthesis.jsonl"
    report = REPO_ROOT / str(config.get("synthesis_report_path") or "tools/automath_newmath_bridge/out/bridge_synthesis_report.md")
    cmd = [
        sys.executable,
        str(SCRIPT_DIR / "bridge_synthesis.py"),
        "--config",
        str(config_path),
        "--input",
        str(inbox),
        "--output",
        str(output),
        "--report",
        str(report),
    ]
    result = run_command(cmd, timeout=timeout)
    if result.stdout.strip():
        _log(result.stdout.strip())
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout or "bridge synthesis failed").strip())


def run_gates(config_path: Path, *, allow_publication_risk: bool) -> list[dict[str, Any]]:
    config = _load_config(config_path)
    inbox = REPO_ROOT / str(config.get("inbox_path"))
    output = SCRIPT_DIR / "out" / "bridge_gate_results.jsonl"
    records = read_jsonl(inbox)
    results = gate_records(records, allow_publication_risk=allow_publication_risk)
    write_jsonl(output, results)
    passed = sum(1 for item in results if item.get("gate_status") == "gate_passed")
    blocked = len(results) - passed
    _log(f"gates: passed={passed} blocked={blocked} output={output}")
    return results


def run_automath_writeback(config: dict[str, Any], *, apply: bool, push_branch: bool, dry_run: bool) -> dict[str, Any]:
    cfg = config.get("automath_writeback")
    if not isinstance(cfg, dict) or not cfg.get("enabled", False):
        return {"status": "disabled"}
    cmd = [
        sys.executable,
        str(SCRIPT_DIR / "bridge_to_automath_killo_golden.py"),
        "--gate-results",
        str(REPO_ROOT / str(cfg.get("gate_results_path") or "tools/automath_newmath_bridge/out/bridge_gate_results.jsonl")),
        "--runtime-dir",
        str(REPO_ROOT / str(cfg.get("runtime_candidate_dir") or "tools/automath_newmath_bridge/inbox/automath_writeback_candidates")),
        "--branch",
        str(cfg.get("branch") or "bridge/automath-newmath-consumption"),
        "--limit",
        str(int(cfg.get("max_candidates_per_pass") or 1)),
        "--review-backend",
        str(cfg.get("review_backend") or "codex-claude"),
    ]
    if apply:
        cmd.append("--apply")
    if dry_run:
        cmd.append("--dry-run")
    if push_branch:
        cmd.append("--push-branch")
    if cfg.get("distillation_timeout_seconds"):
        cmd.extend(["--distillation-timeout-seconds", str(int(cfg.get("distillation_timeout_seconds") or 0))])
    result = run_command(cmd, timeout=7500 if apply else 180)
    if result.returncode != 0:
        return {
            "status": "failed",
            "apply": apply,
            "push_branch": push_branch,
            "reason": (result.stderr or result.stdout).strip()[:2000],
        }
    try:
        payload = json.loads(result.stdout.strip()) if result.stdout.strip() else {}
    except json.JSONDecodeError:
        payload = {"raw": result.stdout.strip()[:2000]}
    return {
        "status": "applied" if apply else "dry_run",
        "apply": apply,
        "push_branch": push_branch,
        **payload,
    }


def _writeback_processes() -> list[dict[str, Any]]:
    script = str(SCRIPT_DIR / "bridge_to_automath_killo_golden.py")
    if os.name != "nt":
        return []
    ps = (
        "Get-CimInstance Win32_Process -Filter \"name = 'python.exe'\" | "
        "Where-Object { $_.CommandLine -like '*bridge_to_automath_killo_golden.py*' } | "
        "Select-Object ProcessId,ParentProcessId,CreationDate,CommandLine | ConvertTo-Json -Compress"
    )
    result = subprocess.run(
        ["powershell", "-NoProfile", "-Command", ps],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )
    if result.returncode != 0 or not result.stdout.strip():
        return []
    try:
        data = json.loads(result.stdout)
    except json.JSONDecodeError:
        return []
    rows = data if isinstance(data, list) else [data]
    return [row for row in rows if isinstance(row, dict) and script.lower() in str(row.get("CommandLine") or "").lower()]


def launch_automath_writeback_background(
    config: dict[str, Any],
    *,
    apply: bool,
    push_branch: bool,
    dry_run: bool,
) -> dict[str, Any]:
    cfg = config.get("automath_writeback")
    if not isinstance(cfg, dict) or not cfg.get("enabled", False):
        return {"status": "disabled"}
    running = _writeback_processes()
    if running:
        return {
            "status": "already_running",
            "running": [
                {
                    "pid": item.get("ProcessId"),
                    "created_at": item.get("CreationDate"),
                }
                for item in running[:5]
            ],
        }
    cmd = [
        sys.executable,
        str(SCRIPT_DIR / "bridge_to_automath_killo_golden.py"),
        "--gate-results",
        str(REPO_ROOT / str(cfg.get("gate_results_path") or "tools/automath_newmath_bridge/out/bridge_gate_results.jsonl")),
        "--runtime-dir",
        str(REPO_ROOT / str(cfg.get("runtime_candidate_dir") or "tools/automath_newmath_bridge/inbox/automath_writeback_candidates")),
        "--branch",
        str(cfg.get("branch") or "bridge/automath-newmath-consumption"),
        "--limit",
        str(int(cfg.get("max_candidates_per_pass") or 1)),
        "--review-backend",
        str(cfg.get("review_backend") or "codex-claude"),
    ]
    if apply:
        cmd.append("--apply")
    if dry_run:
        cmd.append("--dry-run")
    if push_branch:
        cmd.append("--push-branch")
    if cfg.get("distillation_timeout_seconds"):
        cmd.extend(["--distillation-timeout-seconds", str(int(cfg.get("distillation_timeout_seconds") or 0))])
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    handle = WRITEBACK_LOG.open("a", encoding="utf-8")
    handle.write(f"[{_now_iso()}] launch {' '.join(cmd)}\n")
    handle.flush()
    proc = subprocess.Popen(
        cmd,
        cwd=str(REPO_ROOT),
        stdout=handle,
        stderr=subprocess.STDOUT,
        text=True,
        creationflags=subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0,
    )
    handle.close()
    return {
        "status": "launched",
        "pid": proc.pid,
        "apply": apply,
        "push_branch": push_branch,
        "log": str(WRITEBACK_LOG),
    }


def render_newmath_ack_status(config_path: Path) -> dict[str, Any]:
    cmd = [
        sys.executable,
        str(SCRIPT_DIR / "render_newmath_ack_report.py"),
        "--config",
        str(config_path),
    ]
    result = run_command(cmd, timeout=120)
    if result.returncode != 0:
        return {"status": "failed", "reason": (result.stderr or result.stdout).strip()[:1000]}
    try:
        payload = json.loads(result.stdout.strip()) if result.stdout.strip() else {}
    except json.JSONDecodeError:
        payload = {"raw": result.stdout.strip()[:1000]}
    return {"status": "ok", **payload}


def run_pi_reflection(config: dict[str, Any]) -> dict[str, Any]:
    cfg = config.get("pi_reflection")
    if not isinstance(cfg, dict) or not cfg.get("enabled", True):
        return {"status": "disabled"}
    wb_cfg = config.get("automath_writeback") if isinstance(config.get("automath_writeback"), dict) else {}
    cmd = [
        sys.executable,
        str(SCRIPT_DIR / "bridge_pi_reflection.py"),
        "--gate-results",
        str(REPO_ROOT / str(cfg.get("gate_results_path") or wb_cfg.get("gate_results_path") or "tools/automath_newmath_bridge/out/bridge_gate_results.jsonl")),
        "--ack-status",
        str(REPO_ROOT / str(cfg.get("ack_status_path") or "docs/bridge/newmath-bridge-ack-status.md")),
        "--report",
        str(REPO_ROOT / str(cfg.get("report_path") or "docs/bridge/automath-newmath-pi-reflection.md")),
        "--actions",
        str(REPO_ROOT / str(cfg.get("actions_path") or "docs/bridge/automath-newmath-pi-actions.jsonl")),
        "--retry-policy",
        str(REPO_ROOT / str(cfg.get("retry_policy_path") or "docs/bridge/automath-newmath-retry-policy.jsonl")),
        "--review-backend",
        str(wb_cfg.get("review_backend") or "codex-claude"),
    ]
    result = run_command(cmd, timeout=120)
    if result.returncode != 0:
        return {"status": "failed", "reason": (result.stderr or result.stdout).strip()[:1000]}
    try:
        payload = json.loads(result.stdout.strip()) if result.stdout.strip() else {}
    except json.JSONDecodeError:
        payload = {"raw": result.stdout.strip()[:1000]}
    return {"status": "ok", **payload}


def _packet_name(result: dict[str, Any]) -> str:
    raw = str(result.get("id") or result.get("artifact_key") or result.get("source_path") or "packet")
    safe = "".join(ch if ch.isalnum() or ch in "._-" else "_" for ch in raw)
    return safe[:180] + ".json"


def write_local_packets(gate_results: list[dict[str, Any]], *, limit: int) -> list[Path]:
    PACKET_DIR.mkdir(parents=True, exist_ok=True)
    written: list[Path] = []
    for result in gate_results:
        if len(written) >= limit:
            break
        if result.get("gate_status") != "gate_passed":
            continue
        if not result.get("packet_write_allowed"):
            continue
        packet = {
            "schema_version": "automath-newmath-bridge-writeback-packet-v1",
            "created_at": _now_iso(),
            "status": "needs_operator_review",
            "durable_write_allowed": False,
            "reason": "Local bridge packet generated after deterministic gates. Durable writes require accepted/consumed manifest entry.",
            "gate_result": result,
            "non_actions": [
                "no push",
                "no publication",
                "no external send",
                "no paper write",
                "no Lean write",
                "no automatic acceptance",
            ],
        }
        path = PACKET_DIR / _packet_name(result)
        path.write_text(json.dumps(packet, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        written.append(path)
    return written


def supervisor_pass(args: argparse.Namespace) -> bool:
    config_path = Path(args.config).resolve()
    config = _load_config(config_path)
    ensure_branch(expected_branch_from_config(config_path, args.branch))
    if tracked_dirty_lines(REPO_ROOT) and not args.allow_dirty:
        raise RuntimeError("Tracked worktree changes present; pass --allow-dirty only for local runtime/debug work")

    if not args.no_fetch:
        fetch_results = fetch_repositories(config_path)
        for item in fetch_results:
            _log(f"fetch: {item}")
        if any(item.get("status") == "fetch_failed" for item in fetch_results):
            return False

    run_pipeline(
        config_path,
        include_unchanged=args.include_unchanged,
        update_state=args.update_state,
        limit_per_rule=args.limit_per_rule,
        scan_limit_per_rule=args.scan_limit_per_rule,
    )
    run_synthesis_report(
        config_path,
        enabled=bool(args.run_standalone_synthesis),
        timeout=args.standalone_synthesis_timeout,
    )
    gate_results = run_gates(config_path, allow_publication_risk=args.allow_publication_risk)
    ack_result = render_newmath_ack_status(config_path)
    _log(f"newmath_ack_status: {ack_result}")

    automath_apply = bool(args.apply_automath_writeback or config.get("automath_writeback", {}).get("apply_by_default", False))
    automath_push = bool(args.push_branch or config.get("automath_writeback", {}).get("push_branch_by_default", False))
    if not args.no_automath_writeback:
        if args.automath_writeback_background:
            wb_result = launch_automath_writeback_background(
                config,
                apply=automath_apply,
                push_branch=automath_push,
                dry_run=args.automath_writeback_dry_run,
            )
        else:
            wb_result = run_automath_writeback(
                config,
                apply=automath_apply,
                push_branch=automath_push,
                dry_run=args.automath_writeback_dry_run,
            )
        _log(f"automath_writeback: {wb_result}")
        if wb_result.get("status") == "failed":
            return False
    else:
        _log("automath_writeback: disabled by --no-automath-writeback")

    pi_result = run_pi_reflection(config)
    _log(f"pi_reflection: {pi_result}")

    if args.commit_durable:
        commit_result = commit_and_push_durable(
            REPO_ROOT,
            message=f"bridge(automath): record PI bridge feedback {_now_iso()}",
            push=args.push_branch,
        )
        _log(f"commit_durable: {commit_result}")

    if args.apply_writeback_packets:
        written = write_local_packets(gate_results, limit=args.packet_limit)
        _log(f"local writeback packets: wrote={len(written)} dir={PACKET_DIR}")
    else:
        _log("local writeback packets: disabled; pass --apply-writeback-packets to write ignored review packets")
    return True


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Automath-NewMath bridge supervisor")
    parser.add_argument("--branch", default="bridge/automath-newmath-consumption", help="Required current branch fallback; config.required_branch wins")
    parser.add_argument("--config", default=str(DEFAULT_CONFIG), help="bridge pipeline config JSON")
    parser.add_argument("--once", action="store_true", help="Run one pass")
    parser.add_argument("--poll-interval", type=int, default=300, help="Seconds between passes")
    parser.add_argument("--no-fetch", action="store_true", help="Do not fetch origin for configured repos")
    parser.add_argument("--include-unchanged", action="store_true", help="Emit already-seen artifacts")
    parser.add_argument("--update-state", action="store_true", help="Persist seen artifacts to ignored local state")
    parser.add_argument("--allow-dirty", action="store_true", help="Allow tracked dirty worktree before running")
    parser.add_argument("--allow-publication-risk", action="store_true", help="Suppress publication-risk gate warnings")
    parser.add_argument("--limit-per-rule", type=int, default=50)
    parser.add_argument("--scan-limit-per-rule", type=int, default=0, help="Limit candidate path scans per discovery rule")
    parser.add_argument(
        "--run-standalone-synthesis",
        action="store_true",
        help="Run the legacy standalone bridge_synthesis report after run_bridge_pipeline",
    )
    parser.add_argument("--standalone-synthesis-timeout", type=int, default=120)
    parser.add_argument(
        "--apply-automath-writeback",
        action="store_true",
        help="Invoke Automath-native distillation/Claude Killo-golden writeback for accepted bridge records",
    )
    parser.add_argument(
        "--automath-writeback-dry-run",
        action="store_true",
        help="Pass --dry-run to the Automath distillation supervisor",
    )
    parser.add_argument(
        "--automath-writeback-background",
        action="store_true",
        help="Launch Automath Killo/golden writeback in a background lane so the main scan/PI loop keeps running",
    )
    parser.add_argument(
        "--push-branch",
        action="store_true",
        help="Push only the Automath bridge branch after successful Automath-native writeback",
    )
    parser.add_argument(
        "--no-automath-writeback",
        action="store_true",
        help="Skip the Automath-native writeback adapter",
    )
    parser.add_argument(
        "--apply-writeback-packets",
        action="store_true",
        help="Write local ignored review packets for gate-passed candidates",
    )
    parser.add_argument("--packet-limit", type=int, default=25)
    parser.add_argument("--commit-durable", action="store_true", help="Commit durable bridge/PI outputs but not runtime artifacts")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    while True:
        try:
            ok = supervisor_pass(args)
        except Exception as exc:
            _log(f"supervisor pass failed: {exc}")
            ok = False
        if args.once or STOP_FILE.exists():
            return 0 if ok else 1
        time.sleep(max(30, args.poll_interval))


if __name__ == "__main__":
    raise SystemExit(main())
