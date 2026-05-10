#!/usr/bin/env python3
"""Isolated heavy-job loop for Automath-NewMath bridge artifacts.

The main bridge supervisor must keep scanning, queueing, and gating even when
cross-repo synthesis or Automath-native writeback dry-runs are slow. This
runner consumes the main loop's ignored artifacts on its own cadence and never
blocks the main scan loop.
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
STOP_FILE = SCRIPT_DIR / ".bridge_heavy_loop.stop"
LOCK_FILE = SCRIPT_DIR / "state" / "bridge_heavy_loop.lock"
LOG_FILE = SCRIPT_DIR / "logs" / "bridge_heavy_loop.log"


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def _log(message: str) -> None:
    LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {message}"
    print(line, flush=True)
    with LOG_FILE.open("a", encoding="utf-8") as handle:
        handle.write(line + "\n")


def _load_config(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8-sig"))
    if not isinstance(data, dict):
        raise ValueError(f"Expected object JSON in {path}")
    return data


def _path_from_config(config: dict[str, Any], key: str, fallback: str) -> Path:
    return REPO_ROOT / str(config.get(key) or fallback)


def _run(args: list[str], *, timeout: int) -> dict[str, Any]:
    started = time.time()
    try:
        result = subprocess.run(
            args,
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
        return {
            "status": "ok" if result.returncode == 0 else "failed",
            "returncode": result.returncode,
            "seconds": round(time.time() - started, 3),
            "stdout_tail": result.stdout[-2000:],
            "stderr_tail": result.stderr[-2000:],
        }
    except subprocess.TimeoutExpired as exc:
        return {
            "status": "timeout",
            "seconds": round(time.time() - started, 3),
            "stdout_tail": (exc.stdout or "")[-2000:] if isinstance(exc.stdout, str) else "",
            "stderr_tail": (exc.stderr or "")[-2000:] if isinstance(exc.stderr, str) else "",
        }


def _current_branch() -> str:
    result = subprocess.run(["git", "branch", "--show-current"], cwd=str(REPO_ROOT), capture_output=True, text=True, check=False)
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout).strip())
    return result.stdout.strip()


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


def run_once(args: argparse.Namespace) -> bool:
    config_path = Path(args.config).resolve()
    config = _load_config(config_path)
    inbox = _path_from_config(config, "inbox_path", "tools/automath_newmath_bridge/inbox/bridge_inbox.jsonl")
    synthesis_output = SCRIPT_DIR / "out" / "bridge_synthesis.jsonl"
    synthesis_report = _path_from_config(config, "synthesis_report_path", "tools/automath_newmath_bridge/out/bridge_synthesis_report.md")
    gate_results = SCRIPT_DIR / "out" / "bridge_gate_results.jsonl"
    writeback_cfg = config.get("automath_writeback")
    if isinstance(writeback_cfg, dict):
        gate_results = REPO_ROOT / str(writeback_cfg.get("gate_results_path") or gate_results.relative_to(REPO_ROOT))

    if not inbox.exists():
        _log(f"skip: inbox not found at {inbox}")
        return True

    fd = _acquire_lock(stale_seconds=args.stale_lock_seconds)
    if fd is None:
        _log(f"skip: another heavy loop owns {LOCK_FILE}")
        return True
    try:
        ok = True
        if not args.no_synthesis:
            result = _run(
                [
                    sys.executable,
                    str(SCRIPT_DIR / "bridge_synthesis.py"),
                    "--config",
                    str(config_path),
                    "--input",
                    str(inbox),
                    "--output",
                    str(synthesis_output),
                    "--report",
                    str(synthesis_report),
                ],
                timeout=args.synthesis_timeout,
            )
            _log(f"synthesis: {json.dumps(result, ensure_ascii=False, sort_keys=True)}")
            ok = ok and result.get("status") == "ok"

        if not args.no_automath_dry_run:
            branch = _current_branch()
            runtime_dir = "tools/automath_newmath_bridge/inbox/automath_writeback_candidates"
            if isinstance(writeback_cfg, dict):
                runtime_dir = str(writeback_cfg.get("runtime_candidate_dir") or runtime_dir)
            result = _run(
                [
                    sys.executable,
                    str(SCRIPT_DIR / "bridge_to_automath_killo_golden.py"),
                    "--gate-results",
                    str(gate_results),
                    "--runtime-dir",
                    str(REPO_ROOT / runtime_dir),
                    "--branch",
                    branch,
                    "--limit",
                    str(args.adapter_limit),
                    "--dry-run",
                ],
                timeout=args.adapter_timeout,
            )
            _log(f"automath_dry_run: {json.dumps(result, ensure_ascii=False, sort_keys=True)}")
            ok = ok and result.get("status") == "ok"
        return ok
    finally:
        _release_lock(fd)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run isolated heavy bridge jobs without blocking the main scanner")
    parser.add_argument("--config", default=str(DEFAULT_CONFIG))
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--poll-interval", type=int, default=1800)
    parser.add_argument("--synthesis-timeout", type=int, default=240)
    parser.add_argument("--adapter-timeout", type=int, default=120)
    parser.add_argument("--adapter-limit", type=int, default=1)
    parser.add_argument("--stale-lock-seconds", type=int, default=1800)
    parser.add_argument("--no-synthesis", action="store_true")
    parser.add_argument("--no-automath-dry-run", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    while True:
        try:
            ok = run_once(args)
        except Exception as exc:
            _log(f"heavy pass failed: {exc}")
            ok = False
        if args.once or STOP_FILE.exists():
            return 0 if ok else 1
        time.sleep(max(30, args.poll_interval))


if __name__ == "__main__":
    raise SystemExit(main())
