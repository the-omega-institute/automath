#!/usr/bin/env python3
"""Keep a small set of Oracle proof-search targets running overnight.

This controller is intentionally narrower than outreach_supervisor.py:

* no external publishing
* no watchdog/supervisor refills
* at most three active Oracle-deep dispatches
* always resumes pinned ChatGPT conversations
* relaunches a target after nonterminal dispatch exits
* after a BREAKTHROUGH, advances to the next Problems I Like target

It is designed for the operator's "sleep loop": let Oracle be the primary
prover in the same ChatGPT conversation, while Codex only supplies replay/
verification hints and precise follow-up prompts.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import signal
import subprocess
import sys
import time
import urllib.request
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT_DIR = REPO_ROOT / "tools/community-outreach"
STATE_DIR = SCRIPT_DIR / "outreach_state"
TARGETS_DIR = SCRIPT_DIR / "targets"
LOG_DIR = SCRIPT_DIR / "state/overnight_controller"
BOARD_PATH = SCRIPT_DIR / "RESEARCH_BOARD.md"
ORACLE_STATUS_URL = os.environ.get("OUTREACH_ORACLE_SERVER_URL", "http://127.0.0.1:8766/status")

sys.path.insert(0, str(SCRIPT_DIR))
from outreach_board_parser import parse_board  # noqa: E402


DEFAULT_TARGETS = [
    ("T-43", "problemsilike_02"),
    ("T-44", "problemsilike_04"),
    ("T-32", "cand_litt_common_finite_etale_cover"),
]


@dataclass
class Running:
    todo_id: str
    slug: str
    process: subprocess.Popen
    log_path: Path
    started_at: float


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def log(message: str) -> None:
    print(f"[{now_iso()}] {message}", flush=True)


def safe_slug(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", value).strip("_")


def read_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}


def target_state(slug: str) -> dict:
    return read_json(STATE_DIR / f"{slug}.json")


def latest_verdict(slug: str) -> str:
    return str(target_state(slug).get("latest_oracle_deep_verdict") or "").upper()


def latest_conv(slug: str) -> str:
    return str(target_state(slug).get("latest_oracle_deep_conversation_id") or "")


def status_payload() -> dict:
    try:
        with urllib.request.urlopen(ORACLE_STATUS_URL, timeout=5) as resp:  # noqa: S310 - localhost endpoint.
            return json.loads(resp.read().decode("utf-8", errors="replace"))
    except Exception as exc:  # noqa: BLE001
        return {"error": str(exc)}


def task_matches_slug(task_id: str, slug: str) -> bool:
    token = safe_slug(slug)
    return token in str(task_id or "")


def server_has_target(slug: str, payload: dict | None = None) -> bool:
    payload = payload or status_payload()
    for task in payload.get("queued_tasks") or []:
        if task_matches_slug(str(task.get("task_id") or ""), slug):
            return True
        if safe_slug(slug) in str(task.get("tag") or ""):
            return True
    agents = payload.get("agents") or {}
    if isinstance(agents, dict):
        for rec in agents.values():
            if task_matches_slug(str((rec or {}).get("task_id") or ""), slug):
                return True
    return False


def pinned_ok(slug: str) -> bool:
    # Allow operator bypass when the user explicitly cleared the pinned
    # conv (e.g. to recover a context-exhausted Pro chat).  Tampermonkey
    # userscript already supports fresh-chat navigation on a no-conv task
    # (line ~1792 of outreach_oracle_macos.user.js).
    if os.environ.get("OUTREACH_ALLOW_FRESH_CHAT_DISPATCH", "").lower() in ("1", "true", "yes"):
        return True
    conv = latest_conv(slug)
    if not conv:
        return False
    sess = read_json(SCRIPT_DIR / "outreach_oracle/sessions" / f"{conv}.json")
    url = str(sess.get("chatgpt_url") or "")
    return "chatgpt.com" in url and "/c/" in url


def launch_dispatch(todo_id: str, slug: str, *, max_turns: int, timeout_s: int) -> Running:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    log_path = LOG_DIR / f"{todo_id}_{slug}_{stamp}.log"
    env = os.environ.copy()
    env["OUTREACH_ORACLE_DEEP_RESUME"] = "1"
    env["OUTREACH_ORACLE_CLOSURE_CHECK"] = "1"
    env.setdefault("OUTREACH_SKIP_POST_ORACLE_LOCAL_REPLAY", "0")
    env.setdefault("OUTREACH_REQUIRE_PRE_ORACLE_CODEX_WORKUP", "1")
    env.setdefault("OUTREACH_ALLOW_PRE_ORACLE_WORKUP_REUSE", "1")
    cmd = [
        "python3",
        str(SCRIPT_DIR / "dispatch_worktree.py"),
        "--supervise",
        "--supervise-id",
        todo_id,
        "--run",
        "--oracle-deep",
        "--no-arxiv-stage0",
        "--codex-driver",
        "--oracle-max-turns",
        str(max_turns),
        "--oracle-timeout",
        str(timeout_s),
    ]
    with open(log_path, "ab") as logf:
        logf.write(f"[{now_iso()}] launch {' '.join(cmd)}\n".encode("utf-8"))
        logf.flush()
        proc = subprocess.Popen(
            cmd,
            cwd=str(REPO_ROOT),
            env=env,
            stdout=logf,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
    return Running(todo_id=todo_id, slug=slug, process=proc, log_path=log_path, started_at=time.time())


def is_skipped_status(status: str) -> bool:
    return bool(re.search(r"\b(CLOSED|DISCARDED|OVERTAKEN|SOLVED|HANDOFF)\b", status or "", re.I))


def problem_id(todo) -> int:
    m = re.search(r"problemsilike\.com/(\d+)", getattr(todo, "source", "") or "", re.I)
    if not m:
        return 10**9
    return int(m.group(1))


def next_problemsilike(existing_todos: set[str], existing_slugs: set[str]) -> tuple[str, str] | None:
    todos = parse_board(BOARD_PATH)
    candidates = []
    for todo_id, todo in todos.items():
        source = getattr(todo, "source", "") or ""
        if "problemsilike.com/" not in source:
            continue
        if todo_id in existing_todos or todo.slug() in existing_slugs:
            continue
        if is_skipped_status(getattr(todo, "status", "") or ""):
            continue
        candidates.append((problem_id(todo), todo_id, todo.slug()))
    if not candidates:
        return None
    _, todo_id, slug = sorted(candidates)[0]
    return todo_id, slug


def parse_targets(raw: str) -> list[tuple[str, str]]:
    if not raw:
        return list(DEFAULT_TARGETS)
    todos = parse_board(BOARD_PATH)
    out = []
    for item in raw.split(","):
        todo_id = item.strip()
        if not todo_id:
            continue
        todo = todos.get(todo_id)
        if not todo:
            raise SystemExit(f"unknown todo id {todo_id}")
        out.append((todo_id, todo.slug()))
    return out


def terminate_children(running: dict[str, Running]) -> None:
    for run in running.values():
        if run.process.poll() is not None:
            continue
        try:
            os.killpg(run.process.pid, signal.SIGTERM)
        except OSError:
            pass


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--targets", default="", help="Comma-separated TODO ids. Default: T-43,T-44,T-32")
    parser.add_argument("--parallel", type=int, default=3)
    parser.add_argument("--max-turns", type=int, default=100)
    parser.add_argument("--oracle-timeout", type=int, default=7200)
    parser.add_argument("--poll-seconds", type=int, default=30)
    parser.add_argument("--relaunch-delay", type=int, default=30)
    parser.add_argument("--no-next-problemsilike", action="store_true")
    args = parser.parse_args(argv)

    targets = parse_targets(args.targets)
    running: dict[str, Running] = {}
    completed: set[str] = set()
    known_todos = {todo_id for todo_id, _ in targets}
    known_slugs = {slug for _, slug in targets}
    last_exit: dict[str, float] = {}

    log(
        "overnight_deep_loop starting "
        f"targets={','.join(t for t, _ in targets)} parallel={args.parallel} "
        f"max_turns={args.max_turns} next_problemsilike={not args.no_next_problemsilike}"
    )
    try:
        while True:
            payload = status_payload()
            if payload.get("error"):
                log(f"oracle status unavailable: {payload['error']}")

            for todo_id, run in list(running.items()):
                rc = run.process.poll()
                if rc is None:
                    continue
                verdict = latest_verdict(run.slug) or "UNKNOWN"
                log(
                    f"{todo_id} dispatch exited rc={rc} verdict={verdict} "
                    f"log={run.log_path}"
                )
                running.pop(todo_id, None)
                last_exit[todo_id] = time.time()
                if verdict == "BREAKTHROUGH":
                    completed.add(todo_id)
                    flag = LOG_DIR / f"{todo_id}_{run.slug}.breakthrough"
                    flag.write_text(f"{now_iso()}\n", encoding="utf-8")
                    if not args.no_next_problemsilike:
                        nxt = next_problemsilike(known_todos, known_slugs)
                        if nxt is not None:
                            targets.append(nxt)
                            known_todos.add(nxt[0])
                            known_slugs.add(nxt[1])
                            log(f"added next Problems I Like target {nxt[0]} ({nxt[1]})")

            active_payload = status_payload()
            for todo_id, slug in list(targets):
                if todo_id in completed or todo_id in running:
                    continue
                if len(running) >= max(1, args.parallel):
                    break
                if server_has_target(slug, active_payload):
                    continue
                if time.time() - last_exit.get(todo_id, 0) < args.relaunch_delay:
                    continue
                if not pinned_ok(slug):
                    log(f"{todo_id} ({slug}) has no pinned conversation; waiting instead of opening fresh chat")
                    continue
                run = launch_dispatch(
                    todo_id,
                    slug,
                    max_turns=args.max_turns,
                    timeout_s=args.oracle_timeout,
                )
                running[todo_id] = run
                log(f"launched {todo_id} ({slug}) pid={run.process.pid} log={run.log_path}")

            time.sleep(max(5, args.poll_seconds))
    except KeyboardInterrupt:
        log("received KeyboardInterrupt; terminating child dispatches")
        terminate_children(running)
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
