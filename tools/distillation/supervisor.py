#!/usr/bin/env python3
"""Outer-loop supervisor for Omega distillation.

This is intentionally thinner than the BEDC supervisor.  BEDC extends one
claim board; Omega distillation is a source-expansion lane for importing more
mathematical mechanisms from more mathematicians and keeping a backlog useful
for outreach and new-paper planning.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import Any

try:
    from tools.distillation import distill, lifecycle, source_queue
except ModuleNotFoundError:  # pragma: no cover - supports direct script imports
    import distill
    import lifecycle
    import source_queue


DEFAULT_BRANCH = os.environ.get("DISTILL_SUPERVISOR_BRANCH", "distill-clean")
SUPERVISOR_STOP_FILE = distill.SCRIPT_DIR / ".supervisor.stop"
SUPERVISOR_LOG_DIR = distill.LOG_DIR / "supervisor"


def _now_iso() -> str:
    return datetime.utcnow().replace(microsecond=0).isoformat() + "Z"


def _log(message: str) -> None:
    SUPERVISOR_LOG_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {message}"
    print(line, flush=True)
    with (SUPERVISOR_LOG_DIR / "supervisor.log").open("a", encoding="utf-8") as handle:
        handle.write(line + "\n")


def _git(args: list[str], *, timeout: int = 120) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git"] + args,
        cwd=str(distill.REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )


def _git_stdout(args: list[str], *, timeout: int = 120) -> str:
    result = _git(args, timeout=timeout)
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout or "git command failed").strip())
    return result.stdout.strip()


def current_branch() -> str:
    return _git_stdout(["rev-parse", "--abbrev-ref", "HEAD"], timeout=30)


def ensure_branch(expected: str) -> None:
    branch = current_branch()
    if branch != expected:
        raise RuntimeError(
            f"Refusing to run on branch {branch!r}; expected {expected!r}. "
            "The supervisor never checks out dev."
        )


def tracked_dirty_lines() -> list[str]:
    output = _git_stdout(["status", "--porcelain", "--untracked-files=no"], timeout=30)
    return [line for line in output.splitlines() if line.strip()]


def sync_dev_current_branch(branch: str) -> dict[str, Any]:
    """Merge origin/dev into the current branch without checking out dev."""
    ensure_branch(branch)
    if tracked_dirty_lines():
        return {
            "status": "skipped_dirty",
            "branch": branch,
            "reason": "tracked worktree changes present",
        }

    fetch = _git(["fetch", "origin", "dev"], timeout=120)
    if fetch.returncode != 0:
        return {"status": "fetch_failed", "branch": branch, "reason": fetch.stderr.strip()}

    behind_text = _git_stdout(["rev-list", "--count", "HEAD..origin/dev"], timeout=30)
    behind = int(behind_text or "0")
    if behind == 0:
        return {"status": "up_to_date", "branch": branch, "merged_commits": 0}

    _log(f"sync-dev: merging {behind} origin/dev commit(s) into {branch}")
    merge = _git(["merge", "--no-edit", "origin/dev"], timeout=600)
    if merge.returncode != 0:
        return {
            "status": "merge_failed",
            "branch": branch,
            "merged_commits": 0,
            "reason": (merge.stderr or merge.stdout).strip(),
        }
    push = _git(["push", "origin", branch], timeout=120)
    if push.returncode != 0:
        return {
            "status": "push_failed",
            "branch": branch,
            "merged_commits": behind,
            "reason": push.stderr.strip(),
        }
    return {"status": "merged", "branch": branch, "merged_commits": behind}


def push_current_branch(branch: str) -> dict[str, Any]:
    ensure_branch(branch)
    push = _git(["push", "origin", branch], timeout=120)
    if push.returncode == 0:
        return {"status": "pushed", "branch": branch}
    stderr = push.stderr.strip()
    if "Everything up-to-date" in stderr or "Everything up-to-date" in push.stdout:
        return {"status": "up_to_date", "branch": branch}
    return {"status": "push_failed", "branch": branch, "reason": stderr}


def commit_paths(paths: list[Path], message: str) -> dict[str, Any]:
    existing = [str(path) for path in paths if path.exists()]
    if not existing:
        return {"status": "nothing_to_commit"}
    add = _git(["add"] + existing, timeout=30)
    if add.returncode != 0:
        return {"status": "add_failed", "reason": add.stderr.strip()}
    diff = _git(["diff", "--cached", "--quiet"], timeout=30)
    if diff.returncode == 0:
        return {"status": "nothing_to_commit"}
    commit = _git(["commit", "-m", message], timeout=120)
    if commit.returncode != 0:
        return {"status": "commit_failed", "reason": commit.stderr.strip()}
    return {"status": "committed", "commit": commit.stdout.strip().splitlines()[-1:]}


def source_record(name: str, *, persist: bool = True) -> dict[str, Any]:
    state = distill.reconcile_state_contract(distill.load_state(name))
    action = distill.refresh_policy_state(state, persist=persist, update_memory=False)
    _scope, inventory, _action = distill._policy_model(state)
    done, done_reason = distill._pipeline_done_contract(state)
    families = distill._theorem_family_names(state)
    return {
        "name": state.name,
        "stage": state.current_stage,
        "families_done": len(state.completed_families),
        "families_total": len(families),
        "debts": len(distill._open_debts_from_inventory(inventory)),
        "splits": len(inventory.get("split_candidates", [])),
        "failure_kind": state.failure_kind,
        "next_action": state.next_action,
        "policy_action": action,
        "done": done,
        "done_reason": done_reason,
        "updated_at": state.updated_at,
    }


def source_records(names: list[str], *, persist: bool = True) -> list[dict[str, Any]]:
    return [source_record(name, persist=persist) for name in names]


def runnable_records(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        record
        for record in records
        if not record.get("done") and lifecycle.should_run_pipeline(record)
    ]


def backlog_records(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        record
        for record in records
        if int(record.get("splits", 0) or 0) > 0 or int(record.get("debts", 0) or 0) > 0
    ]


def format_dashboard(records: list[dict[str, Any]], *, branch: str, sync: dict[str, Any] | None = None) -> str:
    lines = [
        f"Omega distillation supervisor dashboard",
        f"branch: {branch}",
    ]
    if sync:
        detail = sync.get("status", "unknown")
        if sync.get("merged_commits"):
            detail += f" ({sync['merged_commits']} dev commit(s))"
        lines.append(f"sync-dev: {detail}")
    lines.append("")
    lines.append("sources:")
    for record in records:
        lines.append(
            "- {name}: stage={stage} families={families_done}/{families_total} "
            "debts={debts} splits={splits} failure={failure_kind}/{next_action} "
            "done={done}".format(**record)
        )

    backlog = backlog_records(records)
    lines.append("")
    lines.append(f"expansion backlog: {len(backlog)} source(s) with debts or split candidates")
    for record in backlog:
        lines.append(
            f"- {record['name']}: debts={record['debts']} splits={record['splits']} "
            f"basis for future mathematician/source expansion"
        )
    return "\n".join(lines)


def refresh_source_queue_if_needed(args: argparse.Namespace) -> dict[str, Any]:
    if not args.refresh_source_queue:
        return {"status": "disabled"}
    queue_before = source_queue.read_queue()
    open_candidate = source_queue.next_open_candidate(queue_before)
    use_oracle = bool(args.oracle_source_queue and not open_candidate)
    result = source_queue.refresh_source_queue(
        use_oracle=use_oracle,
        seed_limit=args.source_queue_seed_limit,
        oracle_limit=args.source_queue_oracle_limit,
        oracle_timeout=args.oracle_timeout,
        oracle_model=args.oracle_model,
        dry_run=args.dry_run,
    )
    print(source_queue.format_queue_summary(result["queue"]), flush=True)
    if result.get("changed") and not args.dry_run:
        commit_result = commit_paths(
            [source_queue.SOURCE_QUEUE_PATH],
            "chore: refresh distillation source queue",
        )
        _log(f"source-queue commit: {commit_result}")
        if commit_result.get("status") == "committed":
            push_result = push_current_branch(args.branch)
            _log(f"source-queue push: {push_result}")
    return result


def commit_source_queue(args: argparse.Namespace, message: str) -> None:
    if args.dry_run:
        return
    commit_result = commit_paths([source_queue.SOURCE_QUEUE_PATH], message)
    _log(f"source-queue commit: {commit_result}")
    if commit_result.get("status") == "committed":
        push_result = push_current_branch(args.branch)
        _log(f"source-queue push: {push_result}")


def promote_and_run_source_queue_candidate(args: argparse.Namespace) -> bool:
    if not args.auto_promote_source_queue:
        return True
    if args.dry_run:
        candidate = source_queue.next_open_candidate()
        _log(
            "source-queue dry-run: would promote %s"
            % (candidate.get("id") if candidate else "none")
        )
        return True
    candidate = source_queue.claim_candidate(args.source_queue_candidate)
    if not candidate:
        _log("source-queue: no open candidate to promote")
        return True
    source_name = str(candidate.get("distillation_source_name") or candidate.get("proposed_source"))
    queue_id = str(candidate.get("id", ""))
    _log(f"source-queue: promoted {queue_id} -> {source_name}")
    commit_source_queue(args, "chore: claim distillation source candidate")
    ok = run_source(source_name, args)
    state = distill.load_state(source_name)
    source_queue.finalize_candidate(
        queue_id,
        success=ok,
        failure_kind=state.failure_kind,
        detail=state.next_action,
    )
    commit_source_queue(
        args,
        "chore: complete distillation source candidate" if ok
        else "chore: block distillation source candidate",
    )
    return ok


def _increment_attempt_for_retry(name: str) -> None:
    state = distill.load_state(name)
    if state.next_action == "retry_resume" and state.failure_kind not in {"none", "incomplete"}:
        state.attempts += 1
        distill.save_state(state)


def run_source(name: str, args: argparse.Namespace) -> bool:
    _increment_attempt_for_retry(name)
    return distill.run_pipeline(
        name,
        dry_run=args.dry_run,
        supervised=args.supervised,
        review_backend=args.review_backend,
        oracle_research=args.oracle_research,
        oracle_deepening=args.oracle_deepening,
        oracle_timeout=args.oracle_timeout,
        oracle_model=args.oracle_model,
        oracle_pdf=args.oracle_pdf,
    )


def selected_names(args: argparse.Namespace) -> list[str]:
    if args.name:
        return args.name
    names = distill._existing_state_names()
    if not names:
        raise RuntimeError("No existing distillation states found")
    return names


def supervisor_pass(args: argparse.Namespace) -> bool:
    ensure_branch(args.branch)
    sync_result: dict[str, Any] | None = None
    if args.sync_dev:
        sync_result = sync_dev_current_branch(args.branch)
        _log(f"sync-dev: {sync_result}")
        if sync_result.get("status") in {"merge_failed", "fetch_failed"}:
            print(format_dashboard(source_records(selected_names(args), persist=False), branch=args.branch, sync=sync_result))
            return False

    names = selected_names(args)
    records = source_records(names)
    print(format_dashboard(records, branch=args.branch, sync=sync_result), flush=True)
    runnable = runnable_records(records)
    if not runnable:
        if args.auto_promote_source_queue and source_queue.next_open_candidate():
            promoted_ok = promote_and_run_source_queue_candidate(args)
            _log("no runnable sources; promoted existing source-queue candidate")
            return promoted_ok
        queue_result = refresh_source_queue_if_needed(args)
        _log(
            "source-queue: seeds=%s oracle=%s status=%s"
            % (
                queue_result.get("seed_count", 0),
                queue_result.get("oracle_count", 0),
                queue_result.get("oracle_status", {}).get("status", queue_result.get("status")),
            )
        )
        promoted_ok = promote_and_run_source_queue_candidate(args)
        _log("no runnable sources; supervisor pass complete")
        return promoted_ok

    ok = True
    for record in runnable:
        if SUPERVISOR_STOP_FILE.exists() or distill.STOP_FILE.exists():
            _log("stop file present; pausing before next source")
            break
        name = str(record["name"])
        _log(f"running source: {name}")
        ok = run_source(name, args) and ok
    push_result = push_current_branch(args.branch)
    _log(f"push: {push_result}")
    return ok and push_result.get("status") != "push_failed"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Omega distillation supervisor")
    parser.add_argument("--branch", default=DEFAULT_BRANCH, help="Required current branch")
    parser.add_argument("--name", action="append", help="Run a specific source; may be repeated")
    parser.add_argument("--once", action="store_true", help="Run one supervisor pass")
    parser.add_argument("--poll-interval", type=int, default=60, help="Seconds between passes")
    parser.add_argument("--dry-run", action="store_true", help="Avoid model calls and core writes")
    parser.add_argument("--sync-dev", dest="sync_dev", action="store_true", default=True)
    parser.add_argument("--no-sync-dev", dest="sync_dev", action="store_false")
    parser.add_argument("--refresh-source-queue", dest="refresh_source_queue", action="store_true", default=True)
    parser.add_argument("--no-refresh-source-queue", dest="refresh_source_queue", action="store_false")
    parser.add_argument("--oracle-source-queue", action="store_true", help="Use Oracle to enrich source queue seeds")
    parser.add_argument("--source-queue-seed-limit", type=int, default=source_queue.DEFAULT_SEED_LIMIT)
    parser.add_argument("--source-queue-oracle-limit", type=int, default=source_queue.DEFAULT_ORACLE_LIMIT)
    parser.add_argument(
        "--auto-promote-source-queue",
        action="store_true",
        help="Claim the highest-priority open source queue candidate and run distillation",
    )
    parser.add_argument("--source-queue-candidate", help="Specific source queue candidate id to promote")
    parser.add_argument("--supervised", action="store_true", help="Prompt before applying writebacks")
    parser.add_argument(
        "--review-backend",
        choices=distill.REVIEW_BACKENDS,
        default=distill.DEFAULT_REVIEW_BACKEND,
        help="Review gate backend",
    )
    parser.add_argument("--oracle-research", action="store_true", help="Use Oracle in Stage R")
    parser.add_argument("--oracle-deepening", action="store_true", help="Use Oracle in Stage W")
    parser.add_argument("--oracle-timeout", type=int, default=distill.DEFAULT_ORACLE_TIMEOUT)
    parser.add_argument("--oracle-model", default=distill.DEFAULT_ORACLE_MODEL)
    parser.add_argument("--oracle-pdf", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    while True:
        try:
            ok = supervisor_pass(args)
        except Exception as exc:
            _log(f"supervisor pass failed: {exc}")
            ok = False
        if args.once or SUPERVISOR_STOP_FILE.exists():
            return 0 if ok else 1
        time.sleep(max(5, args.poll_interval))


if __name__ == "__main__":
    sys.exit(main())
