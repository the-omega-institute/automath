#!/usr/bin/env python3
"""Regression test for dispatch_worktree pre-Oracle Codex handoff reuse."""

from __future__ import annotations

import importlib.util
import json
import os
import sys
import tempfile
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "dispatch_worktree.py"


def _load_dispatch_worktree():
    spec = importlib.util.spec_from_file_location("dispatch_worktree_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _workup() -> str:
    return """
# Codex Workup

## Target claim now

The target is a finite certificate theorem whose local verifier should close a
bounded case split.

## Local evidence checked

I inspected `tools/community-outreach/targets/demo/results.json` and found that
the case-7 certificate is missing while the verifier script is present.

## Commands run

```bash
python3 tools/community-outreach/targets/demo/verify_demo.py --json
python3 -m json.tool tools/community-outreach/targets/demo/results.json
```

## Codex attempt before Oracle

I ran `python3 tools/community-outreach/targets/demo/verify_demo.py --json` and
the finite check failed at case 7 because `results.json` has no certificate for
that case. This is the first local blocker, so Oracle must prove the case-7
lemma or provide a checkable obstruction.

## Verifier/artifact status

The verifier exists, `results.json` parses, and the local failure is exactly the
missing case-7 certificate.

## Proof obligations still open

Prove the case-7 lemma or produce a checkable obstruction for the certificate
route.

## Next Oracle question

`tools/community-outreach/targets/demo/results.json` parses, but the local
command `python3 tools/community-outreach/targets/demo/verify_demo.py --json`
failed at case 7 because the case-7 certificate is missing. Prove the case-7
lemma or provide a checkable obstruction that closes this certificate route.

## Publication value / re-scope judgment

If the case-7 certificate closes, this becomes a bounded verifier note.
"""


def _iso_from_epoch(ts: float) -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%S+00:00", time.gmtime(ts))


def _local_repair_last(stdout_log: str, *, finished_at: float) -> str:
    return json.dumps(
        {
            "ok": True,
            "started_at": _iso_from_epoch(finished_at - 1),
            "finished_at": _iso_from_epoch(finished_at),
            "stdout_log": stdout_log,
            "postcheck": {
                "codex_command_trace": {
                    "ok": True,
                    "target_command_count": 2,
                    "mathematical_action_command_count": 1,
                },
                "substantive_local_work": {
                    "ok": True,
                    "report_declares_pre_oracle_processing": True,
                    "mathematical_action_command_count": 1,
                },
            },
        },
        indent=2,
    )


def main() -> int:
    dispatch = _load_dispatch_worktree()
    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        repo_root = Path(tmp)
        target_root = repo_root / "tools/community-outreach/targets"
        target_dir = target_root / "demo"
        target_dir.mkdir(parents=True)
        dispatch.REPO_ROOT_DEFAULT = repo_root
        dispatch.TARGETS_DIR_DEFAULT = target_root
        log_dir = repo_root / "tools/community-outreach/outreach_state/local_repair_logs"
        log_dir.mkdir(parents=True)
        stdout_log = log_dir / "codex.jsonl"
        stdout_log.write_text("{}\n", encoding="utf-8")
        rel_stdout = str(stdout_log.relative_to(repo_root))
        for name in ("codex_workup.md", "next_oracle_question.md", "local_repair_report.md"):
            (target_dir / name).write_text(_workup(), encoding="utf-8")
        now = time.time()
        for name in ("codex_workup.md", "next_oracle_question.md", "local_repair_report.md"):
            path = target_dir / name
            os.utime(path, (now - 1, now - 1))
        (target_dir / "local_repair_last.json").write_text(
            _local_repair_last(rel_stdout, finished_at=now - 2),
            encoding="utf-8",
        )

        ok, reason = dispatch._pre_oracle_codex_workup_recent("demo", max_age_seconds=3600)
        if not ok:
            raise AssertionError(f"fresh handoff without claim packet should pass: {reason}")

        dispatch.ALLOW_PRE_ORACLE_WORKUP_REUSE = False
        dispatch.LOCAL_REPAIR_SCRIPT_DEFAULT = repo_root / "missing_local_repair.py"
        ok, reason, _log = dispatch._run_pre_oracle_codex_workup("T-DEMO", "demo", timeout=60)
        if ok or "local repair script missing" not in reason:
            raise AssertionError(
                "direct dispatch path reused a recent handoff without explicit supervisor allowance: "
                f"ok={ok} reason={reason!r}"
            )
        dispatch.ALLOW_PRE_ORACLE_WORKUP_REUSE = True
        ok, reason, log = dispatch._run_pre_oracle_codex_workup("T-DEMO", "demo", timeout=60)
        if not ok or "reused" not in log:
            raise AssertionError(
                "supervisor-allowed dispatch path did not reuse the current fresh handoff: "
                f"ok={ok} reason={reason!r} log={log!r}"
            )
        dispatch.ALLOW_PRE_ORACLE_WORKUP_REUSE = False

        weak_payload = json.loads(_local_repair_last(rel_stdout, finished_at=now - 2))
        weak_payload["postcheck"]["substantive_local_work"].pop("report_declares_pre_oracle_processing")
        (target_dir / "local_repair_last.json").write_text(
            json.dumps(weak_payload, indent=2),
            encoding="utf-8",
        )
        ok, reason = dispatch._pre_oracle_codex_workup_recent("demo", max_age_seconds=3600)
        if ok or "pre-Oracle mathematical action" not in reason:
            raise AssertionError(
                "dispatch accepted local repair without explicit pre-Oracle action declaration: "
                f"ok={ok} reason={reason!r}"
            )
        (target_dir / "local_repair_last.json").write_text(
            _local_repair_last(rel_stdout, finished_at=now - 2),
            encoding="utf-8",
        )

        time.sleep(0.02)
        (target_dir / "oracle_claim_packet_new.md").write_text(
            "# Oracle Claim Packet\n\n## Oracle Response\n\n"
            "Here is a substantive claim: the finite verifier closes case 7 with sha256=abc123.\n",
            encoding="utf-8",
        )
        ok, reason = dispatch._pre_oracle_codex_workup_recent("demo", max_age_seconds=3600)
        if ok or "older than latest substantive Oracle claim" not in reason:
            raise AssertionError(
                "dispatch reused a handoff older than newest substantive Oracle claim: "
                f"ok={ok} reason={reason!r}"
            )

        time.sleep(0.02)
        refreshed = time.time() + 2
        for name in ("codex_workup.md", "next_oracle_question.md", "local_repair_report.md"):
            path = target_dir / name
            path.write_text(path.read_text(encoding="utf-8") + "\nRefreshed after claim.\n", encoding="utf-8")
            os.utime(path, (refreshed + 1, refreshed + 1))
        (target_dir / "local_repair_last.json").write_text(
            _local_repair_last(rel_stdout, finished_at=refreshed),
            encoding="utf-8",
        )
        ok, reason = dispatch._pre_oracle_codex_workup_recent("demo", max_age_seconds=3600)
        if not ok:
            raise AssertionError(f"handoff refreshed after claim should pass: {reason}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
