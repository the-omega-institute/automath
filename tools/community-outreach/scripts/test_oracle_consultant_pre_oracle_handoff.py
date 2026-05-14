#!/usr/bin/env python3
"""Regression test for oracle_consultant pre-Oracle Codex handoff parsing."""

from __future__ import annotations

import importlib.util
import json
import os
import sys
import tempfile
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "oracle_consultant.py"


def _load_oracle_consultant():
    spec = importlib.util.spec_from_file_location("oracle_consultant_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _workup(*, include_attempt: bool = True) -> str:
    attempt = ""
    if include_attempt:
        attempt = """
## Codex attempt before Oracle

I ran `python3 tools/community-outreach/targets/demo/verify_demo.py --json` and the finite check failed at case 7 because `results.json` has no certificate for that case. This is the first local blocker, so Oracle must prove the case-7 lemma or provide a checkable obstruction.
"""
    return f"""
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

{attempt}

## Verifier/artifact status

The verifier exists, `results.json` parses, and the local failure is exactly the
missing case-7 certificate.

## Proof obligations still open

Prove the case-7 lemma or produce a checkable obstruction for the certificate
route.

## Next Oracle question

`tools/community-outreach/targets/demo/results.json` parses, but the local command `python3 tools/community-outreach/targets/demo/verify_demo.py --json` failed at case 7 because the case-7 certificate is missing. Prove the case-7 lemma or provide a checkable obstruction that closes this certificate route.

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


def _todo(oracle: object) -> object:
    return oracle.TodoSpec(
        todo_id="T-DEMO",
        title="Demo certificate",
        status="active",
        source="local",
        type_="open_problem",
        untouched="",
        fit_score=10,
        topic_score=10,
        effort="small",
        risk="low",
        final_display="short note",
        success_gate="verifier passes",
        statement="demo",
        prior="",
        omega_fit_detail="",
        attack_plan=[],
        worktree_inputs=[],
        deliverables=["tools/community-outreach/targets/demo/research.md"],
        raw_block="",
    )


def main() -> int:
    oracle = _load_oracle_consultant()
    section = oracle._extract_markdown_section(_workup(), "Commands run", max_chars=20000)
    if "verify_demo.py --json" not in section:
        raise AssertionError(f"failed to extract Commands run section: {section!r}")

    ok, reason = oracle._target_workup_local_trace_status(_workup())
    if not ok:
        raise AssertionError(f"valid local Codex workup was rejected: {reason}")

    ok, reason = oracle._target_workup_local_trace_status(_workup(include_attempt=False))
    if ok or "codex attempt before oracle" not in reason.lower():
        raise AssertionError(f"metadata-only workup was not rejected correctly: ok={ok} reason={reason!r}")

    grounded = oracle._question_is_grounded_in_local_work(
        (
            "`tools/community-outreach/targets/demo/results.json` parses, but "
            "`verify_demo.py --json` failed at case 7. Prove the case-7 lemma."
        ),
        _workup(),
        "demo",
    )
    if not grounded:
        raise AssertionError("grounded Oracle question was not recognized")

    slug_only = oracle._question_is_grounded_in_local_work(
        "For demo, prove the exact theorem and explain the remaining obstruction.",
        _workup(),
        "demo",
    )
    if slug_only:
        raise AssertionError("slug-only Oracle question should not count as locally grounded")

    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        target_root = Path(tmp)
        target_dir = target_root / "demo"
        target_dir.mkdir()
        stdout_log = target_root / "codex.jsonl"
        stdout_log.write_text("{}\n", encoding="utf-8")
        rel_stdout = str(stdout_log.relative_to(oracle.REPO_ROOT))
        for name in ("codex_workup.md", "next_oracle_question.md", "local_repair_report.md"):
            (target_dir / name).write_text(_workup(), encoding="utf-8")
        oracle.TARGETS_DIR = target_root
        now = time.time()
        for name in ("codex_workup.md", "next_oracle_question.md", "local_repair_report.md"):
            os.utime(target_dir / name, (now - 1, now - 1))
        (target_dir / "local_repair_last.json").write_text(
            _local_repair_last(rel_stdout, finished_at=now - 2),
            encoding="utf-8",
        )
        ok, reason = oracle._pre_oracle_target_files_recent("demo", max_age_seconds=3600)
        if not ok:
            raise AssertionError(f"fresh handoff without claim packet should pass: {reason}")

        old_repo_root = oracle.REPO_ROOT
        oracle.ALLOW_PRE_ORACLE_WORKUP_REUSE = False
        oracle.REPO_ROOT = target_root / "fake_repo_without_local_repair"
        try:
            ok_result = oracle._run_pre_oracle_codex_workup_for_todo(
                _todo(oracle),
                per_turn_timeout=120,
            )
        finally:
            oracle.REPO_ROOT = old_repo_root
            oracle.ALLOW_PRE_ORACLE_WORKUP_REUSE = False
        if ok_result.get("ok") or ok_result.get("reused_recent"):
            raise AssertionError(
                "oracle consultant direct path reused a recent handoff without explicit supervisor allowance: "
                f"{ok_result}"
            )
        if "missing local repair script" not in str(ok_result.get("error") or ""):
            raise AssertionError(f"direct path should have tried local repair instead of reuse: {ok_result}")

        oracle.ALLOW_PRE_ORACLE_WORKUP_REUSE = True
        ok_result = oracle._run_pre_oracle_codex_workup_for_todo(
            _todo(oracle),
            per_turn_timeout=120,
        )
        if not ok_result.get("ok") or not ok_result.get("reused_recent"):
            raise AssertionError(
                "oracle consultant did not reuse a fresh handoff when supervisor allowance was explicit: "
                f"{ok_result}"
            )
        oracle.ALLOW_PRE_ORACLE_WORKUP_REUSE = False

        os.environ[oracle.DISPATCH_VERIFIED_PRE_ORACLE_HANDOFF_ENV] = "1"
        os.environ[oracle.DISPATCH_VERIFIED_PRE_ORACLE_TODO_ENV] = "T-DEMO"
        os.environ[oracle.DISPATCH_VERIFIED_PRE_ORACLE_SLUG_ENV] = "demo"
        os.environ[oracle.DISPATCH_VERIFIED_PRE_ORACLE_LOG_ENV] = "dispatch-log"
        old_popen = oracle.subprocess.Popen
        oracle.subprocess.Popen = lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("dispatch-verified handoff should not spawn local repair")
        )
        try:
            ok_result = oracle._run_pre_oracle_codex_workup_for_todo(
                _todo(oracle),
                per_turn_timeout=120,
            )
        finally:
            oracle.subprocess.Popen = old_popen
            os.environ.pop(oracle.DISPATCH_VERIFIED_PRE_ORACLE_HANDOFF_ENV, None)
            os.environ.pop(oracle.DISPATCH_VERIFIED_PRE_ORACLE_TODO_ENV, None)
            os.environ.pop(oracle.DISPATCH_VERIFIED_PRE_ORACLE_SLUG_ENV, None)
            os.environ.pop(oracle.DISPATCH_VERIFIED_PRE_ORACLE_LOG_ENV, None)
        if not ok_result.get("ok") or not ok_result.get("reused_dispatch_verified"):
            raise AssertionError(
                "oracle consultant did not validate/reuse a dispatch-verified handoff without spawning local repair: "
                f"{ok_result}"
            )
        if ok_result.get("log_path") != "dispatch-log":
            raise AssertionError(f"dispatch handoff log path was not preserved: {ok_result}")

        os.environ[oracle.DISPATCH_VERIFIED_PRE_ORACLE_HANDOFF_ENV] = "1"
        os.environ[oracle.DISPATCH_VERIFIED_PRE_ORACLE_TODO_ENV] = "T-OTHER"
        old_repo_root = oracle.REPO_ROOT
        oracle.REPO_ROOT = target_root / "fake_repo_without_local_repair"
        try:
            wrong_target_result = oracle._run_pre_oracle_codex_workup_for_todo(
                _todo(oracle),
                per_turn_timeout=120,
            )
        finally:
            oracle.REPO_ROOT = old_repo_root
            os.environ.pop(oracle.DISPATCH_VERIFIED_PRE_ORACLE_HANDOFF_ENV, None)
            os.environ.pop(oracle.DISPATCH_VERIFIED_PRE_ORACLE_TODO_ENV, None)
        if wrong_target_result.get("ok") or "missing local repair script" not in str(
            wrong_target_result.get("error") or ""
        ):
            raise AssertionError(
                "oracle consultant reused a dispatch-verified handoff for the wrong todo id: "
                f"{wrong_target_result}"
            )

        weak_payload = json.loads(_local_repair_last(rel_stdout, finished_at=now - 2))
        weak_payload["postcheck"]["substantive_local_work"].pop("report_declares_pre_oracle_processing")
        (target_dir / "local_repair_last.json").write_text(
            json.dumps(weak_payload, indent=2),
            encoding="utf-8",
        )
        os.environ[oracle.DISPATCH_VERIFIED_PRE_ORACLE_HANDOFF_ENV] = "1"
        os.environ[oracle.DISPATCH_VERIFIED_PRE_ORACLE_TODO_ENV] = "T-DEMO"
        os.environ[oracle.DISPATCH_VERIFIED_PRE_ORACLE_SLUG_ENV] = "demo"
        old_popen = oracle.subprocess.Popen
        oracle.subprocess.Popen = lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("bad dispatch-verified handoff should fail validation before local repair")
        )
        try:
            bad_dispatch_result = oracle._run_pre_oracle_codex_workup_for_todo(
                _todo(oracle),
                per_turn_timeout=120,
            )
        finally:
            oracle.subprocess.Popen = old_popen
            os.environ.pop(oracle.DISPATCH_VERIFIED_PRE_ORACLE_HANDOFF_ENV, None)
            os.environ.pop(oracle.DISPATCH_VERIFIED_PRE_ORACLE_TODO_ENV, None)
            os.environ.pop(oracle.DISPATCH_VERIFIED_PRE_ORACLE_SLUG_ENV, None)
        if bad_dispatch_result.get("ok") or "dispatch-verified pre-Oracle handoff failed validation" not in str(
            bad_dispatch_result.get("error") or ""
        ):
            raise AssertionError(
                "oracle consultant should fail a stale/bad dispatch-verified handoff instead of spawning local repair: "
                f"{bad_dispatch_result}"
            )
        ok, reason = oracle._pre_oracle_target_files_recent("demo", max_age_seconds=3600)
        if ok or "pre-Oracle mathematical action" not in reason:
            raise AssertionError(
                "oracle consultant accepted local repair without explicit pre-Oracle action declaration: "
                f"ok={ok} reason={reason!r}"
            )
        (target_dir / "local_repair_last.json").write_text(
            _local_repair_last(rel_stdout, finished_at=now - 2),
            encoding="utf-8",
        )

        time.sleep(0.02)
        claim = target_dir / "oracle_claim_packet_new.md"
        claim.write_text(
            "# Oracle Claim Packet\n\n## Oracle Response\n\n"
            "Here is a substantive claim: the finite verifier closes case 7 with sha256=abc123.\n",
            encoding="utf-8",
        )
        ok, reason = oracle._pre_oracle_target_files_recent("demo", max_age_seconds=3600)
        if ok or "older than latest substantive Oracle claim" not in reason:
            raise AssertionError(
                "handoff older than newest substantive Oracle claim was not rejected: "
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
        ok, reason = oracle._pre_oracle_target_files_recent("demo", max_age_seconds=3600)
        if not ok:
            raise AssertionError(f"handoff refreshed after claim should pass: {reason}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
