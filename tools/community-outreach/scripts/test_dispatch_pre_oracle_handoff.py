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

        long_run_finished = now + 600
        long_run_payload = json.loads(_local_repair_last(rel_stdout, finished_at=long_run_finished))
        long_run_payload["started_at"] = _iso_from_epoch(now - 2)
        (target_dir / "local_repair_last.json").write_text(json.dumps(long_run_payload, indent=2), encoding="utf-8")
        ok, reason = dispatch._pre_oracle_codex_workup_recent("demo", max_age_seconds=3600)
        if not ok:
            raise AssertionError(
                "handoff written during a long local-repair run should be reusable after finish: "
                f"{reason}"
            )
        stale_started_payload = json.loads(_local_repair_last(rel_stdout, finished_at=now + 600))
        stale_started_payload["started_at"] = _iso_from_epoch(now + 5)
        (target_dir / "local_repair_last.json").write_text(
            json.dumps(stale_started_payload, indent=2),
            encoding="utf-8",
        )
        ok, reason = dispatch._pre_oracle_codex_workup_recent("demo", max_age_seconds=3600)
        if ok or "older than last local repair start" not in reason:
            raise AssertionError(
                "handoff older than local-repair start should not be reusable: "
                f"ok={ok} reason={reason!r}"
            )
        (target_dir / "local_repair_last.json").write_text(
            _local_repair_last(rel_stdout, finished_at=now - 2),
            encoding="utf-8",
        )

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

        class FakeConsultant:
            server_url = "http://127.0.0.1:8766"

            def is_alive(self) -> bool:
                return True

            def deep_reasoning(self, *_args, **_kwargs):
                if os.environ.get(dispatch.DISPATCH_VERIFIED_PRE_ORACLE_HANDOFF_ENV) != "1":
                    raise AssertionError("dispatch did not mark handoff as verified before Oracle deep reasoning")
                return {
                    "final_verdict": "EXHAUSTED",
                    "turns": [],
                    "total_elapsed_seconds": 0,
                    "conversation_id": "conv_demo",
                }

        old_run_pre = dispatch._run_pre_oracle_codex_workup
        old_build_initial = dispatch._build_deep_initial_prompt
        old_resume_conv = dispatch._resume_conversation_id
        old_env = os.environ.get(dispatch.DISPATCH_VERIFIED_PRE_ORACLE_HANDOFF_ENV)
        dispatch._run_pre_oracle_codex_workup = lambda *_args, **_kwargs: (True, "", "test handoff")
        dispatch._build_deep_initial_prompt = lambda *_args, **_kwargs: "initial"
        dispatch._resume_conversation_id = lambda *_args, **_kwargs: ""
        os.environ.pop(dispatch.DISPATCH_VERIFIED_PRE_ORACLE_HANDOFF_ENV, None)
        try:
            import types

            fake_oracle_module = types.SimpleNamespace(
                DEFAULT_WRITE_PAPER_LATEX_PROMPT="write latex",
                OracleConsultant=lambda state_dir=None: FakeConsultant(),
                codex_driven_prompt_generator=None,
                generate_outreach_paper=lambda path: path,
                oracle_bridge_readiness=lambda server_url: (True, "", {}),
                run_paper_pipeline=lambda *_args, **_kwargs: {},
            )
            sys.modules["oracle_consultant"] = fake_oracle_module
            fake_profile = types.SimpleNamespace(slug="demo")
            result = dispatch._run_oracle_deep(
                dispatch.TodoSpec(
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
                    deliverables=[],
                    raw_block="",
                ),
                fake_profile,
                repo_root=repo_root,
                state_dir=repo_root / "tools/community-outreach/outreach_state",
                oracle_timeout=60,
                max_turns=1,
                write_latex=False,
            )
        finally:
            dispatch._run_pre_oracle_codex_workup = old_run_pre
            dispatch._build_deep_initial_prompt = old_build_initial
            dispatch._resume_conversation_id = old_resume_conv
            sys.modules.pop("oracle_consultant", None)
            if old_env is None:
                os.environ.pop(dispatch.DISPATCH_VERIFIED_PRE_ORACLE_HANDOFF_ENV, None)
            else:
                os.environ[dispatch.DISPATCH_VERIFIED_PRE_ORACLE_HANDOFF_ENV] = old_env
        if not result or result.get("conversation_id") != "conv_demo":
            raise AssertionError(f"fake oracle-deep did not return expected run: {result}")
        if os.environ.get(dispatch.DISPATCH_VERIFIED_PRE_ORACLE_HANDOFF_ENV) != old_env:
            raise AssertionError("dispatch leaked the verified-handoff env var after oracle deep reasoning")

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
