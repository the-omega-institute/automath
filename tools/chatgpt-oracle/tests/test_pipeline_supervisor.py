"""Smoke tests for tools/chatgpt-oracle/pipeline_supervisor and oracle_server multi-turn glue.

These tests exercise the cross-platform helpers and the multi-turn server
pieces that were added on dev-automation-integration. They do not require a
live ChatGPT browser tab — the oracle_server is exercised in-process.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import threading
import time
import unittest
import urllib.request
from unittest import mock
from http.server import HTTPServer
from pathlib import Path

SCRIPT_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_ROOT))

import oracle_server  # noqa: E402
import oracle_pipeline  # noqa: E402
import pipeline_supervisor  # noqa: E402


class SupervisorHelpersTests(unittest.TestCase):
    def test_python_resolves_to_executable(self):
        py = pipeline_supervisor._python()
        self.assertTrue(py)
        self.assertTrue(Path(py).exists() or py in {"python", "python3"})

    def test_detached_kwargs_match_platform(self):
        kwargs = pipeline_supervisor._detached_popen_kwargs()
        if pipeline_supervisor.IS_WINDOWS:
            self.assertIn("creationflags", kwargs)
            self.assertNotIn("start_new_session", kwargs)
        else:
            self.assertIn("start_new_session", kwargs)
            self.assertIs(kwargs["start_new_session"], True)

    def test_subprocess_env_defaults_to_five_oracle_agents(self):
        with mock.patch.dict(pipeline_supervisor.os.environ, {}, clear=True):
            env = pipeline_supervisor._subprocess_env()

        self.assertEqual(env["ORACLE_MAX_AGENTS"], "5")
        self.assertEqual(env["PYTHONUTF8"], "1")

    def test_install_signal_handlers_does_not_raise(self):
        pipeline_supervisor._install_signal_handlers()  # idempotent

    def test_discover_runnable_papers_returns_path_list(self):
        papers = pipeline_supervisor.discover_runnable_papers()
        self.assertIsInstance(papers, list)
        for p in papers:
            self.assertTrue(p.is_dir())
            self.assertTrue((p / "main.tex").exists())

    def test_discover_runnable_papers_uses_pipeline_board_gates(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper = Path(tmp) / "2026_allowed_by_pipeline"
            paper.mkdir()
            (paper / "main.tex").write_text("paper", encoding="utf-8")
            old_publication_dir = pipeline_supervisor.PUBLICATION_DIR
            pipeline_supervisor.PUBLICATION_DIR = Path(tmp) / "empty_pub"
            try:
                with mock.patch.object(
                    pipeline_supervisor,
                    "_pipeline_discovery_summary",
                    return_value={"papers": [str(paper)]},
                    create=True,
                ) as discovery:
                    papers = pipeline_supervisor.discover_runnable_papers()
            finally:
                pipeline_supervisor.PUBLICATION_DIR = old_publication_dir

        discovery.assert_called_once_with(None)
        self.assertEqual(papers, [paper])

    def test_pipeline_discovery_summary_reports_subprocess_failure(self):
        proc = subprocess.CompletedProcess(
            args=["python", "-c"],
            returncode=1,
            stdout="partial output\n",
            stderr="traceback line\n",
        )
        with mock.patch.object(pipeline_supervisor.subprocess, "run",
                               return_value=proc):
            with self.assertRaisesRegex(RuntimeError, "rc=1"):
                pipeline_supervisor._pipeline_discovery_summary(None)

    def test_format_discovery_summary_for_no_runnable_log(self):
        summary = {
            "diagnosis": "gate_exhausted",
            "candidate_count": 43,
            "runnable_count": 0,
            "skipped_status_count": 34,
            "skipped_done_count": 0,
            "skipped_unregistered_count": 9,
            "skipped_assignment_count": 0,
        }

        line = pipeline_supervisor.format_discovery_summary(summary)

        self.assertIn("diagnosis=gate_exhausted", line)
        self.assertIn("candidates=43", line)
        self.assertIn("status_skipped=34", line)
        self.assertIn("unregistered_skipped=9", line)

    def test_board_skip_keeps_hard_overlap_blocked(self):
        self.assertTrue(oracle_pipeline._board_skip(
            "A-BLOCKED (overlap deferred; wait for prior submitted sibling feedback)"
        ))
        self.assertTrue(oracle_pipeline._board_skip(
            "A-BLOCKED (overlap needs_human_resolution before Stage A)"
        ))

    def test_board_entry_skip_allows_active_route_with_parked_legacy_note(self):
        entry = {
            "journal": "retarget physics-math venue",
            "status": "A-READY (canonical merged rewrite route; overlap resolved)",
            "notes": (
                "Existing folder remains canonical; prior GRG route "
                "`submitted_2026_shell_geometry_detector_thermality_kms_grg` "
                "is parked and superseded into this merged rewrite"
            ),
            "reroute": "rerun Stage A with both rejection reasons",
        }

        self.assertFalse(oracle_pipeline._board_entry_skip(
            "2026_detector_shells_click_record_kms_jphyscomm",
            entry,
        ))

    def test_board_skip_allows_codex_ceiling_for_oracle_escalation(self):
        self.assertFalse(oracle_pipeline._board_skip(
            "A-BLOCKED (A2 fake extension: no new theorems; "
            "manual theorem-deepening required)"
        ))
        self.assertFalse(oracle_pipeline._board_skip(
            "A-BLOCKED (max Stage A rounds exhausted; final audit real block score=6)"
        ))
        self.assertFalse(oracle_pipeline._board_skip(
            "A-BLOCKED (Stage A real block: central homotopy theorem not self-contained)"
        ))
        self.assertFalse(oracle_pipeline._board_skip(
            "A-BLOCKED (FQ deepening audit real block score=6)"
        ))

    def test_watchdog_requests_inner_restart_for_recoverable_stage_a_blocks(self):
        summary = {
            "skipped_status": [
                "  2026_hard: A-BLOCKED (overlap deferred; wait for prior submitted sibling feedback)",
                "  2026_soft: A-BLOCKED (A2 fake extension: no new theorems; manual theorem-deepening required)",
            ]
        }
        with tempfile.TemporaryDirectory() as tmp:
            restart_file = Path(tmp) / ".inner.restart"
            with mock.patch.object(pipeline_supervisor, "INNER_RESTART_FILE", restart_file), \
                 mock.patch.object(pipeline_supervisor, "supervisor_log") as log:
                count = pipeline_supervisor.watchdog_wake_recoverable_stage_a_blocks(summary)

            self.assertEqual(count, 1)
            self.assertTrue(restart_file.exists())
            self.assertIn("2026_soft", restart_file.read_text(encoding="utf-8"))
            self.assertTrue(any(
                "recoverable Stage A block" in call.args[0]
                for call in log.call_args_list
            ))

    def test_watchdog_ignores_oracle_terminal_stage_a_blocks(self):
        summary = {
            "skipped_status": [
                "  2026_parked: A-BLOCKED (Oracle escalation parked: no independent theorem package remains)",
                "  2026_human: A-BLOCKED (Oracle escalation human_decision: choose merge route)",
            ]
        }

        self.assertEqual(
            pipeline_supervisor.recoverable_stage_a_blocked_papers(summary),
            [],
        )

    def test_inner_restart_defers_while_oracle_work_in_flight(self):
        self.assertTrue(pipeline_supervisor.oracle_work_in_flight({
            "queue_length": 0,
            "agents_busy": 1,
            "queued_tasks": [],
        }))
        self.assertTrue(pipeline_supervisor.oracle_work_in_flight({
            "queue_length": 1,
            "agents_busy": 0,
            "queued_tasks": [],
        }))
        self.assertTrue(pipeline_supervisor.oracle_work_in_flight({
            "queue_length": 0,
            "agents_busy": 0,
            "queued_tasks": [{"task_id": "stage_a"}],
        }))
        self.assertFalse(pipeline_supervisor.oracle_work_in_flight({
            "queue_length": 0,
            "agents_busy": 0,
            "queued_tasks": [],
        }))

    def test_stage_a_oracle_escalation_resets_codex_ceiling_state(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper = Path(tmp) / "2026_soft"
            paper.mkdir()
            (paper / "main.tex").write_text(
                "\\section{Intro}\nA paper.\n", encoding="utf-8")
            state = oracle_pipeline.PaperState(
                paper_dir=str(paper),
                paper_name="2026_soft",
                target_journal="Example Journal",
                current_stage="A",
                stage_a_rounds=oracle_pipeline.MAX_STAGE_A_ROUNDS,
                current_round=oracle_pipeline.MAX_STAGE_A_ROUNDS,
                error="Stage A blocked: A2 fake extension: no new theorems",
            )
            response = json.dumps({
                "verdict": "rerun_stage_a",
                "publishable_route": True,
                "core_theorem_direction": "Prove a rigidity theorem.",
                "required_theorem_package": [
                    "Add a labelled rigidity theorem with proof."
                ],
                "journal_route": "keep",
                "park_reason": "",
                "codex_instructions": [
                    "Add one substantive theorem, not prose."
                ],
            })

            with mock.patch.object(oracle_pipeline, "oracle_submit",
                                   return_value=True) as submit, \
                 mock.patch.object(oracle_pipeline, "oracle_poll",
                                   return_value=response), \
                 mock.patch.object(oracle_pipeline, "save_state"), \
                 mock.patch.object(oracle_pipeline, "git_commit",
                                   return_value="abc123"):
                ok = oracle_pipeline._maybe_stage_a_oracle_escalate(
                    state,
                    reason="A2 fake extension: no new theorems",
                    dry_run=False,
                    oracle_timeout=1,
                    tag="[2026_soft|A]",
                )

            self.assertTrue(ok)
            submit.assert_called_once()
            self.assertEqual(state.stage_a_rounds, 0)
            self.assertEqual(state.current_round, 0)
            self.assertEqual(state.stage_a_scores, [])
            self.assertEqual(state.stage_a_audit_metrics, {})
            self.assertEqual(state.error, "")
            self.assertTrue((paper / "oracle_stage_a_escalation.json").exists())
            directive = (paper / "research_directive.md").read_text(encoding="utf-8")
            self.assertIn("Oracle Stage A Escalation", directive)
            self.assertIn("Add one substantive theorem", directive)

    def test_oracle_directed_rework_failure_preserves_later_stage_context(self):
        state = oracle_pipeline.PaperState(
            paper_dir=".",
            paper_name="2026_retargeted",
            target_journal="Retarget Journal",
            current_stage="A",
            stage_b_rounds=13,
            stage_c_rounds=9,
            stage_b_verdicts=["accept"],
            stage_c_verdicts=["oracle accept"],
        )
        state.log_event(
            "A",
            "oracle_escalation_reuse",
            detail=json.dumps({"verdict": "rerun_stage_a"}),
        )

        self.assertTrue(oracle_pipeline._state_has_later_stage_history(state))
        self.assertTrue(oracle_pipeline._stage_a_rework_directive_active(state))

        reason = (
            "Oracle-directed Stage A rework did not add substantive theorem "
            "content: FAKE EXTENSION: no new theorems added, content delta "
            "only -383 chars (threshold: 500). Preserving prior B/C evidence; "
            "rerun requires fresh Oracle directive or manual theorem patch."
        )
        detail = oracle_pipeline._compact_board_detail(reason)

        self.assertIn("post-rejection Oracle-directed rework", detail)
        self.assertIn("prior B/C evidence preserved", detail)
        self.assertEqual(state.stage_b_rounds, 13)
        self.assertEqual(state.stage_c_rounds, 9)

    def test_no_oracle_mode_skips_stage_a_oracle_escalation(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper = Path(tmp) / "2026_local_only"
            paper.mkdir()
            (paper / "main.tex").write_text(
                "\\section{Intro}\nA paper.\n", encoding="utf-8")
            state = oracle_pipeline.PaperState(
                paper_dir=str(paper),
                paper_name="2026_local_only",
                target_journal="Example Journal",
                current_stage="A",
                stage_a_rounds=oracle_pipeline.MAX_STAGE_A_ROUNDS,
                current_round=oracle_pipeline.MAX_STAGE_A_ROUNDS,
                error="Stage A blocked: max Stage A rounds exhausted",
            )
            old_oracle_enabled = oracle_pipeline.ORACLE_ENABLED
            try:
                oracle_pipeline.ORACLE_ENABLED = False
                with mock.patch.object(oracle_pipeline, "oracle_submit") as submit, \
                     mock.patch.object(oracle_pipeline, "save_state"):
                    ok = oracle_pipeline._maybe_stage_a_oracle_escalate(
                        state,
                        reason="max Stage A rounds exhausted",
                        dry_run=False,
                        oracle_timeout=1,
                        tag="[2026_local_only|A]",
                    )
            finally:
                oracle_pipeline.ORACLE_ENABLED = old_oracle_enabled

            self.assertFalse(ok)
            submit.assert_not_called()
            self.assertEqual(
                state.error,
                "Stage A blocked: max Stage A rounds exhausted",
            )

    def test_no_oracle_mode_pauses_before_oracle_stages(self):
        state = oracle_pipeline.PaperState(
            paper_dir=".",
            paper_name="2026_stage_b",
            target_journal="Example Journal",
            current_stage="B",
        )
        old_oracle_enabled = oracle_pipeline.ORACLE_ENABLED
        try:
            oracle_pipeline.ORACLE_ENABLED = False
            with mock.patch.object(oracle_pipeline, "save_state") as save:
                paused = oracle_pipeline._pause_if_oracle_stage_disabled(
                    state, "B", "[2026_stage_b]"
                )
        finally:
            oracle_pipeline.ORACLE_ENABLED = old_oracle_enabled

        self.assertTrue(paused)
        self.assertIn("Stage B waiting for Oracle", state.error)
        save.assert_called_once_with(state)

    def test_post_rejection_retarget_does_not_rebuild_old_rounds_from_git(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper = Path(tmp) / "2026_retarget"
            paper.mkdir()
            (paper / "main.tex").write_text(
                "\\section{Intro}\nA paper.\n", encoding="utf-8")
            state = oracle_pipeline.PaperState(
                paper_dir=str(paper),
                paper_name="2026_retarget",
                target_journal="New Journal",
                current_stage="F",
                stage_a_rounds=0,
                stage_b_rounds=0,
                stage_c_rounds=0,
                stage_a_passed=False,
                completed_at="",
            )
            state.retarget_history.append({
                "from": "Journal of Spectral Theory",
                "to": "New Journal",
                "reason": "post_rejection_retarget_reopen",
            })
            git_log = "\n".join([
                "stage-A R10: old JST polish",
                "stage-B R14: old JST review",
                "stage-C R3: old JST final",
            ])
            proc = subprocess.CompletedProcess(
                args=["git", "log"],
                returncode=0,
                stdout=git_log,
                stderr="",
            )

            with mock.patch.object(oracle_pipeline.subprocess, "run",
                                   return_value=proc):
                oracle_pipeline.rebuild_rounds_from_git(state)

            self.assertEqual(state.stage_a_rounds, 0)
            self.assertEqual(state.stage_b_rounds, 0)
            self.assertEqual(state.stage_c_rounds, 0)

    def test_stage_a_oracle_terminal_verdict_is_hard_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper = Path(tmp) / "2026_parked"
            paper.mkdir()
            (paper / "main.tex").write_text(
                "\\section{Intro}\nA paper.\n", encoding="utf-8")
            (paper / "oracle_stage_a_escalation.json").write_text(
                json.dumps({
                    "verdict": "park",
                    "publishable_route": False,
                    "park_reason": "no independent theorem package remains",
                }),
                encoding="utf-8",
            )
            state = oracle_pipeline.PaperState(
                paper_dir=str(paper),
                paper_name="2026_parked",
                target_journal="Example Journal",
                current_stage="A",
                stage_a_rounds=oracle_pipeline.MAX_STAGE_A_ROUNDS,
                current_round=oracle_pipeline.MAX_STAGE_A_ROUNDS,
                error="Stage A blocked: max Stage A rounds exhausted",
            )

            with mock.patch.object(oracle_pipeline, "save_state"), \
                 mock.patch.object(oracle_pipeline, "update_program_board") as board:
                ok = oracle_pipeline._maybe_stage_a_oracle_escalate(
                    state,
                    reason="max Stage A rounds exhausted",
                    dry_run=False,
                    oracle_timeout=1,
                    tag="[2026_parked|A]",
                )

            self.assertFalse(ok)
            self.assertIn("Oracle escalation parked", state.error)
            board.assert_called_once()
            status, detail = board.call_args.args[1], board.call_args.args[2]
            self.assertEqual(status, "A-BLOCKED")
            self.assertIn("Oracle escalation parked", detail)
            full_status = f"{status} ({detail})"
            self.assertTrue(oracle_pipeline._board_skip(full_status))
            self.assertFalse(
                oracle_pipeline.is_recoverable_stage_a_block_status(full_status)
            )

    def test_stage_a_oracle_human_decision_verdict_is_hard_block(self):
        status = (
            "A-BLOCKED (Oracle escalation human_decision: choose whether "
            "to merge with the prior submitted sibling)"
        )

        self.assertTrue(oracle_pipeline._board_skip(status))
        self.assertFalse(
            oracle_pipeline.is_recoverable_stage_a_block_status(status)
        )

    def test_stage_a_terminal_artifact_blocks_even_if_board_was_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper = Path(tmp) / "2026_old_overwrite"
            paper.mkdir()
            (paper / "main.tex").write_text(
                "\\section{Intro}\nA paper.\n", encoding="utf-8")
            (paper / "oracle_stage_a_escalation.json").write_text(
                json.dumps({
                    "verdict": "park",
                    "park_reason": "real overlap block should stand",
                }),
                encoding="utf-8",
            )
            state = oracle_pipeline.PaperState(
                paper_dir=str(paper),
                paper_name="2026_old_overwrite",
                target_journal="Example Journal",
                current_stage="A",
                error="",
            )

            with mock.patch.object(oracle_pipeline, "save_state"), \
                 mock.patch.object(oracle_pipeline, "update_program_board") as board:
                ok = oracle_pipeline.run_stage_a(
                    state,
                    dry_run=False,
                    model=None,
                    oracle_timeout=1,
                )

            self.assertFalse(ok)
            self.assertIn("Oracle escalation parked", state.error)
            board.assert_called_once()
            self.assertIn("Oracle escalation parked", board.call_args.args[2])

    def test_refill_disabled_message_names_local_context_mode(self):
        message = pipeline_supervisor.refill_disabled_message()

        self.assertIn("--refill-project-url not set", message)
        self.assertIn("local-context", message)

    def test_default_auto_commit_paths_include_health_tool(self):
        paths = pipeline_supervisor.default_auto_commit_paths()

        self.assertIn("tools/chatgpt-oracle/pipeline_health.py", paths)
        self.assertIn("tools/chatgpt-oracle/tests/test_pipeline_health.py", paths)

    def test_supervisor_singleton_blocks_other_live_pid(self):
        emitted = []
        with tempfile.TemporaryDirectory() as tmp:
            pid_file = Path(tmp) / ".pipeline_supervisor.pid"
            pid_file.write_text(
                json.dumps({
                    "pid": 2464,
                    "started_ts": 1778742000.0,
                    "script": "pipeline_supervisor.py",
                }),
                encoding="utf-8",
            )

            with mock.patch.object(pipeline_supervisor, "PID_FILE", pid_file), \
                 mock.patch.object(pipeline_supervisor.os, "getpid", return_value=9999), \
                 mock.patch.object(pipeline_supervisor, "process_alive", return_value=True), \
                 mock.patch.object(pipeline_supervisor, "supervisor_log",
                                   side_effect=emitted.append):
                allowed = pipeline_supervisor.claim_supervisor_singleton(1234.0)

        self.assertFalse(allowed)
        self.assertTrue(any("already running" in line for line in emitted))

    def test_supervisor_singleton_overwrites_dead_pid(self):
        with tempfile.TemporaryDirectory() as tmp:
            pid_file = Path(tmp) / ".pipeline_supervisor.pid"
            pid_file.write_text("2464\n", encoding="utf-8")

            with mock.patch.object(pipeline_supervisor, "PID_FILE", pid_file), \
                 mock.patch.object(pipeline_supervisor.os, "getpid", return_value=9999), \
                 mock.patch.object(pipeline_supervisor, "process_alive", return_value=False):
                allowed = pipeline_supervisor.claim_supervisor_singleton(1234.0)

            record = json.loads(pid_file.read_text(encoding="utf-8"))

        self.assertTrue(allowed)
        self.assertEqual(record["pid"], 9999)
        self.assertEqual(record["started_ts"], 1234.0)

    def test_supervisor_singleton_ignores_live_pid_for_other_script(self):
        with tempfile.TemporaryDirectory() as tmp:
            pid_file = Path(tmp) / ".pipeline_supervisor.pid"
            pid_file.write_text(
                json.dumps({
                    "pid": 2464,
                    "started_ts": 1778742000.0,
                    "script": "not_pipeline_supervisor.py",
                }),
                encoding="utf-8",
            )

            with mock.patch.object(pipeline_supervisor, "PID_FILE", pid_file), \
                 mock.patch.object(pipeline_supervisor.os, "getpid", return_value=9999), \
                 mock.patch.object(pipeline_supervisor, "process_alive", return_value=True):
                allowed = pipeline_supervisor.claim_supervisor_singleton(1234.0)

            record = json.loads(pid_file.read_text(encoding="utf-8"))

        self.assertTrue(allowed)
        self.assertEqual(record["pid"], 9999)

    def test_duplicate_supervisor_does_not_clear_stop_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            stop_file = Path(tmp) / ".pipeline_supervisor.stop"
            pid_file = Path(tmp) / ".pipeline_supervisor.pid"
            stop_file.write_text("operator stop\n", encoding="utf-8")
            pid_file.write_text(
                json.dumps({
                    "pid": 2464,
                    "started_ts": 1778742000.0,
                    "script": "pipeline_supervisor.py",
                }),
                encoding="utf-8",
            )

            with mock.patch.object(sys, "argv", ["pipeline_supervisor.py", "--once"]), \
                 mock.patch.object(pipeline_supervisor, "STOP_FILE", stop_file), \
                 mock.patch.object(pipeline_supervisor, "PID_FILE", pid_file), \
                 mock.patch.object(pipeline_supervisor.os, "getpid", return_value=9999), \
                 mock.patch.object(pipeline_supervisor, "process_alive", return_value=True), \
                 mock.patch.object(pipeline_supervisor, "supervisor_log"):
                rc = pipeline_supervisor.main()

            self.assertEqual(rc, 1)
            self.assertTrue(stop_file.exists())

    def test_maybe_refill_uses_local_context_when_project_url_missing(self):
        args = type("Args", (), {
            "refill_project_url": "",
            "refill_cooldown_hours": 1,
            "refill_limit": 5,
            "refill_timeout": 1800,
        })()
        emitted = []

        with mock.patch.object(pipeline_supervisor, "supervisor_log",
                               side_effect=emitted.append), \
             mock.patch.object(pipeline_supervisor, "_now",
                               return_value=10_000.0), \
             mock.patch.object(pipeline_supervisor, "refill_last_run_ts",
                               return_value=0.0), \
             mock.patch.object(pipeline_supervisor, "trigger_refill") as trigger:
            pipeline_supervisor.maybe_refill_drained_backlog(args)

        trigger.assert_called_once_with("", limit=5, timeout=1800)
        self.assertEqual(emitted, [pipeline_supervisor.refill_disabled_message()])

    def test_maybe_refill_triggers_when_cooldown_satisfied(self):
        args = type("Args", (), {
            "refill_project_url": "https://chatgpt.com/g/project-test",
            "refill_cooldown_hours": 1,
            "refill_limit": 3,
            "refill_timeout": 120,
        })()

        with mock.patch.object(pipeline_supervisor, "_now",
                               return_value=10_000.0), \
             mock.patch.object(pipeline_supervisor, "refill_last_run_ts",
                               return_value=0.0), \
             mock.patch.object(pipeline_supervisor, "trigger_refill") as trigger:
            pipeline_supervisor.maybe_refill_drained_backlog(args)

        trigger.assert_called_once_with(
            "https://chatgpt.com/g/project-test",
            limit=3,
            timeout=120,
        )

    def test_maybe_refill_logs_cooldown_when_not_satisfied(self):
        args = type("Args", (), {
            "refill_project_url": "https://chatgpt.com/g/project-test",
            "refill_cooldown_hours": 2,
            "refill_limit": 3,
            "refill_timeout": 120,
        })()
        emitted = []

        with mock.patch.object(pipeline_supervisor, "_now",
                               return_value=10_000.0), \
             mock.patch.object(pipeline_supervisor, "refill_last_run_ts",
                               return_value=9_000.0), \
             mock.patch.object(pipeline_supervisor, "supervisor_log",
                               side_effect=emitted.append), \
             mock.patch.object(pipeline_supervisor, "trigger_refill") as trigger:
            pipeline_supervisor.maybe_refill_drained_backlog(args)

        trigger.assert_not_called()
        self.assertEqual(emitted, ["refill cooldown not met (1.7h remaining)"])

    def test_surface_log_alerts_starts_at_existing_file_end(self):
        with tempfile.TemporaryDirectory() as tmp:
            log_path = Path(tmp) / "inner.log"
            log_path.write_text(
                "2026-old [ERROR] stale failure\n",
                encoding="utf-8",
            )
            old_logs = pipeline_supervisor.SURFACED_LOGS
            old_offsets = dict(pipeline_supervisor._log_offsets)
            emitted = []
            try:
                pipeline_supervisor.SURFACED_LOGS = [("test", log_path)]
                pipeline_supervisor._log_offsets.clear()
                with mock.patch.object(
                    pipeline_supervisor,
                    "supervisor_log",
                    side_effect=emitted.append,
                ):
                    self.assertEqual(pipeline_supervisor.surface_log_alerts(), 0)
                    with log_path.open("a", encoding="utf-8") as fh:
                        fh.write("2026-new [ERROR] fresh failure\n")
                    self.assertEqual(pipeline_supervisor.surface_log_alerts(), 1)
            finally:
                pipeline_supervisor.SURFACED_LOGS = old_logs
                pipeline_supervisor._log_offsets.clear()
                pipeline_supervisor._log_offsets.update(old_offsets)

        self.assertEqual(emitted, ["test: 2026-new [ERROR] fresh failure"])

    def test_pipeline_continuous_all_waits_when_board_has_no_runnable_papers(self):
        fake_summary = {
            "diagnosis": "gate_exhausted",
            "candidate_count": 2,
            "runnable_count": 0,
            "papers": [],
            "skipped_status_count": 1,
            "skipped_done_count": 0,
            "skipped_unregistered_count": 1,
            "skipped_assignment_count": 0,
        }
        argv = [
            "oracle_pipeline.py",
            "--all",
            "--continuous",
            "--dry-run",
        ]
        with mock.patch.object(sys, "argv", argv), \
             mock.patch.object(oracle_pipeline, "discover_papers",
                               return_value=[]), \
             mock.patch.object(oracle_pipeline, "discover_paper_summary",
                               return_value=fake_summary), \
             mock.patch.object(oracle_pipeline.time, "sleep",
                               side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                oracle_pipeline.main(continuous_sleep_seconds=0)

    def test_command_failure_summary_includes_stderr_without_newline_noise(self):
        proc = subprocess.CompletedProcess(
            args=["git", "pull"],
            returncode=128,
            stdout="",
            stderr="error: cannot pull with rebase: You have unstaged changes.\n"
                   "error: please commit or stash them.\n",
        )

        summary = oracle_pipeline.command_failure_summary(proc)

        self.assertIn("rc=128", summary)
        self.assertIn("cannot pull with rebase", summary)
        self.assertNotIn("\n", summary)

    def test_oracle_poll_treats_response_observed_as_active_phase(self):
        calls = {"result": 0, "status": 0, "sleep": 0}

        def fake_http_get(url: str, timeout: int = 10) -> dict:
            calls["result"] += 1
            raise RuntimeError("not ready")

        def fake_task_status(task_id: str) -> dict:
            calls["status"] += 1
            return {
                "task_id": task_id,
                "phase": "response_observed",
                "agent_id": "oracle_1",
                "elapsed": 10,
            }

        def fake_sleep(seconds: float) -> None:
            calls["sleep"] += 1
            if calls["sleep"] >= 3:
                raise KeyboardInterrupt()

        with mock.patch.object(oracle_pipeline, "http_get", side_effect=fake_http_get), \
             mock.patch.object(oracle_pipeline, "oracle_task_status", side_effect=fake_task_status), \
             mock.patch.object(oracle_pipeline.time, "sleep", side_effect=fake_sleep):
            with self.assertRaises(KeyboardInterrupt):
                oracle_pipeline.oracle_poll("task_phase", timeout=7200, poll_interval=1)

        self.assertGreaterEqual(calls["status"], 3)

    def test_oracle_poll_active_phase_timeout_uses_local_monotonic_elapsed(self):
        fake_now = {"value": 1_000_000.0}

        def fake_http_get(url: str, timeout: int = 10) -> dict:
            raise RuntimeError("not ready")

        def fake_task_status(task_id: str) -> dict:
            return {
                "task_id": task_id,
                "phase": "waiting_response",
                "agent_id": "oracle_1",
                "elapsed": 0,
            }

        def fake_time() -> float:
            return fake_now["value"]

        def fake_sleep(seconds: float) -> None:
            fake_now["value"] += 2.0

        with mock.patch.object(oracle_pipeline, "http_get", side_effect=fake_http_get), \
             mock.patch.object(oracle_pipeline, "oracle_task_status", side_effect=fake_task_status), \
             mock.patch.object(oracle_pipeline.time, "time", side_effect=fake_time), \
             mock.patch.object(oracle_pipeline.time, "sleep", side_effect=fake_sleep):
            self.assertEqual(
                oracle_pipeline.oracle_poll("task_timeout", timeout=5, poll_interval=1),
                "",
            )

    def test_oracle_poll_short_response_observed_stall_returns_timeout(self):
        fake_now = {"value": 1_000_000.0}

        def fake_http_get(url: str, timeout: int = 10) -> dict:
            raise RuntimeError("not ready")

        def fake_task_status(task_id: str) -> dict:
            return {
                "task_id": task_id,
                "phase": "response_observed",
                "agent_id": "oracle_1",
                "elapsed": int(fake_now["value"] - 1_000_000.0),
                "detail": "elapsed=1000s; extracted=56; page=1139; stable=0; gen=false",
            }

        def fake_time() -> float:
            return fake_now["value"]

        def fake_sleep(seconds: float) -> None:
            fake_now["value"] += 60.0

        with mock.patch.object(oracle_pipeline, "http_get", side_effect=fake_http_get), \
             mock.patch.object(oracle_pipeline, "oracle_task_status", side_effect=fake_task_status), \
             mock.patch.object(oracle_pipeline.time, "time", side_effect=fake_time), \
             mock.patch.object(oracle_pipeline.time, "sleep", side_effect=fake_sleep):
            self.assertEqual(
                oracle_pipeline.oracle_poll("task_short_stall", timeout=7200, poll_interval=1),
                "",
            )


class OraclePipelineOverlapGuardTests(unittest.TestCase):
    def setUp(self):
        import tempfile
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._real_board = oracle_pipeline.PROGRAM_BOARD
        self._real_machine_board = oracle_pipeline.PROGRAM_BOARD_MACHINE
        self._real_pub = oracle_pipeline.PAPERS_PUB_DIR_CONST
        self._real_papers_pub = oracle_pipeline.PAPERS_PUB_DIR
        self._real_theory_dir = oracle_pipeline.THEORY_DIR
        self._real_state_dir = oracle_pipeline.STATE_DIR
        oracle_pipeline.PROGRAM_BOARD = self.root / "PROGRAM_BOARD.md"
        oracle_pipeline.PROGRAM_BOARD_MACHINE = self.root / "PROGRAM_BOARD_MACHINE.md"
        oracle_pipeline.PAPERS_PUB_DIR_CONST = self.root
        oracle_pipeline.PAPERS_PUB_DIR = self.root
        oracle_pipeline.THEORY_DIR = self.root / "theory"
        oracle_pipeline.STATE_DIR = self.root / "pipeline_state"
        oracle_pipeline._invalidate_board_cache()

    def tearDown(self):
        oracle_pipeline.PROGRAM_BOARD = self._real_board
        oracle_pipeline.PROGRAM_BOARD_MACHINE = self._real_machine_board
        oracle_pipeline.PAPERS_PUB_DIR_CONST = self._real_pub
        oracle_pipeline.PAPERS_PUB_DIR = self._real_papers_pub
        oracle_pipeline.THEORY_DIR = self._real_theory_dir
        oracle_pipeline.STATE_DIR = self._real_state_dir
        oracle_pipeline._invalidate_board_cache()
        self.tmp.cleanup()

    def _write_paper(self, name: str, body: str) -> Path:
        path = self.root / name
        path.mkdir()
        (path / "main.tex").write_text(body, encoding="utf-8")
        return path

    def _write_board(self, sibling_status: str, sibling_note: str = "") -> None:
        oracle_pipeline.PROGRAM_BOARD.write_text(
            "\n".join([
                "| 目录 | 目标期刊 | 状态 | 改投记录 |",
                "|------|---------|------|---------|",
                "| `2026_current_overlap` | DCDS-A | C-DONE | — |",
                (
                    "| `submitted_2026_old_overlap` | Fibonacci Q. | "
                    f"{sibling_status} | {sibling_note} |"
                ),
            ]),
            encoding="utf-8",
        )
        oracle_pipeline.PROGRAM_BOARD_MACHINE.write_text(
            oracle_pipeline.PROGRAM_BOARD.read_text(encoding="utf-8"),
            encoding="utf-8",
        )
        oracle_pipeline._invalidate_board_cache()

    def test_board_skip_understands_utf8_status(self):
        self.assertTrue(oracle_pipeline._board_skip("已投 05-11 审稿中"))
        self.assertTrue(oracle_pipeline._board_skip("拒稿 05-01"))
        self.assertTrue(oracle_pipeline._board_skip("骨架"))
        self.assertTrue(oracle_pipeline._board_skip("under review"))
        self.assertTrue(oracle_pipeline._board_skip("C-DONE"))
        self.assertTrue(oracle_pipeline._board_skip("C-DONE round 4: Oracle accept + Codex submit"))
        self.assertTrue(oracle_pipeline._board_skip("✅ 可投稿 — C-8"))
        self.assertFalse(oracle_pipeline._board_skip("C-RUNNING"))

    def test_board_skip_halts_blocked_and_stuck_statuses(self):
        self.assertTrue(oracle_pipeline._board_skip(
            "A-BLOCKED (overlap deferred; wait for prior submitted/current sibling feedback)"
        ))
        self.assertTrue(oracle_pipeline._board_skip(
            "A-BLOCKED (overlap needs_human_resolution before Stage A)"
        ))
        self.assertTrue(oracle_pipeline._board_skip(
            "B-STUCK (max fit-retargets reached; needs human review)"
        ))
        self.assertTrue(oracle_pipeline._board_skip(
            "C-STUCK (joint Oracle+Claude gate exhausted)"
        ))
        self.assertTrue(oracle_pipeline._board_skip(
            "TIME-STUCK at Stage C: 24.1h elapsed"
        ))
        self.assertTrue(oracle_pipeline._board_skip(
            "PAUSED (theorem_inventory_invalid)"
        ))
        self.assertTrue(oracle_pipeline._board_skip(
            "needs_human_resolution before Stage A"
        ))
        self.assertFalse(oracle_pipeline._board_skip("B-0"))

    def test_discovery_skips_submitted_archive_even_when_status_is_recoverable_a_block(self):
        paper = self._write_paper("submitted_2026_old_rj_archive", r"""
        \section{Archive}
        Historical submitted route with an active replacement fork.
        """)
        active = self._write_paper("2026_current_fq_fork", r"""
        \section{Current}
        Active deep-revision fork.
        """)
        oracle_pipeline.PROGRAM_BOARD.write_text(
            "\n".join([
                "| Directory | Target journal | Status | Notes |",
                "|------|---------|------|---------|",
                "| `submitted_2026_old_rj_archive` | RJ archive | A-BLOCKED (max Stage A rounds exhausted; final audit failed (score=6)) | active FQ deep-revision fork: `2026_current_fq_fork` |",
                "| `2026_current_fq_fork` | Fibonacci Quarterly | A-BLOCKED (FQ deepening audit real block score=6) | current route |",
            ]),
            encoding="utf-8",
        )
        oracle_pipeline._invalidate_board_cache()

        summary = oracle_pipeline.discover_paper_summary(
            respect_assignment=False)

        self.assertNotIn(str(paper), summary["papers"])
        self.assertIn(str(active), summary["papers"])
        self.assertTrue(any(
            "submitted_2026_old_rj_archive" in item
            for item in summary["skipped_status"]
        ))

    def test_semantic_overlap_blocks_unresolved_submitted_sibling(self):
        current = self._write_paper("2026_current_overlap", """
        We prove a Fibonacci finite-window fold theorem. The sliding overlap
        reconstruction has a sharp m >= 3 threshold, gives finite-memory
        conjugacy with an explicit residue window decoder, and identifies the
        Fischer cover.
        """)
        sibling = self._write_paper("submitted_2026_old_overlap", """
        This submitted paper studies Zeckendorf normalization and Fold_m.
        Overlapping windows recover the input for m >= 3. The result gives a
        finite memory inverse, congruence residue decoder, and the right
        Fischer cover of the image shift.
        """)
        self._write_board("拒稿 05-01")

        records = oracle_pipeline.detect_semantic_submission_overlaps(
            current, [sibling], min_shared_markers=3)

        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["sibling"], "submitted_2026_old_overlap")
        self.assertIn("m_ge_3_threshold", records[0]["shared_claim_markers"])

    def test_semantic_overlap_allows_explicitly_closed_sibling(self):
        current = self._write_paper("2026_current_overlap", """
        We prove a Fibonacci finite-window fold theorem. The sliding overlap
        reconstruction has a sharp m >= 3 threshold, gives finite-memory
        conjugacy with an explicit residue window decoder, and identifies the
        Fischer cover.
        """)
        sibling = self._write_paper("submitted_2026_old_overlap", """
        This submitted paper studies Zeckendorf normalization and Fold_m.
        Overlapping windows recover the input for m >= 3. The result gives a
        finite memory inverse, congruence residue decoder, and the right
        Fischer cover of the image shift.
        """)
        self._write_board("拒稿 05-01；路线关闭；不回 Stage A",
                          "core merged into current paper")

        records = oracle_pipeline.detect_semantic_submission_overlaps(
            current, [sibling], min_shared_markers=3)

        self.assertEqual(records, [])

    def test_stage_a_overlap_gate_writes_harness_report(self):
        current = self._write_paper("2026_current_overlap", """
        We prove a Fibonacci finite-window fold theorem. The sliding overlap
        reconstruction has a sharp m >= 3 threshold, gives finite-memory
        conjugacy with an explicit residue window decoder, and identifies the
        Fischer cover.
        """)
        self._write_paper("submitted_2026_old_overlap", """
        This submitted paper studies Zeckendorf normalization and Fold_m.
        Overlapping windows recover the input for m >= 3. The result gives a
        finite memory inverse, congruence residue decoder, and the right
        Fischer cover of the image shift.
        """)
        self._write_board("æ‹’ç¨¿ 05-01")
        state = oracle_pipeline.PaperState(
            paper_dir=str(current),
            paper_name=current.name,
        )

        ok = oracle_pipeline.run_semantic_submission_overlap_gate(
            state, dry_run=True, tag="[test]"
        )

        self.assertFalse(ok)
        report = json.loads((current / "semantic_overlap_blockers.json").read_text(
            encoding="utf-8"))
        self.assertEqual(report["schema_version"], 1)
        self.assertTrue(report["gate_failed"])
        self.assertEqual(report["summary"]["deferred_wait_for_prior_submission"], 1)
        self.assertIn("defer this later draft", state.error)
        self.assertEqual(report["findings"][0]["paper_b"], "submitted_2026_old_overlap")
        self.assertEqual(
            report["findings"][0]["classification"],
            "deferred_wait_for_prior_submission",
        )

    def test_no_claude_still_writes_deterministic_overlap_block_to_board(self):
        current = self._write_paper("2026_current_overlap", """
        We prove a Fibonacci finite-window fold theorem. The sliding overlap
        reconstruction has a sharp m >= 3 threshold, gives finite-memory
        conjugacy with an explicit residue window decoder, and identifies the
        Fischer cover.
        """)
        self._write_paper("submitted_2026_old_overlap", """
        This submitted paper studies Zeckendorf normalization and Fold_m.
        Overlapping windows recover the input for m >= 3. The result gives a
        finite memory inverse, congruence residue decoder, and the right
        Fischer cover of the image shift.
        """)
        self._write_board("rejected 05-01")
        state = oracle_pipeline.PaperState(
            paper_dir=str(current),
            paper_name=current.name,
        )
        old_claude_enabled = oracle_pipeline.CLAUDE_ENABLED
        try:
            oracle_pipeline.CLAUDE_ENABLED = False
            ok = oracle_pipeline.run_semantic_submission_overlap_gate(
                state, dry_run=False, tag="[test]"
            )
        finally:
            oracle_pipeline.CLAUDE_ENABLED = old_claude_enabled

        self.assertFalse(ok)
        board = oracle_pipeline.PROGRAM_BOARD_MACHINE.read_text(encoding="utf-8")
        self.assertIn("A-BLOCKED", board)
        self.assertIn("defer this later draft", board)

    def test_no_claude_still_writes_terminal_board_statuses(self):
        self._write_board("P0")
        old_claude_enabled = oracle_pipeline.CLAUDE_ENABLED
        try:
            oracle_pipeline.CLAUDE_ENABLED = False
            oracle_pipeline.update_program_board(
                "2026_current_overlap",
                "A-BLOCKED",
                "max Stage A rounds exhausted; final audit failed",
            )
            oracle_pipeline.update_program_board(
                "submitted_2026_old_overlap",
                "C-STUCK",
                "joint Oracle+Claude gate exhausted",
            )
            oracle_pipeline.update_program_board(
                "submitted_2026_old_overlap",
                "C-NEAR-PASS",
                "near-pass final gate; needs final review",
            )
        finally:
            oracle_pipeline.CLAUDE_ENABLED = old_claude_enabled

        board = oracle_pipeline.PROGRAM_BOARD_MACHINE.read_text(encoding="utf-8")
        self.assertIn("A-BLOCKED", board)
        self.assertIn("C-NEAR-PASS", board)

    def test_stage_c_terminal_classifies_recent_accept_submit_as_near_pass(self):
        state = oracle_pipeline.PaperState(
            paper_dir=str(self.root / "2026_near_pass"),
            paper_name="2026_near_pass",
            stage_c_rounds=oracle_pipeline.MAX_STAGE_C_ROUNDS,
            stage_c_verdicts=[
                "oracle:major revision;claude:submit",
                "oracle:accept;claude:submit",
                "oracle:accept;claude:submit",
            ],
        )

        status, detail = oracle_pipeline.classify_stage_c_terminal(state)

        self.assertEqual(status, "C-NEAR-PASS")
        self.assertIn("final review", detail)
        self.assertIn("report to the user", detail)

    def test_stage_c_terminal_classifies_repeated_revisions_as_hard_stuck(self):
        state = oracle_pipeline.PaperState(
            paper_dir=str(self.root / "2026_hard_stuck"),
            paper_name="2026_hard_stuck",
            stage_c_rounds=oracle_pipeline.MAX_STAGE_C_ROUNDS,
            stage_c_verdicts=[
                "oracle:major revision;claude:revise",
                "oracle:major revision;claude:revise",
                "oracle:reject;claude:revise",
            ],
        )

        status, detail = oracle_pipeline.classify_stage_c_terminal(state)

        self.assertEqual(status, "C-HARD-STUCK")
        self.assertIn("major revision", detail.lower())
        self.assertIn("ask the user", detail)

    def test_stage_c_terminal_does_not_treat_extraction_word_as_infra(self):
        state = oracle_pipeline.PaperState(
            paper_dir=str(self.root / "2026_near_pass"),
            paper_name="2026_near_pass",
            stage_c_rounds=oracle_pipeline.MAX_STAGE_C_ROUNDS,
            stage_c_verdicts=[
                "oracle:accept;claude:submit",
                "oracle:accept;claude:submit",
            ],
            history=[
                {
                    "stage": "C",
                    "action": "oracle_final_review",
                    "verdict": "accept",
                    "detail": "Overall verdict: Accept. No blockers. "
                              "Do not refresh; extraction-safe prompt worked.",
                },
                {
                    "stage": "C",
                    "action": "codex_independent_review",
                    "verdict": "submit",
                    "detail": '{"verdict":"submit","issues":[]}',
                },
            ],
        )

        status, _detail = oracle_pipeline.classify_stage_c_terminal(state)

        self.assertEqual(status, "C-NEAR-PASS")

    def test_stage_c_terminal_prioritizes_recent_clean_accepts_over_old_scope_text(self):
        state = oracle_pipeline.PaperState(
            paper_dir=str(self.root / "2026_near_pass_scope_text"),
            paper_name="2026_near_pass_scope_text",
            stage_c_rounds=oracle_pipeline.MAX_STAGE_C_ROUNDS,
            stage_c_verdicts=[
                "oracle:major revision;claude:submit",
                "oracle:accept;claude:submit",
                "oracle:accept;claude:submit",
            ],
            history=[
                {
                    "stage": "C",
                    "action": "codex_independent_review",
                    "verdict": "submit",
                    "detail": "low priority journal template check only",
                },
            ],
        )

        status, _detail = oracle_pipeline.classify_stage_c_terminal(state)

        self.assertEqual(status, "C-NEAR-PASS")

    def test_stage_c_terminal_normalizer_recovers_drifted_near_pass_state(self):
        self._write_board("P0")
        state = oracle_pipeline.PaperState(
            paper_dir=str(self.root / "submitted_2026_old_overlap"),
            paper_name="submitted_2026_old_overlap",
            current_stage="A",
            current_round=0,
            stage_c_rounds=oracle_pipeline.MAX_STAGE_C_ROUNDS,
            stage_c_verdicts=[
                "oracle:major revision;claude:submit",
                "oracle:accept;claude:submit",
                "oracle:accept;claude:submit",
            ],
        )

        normalized = oracle_pipeline.normalize_stage_c_terminal_state(state)

        self.assertTrue(normalized)
        self.assertEqual(state.current_stage, "C")
        self.assertEqual(state.current_round, oracle_pipeline.MAX_STAGE_C_ROUNDS)
        self.assertTrue(state.error.startswith("C-NEAR-PASS:"))
        board = oracle_pipeline.PROGRAM_BOARD_MACHINE.read_text(encoding="utf-8")
        self.assertIn("submitted_2026_old_overlap", board)
        self.assertIn("C-NEAR-PASS", board)

    def test_run_paper_pipeline_preserves_structured_stage_c_terminal_error(self):
        paper = oracle_pipeline.PAPERS_PUB_DIR / "submitted_2026_old_overlap"
        paper.mkdir(exist_ok=True)
        (paper / "main.tex").write_text("\\title{Near Pass}\n", encoding="utf-8")
        self._write_board("C-NEAR-PASS")
        state = oracle_pipeline.PaperState(
            paper_dir=str(paper),
            paper_name="submitted_2026_old_overlap",
            current_stage="C",
            current_round=oracle_pipeline.MAX_STAGE_C_ROUNDS,
            stage_c_rounds=oracle_pipeline.MAX_STAGE_C_ROUNDS,
            stage_c_verdicts=[
                "oracle:accept;claude:submit",
                "oracle:accept;claude:submit",
            ],
            error="C-NEAR-PASS: existing final-review lane",
        )
        oracle_pipeline.save_state(state)

        old_runner = oracle_pipeline.STAGE_RUNNERS["C"]
        try:
            def fail_if_called(_state, **_kwargs):
                raise AssertionError("Stage C runner should not be called")

            oracle_pipeline.STAGE_RUNNERS["C"] = fail_if_called
            ok, loaded = oracle_pipeline.run_paper_pipeline(str(paper))
        finally:
            oracle_pipeline.STAGE_RUNNERS["C"] = old_runner

        self.assertFalse(ok)
        self.assertEqual(loaded.current_stage, "C")
        self.assertTrue(loaded.error.startswith("C-NEAR-PASS:"))

    def test_dashboard_stage_cell_preserves_structured_stage_c_terminal_status(self):
        self.assertEqual(
            oracle_pipeline._dashboard_stage_cell({
                "current_stage": "C",
                "error": "C-NEAR-PASS: recent accept/submit",
            }),
            "C-NEAR-PASS",
        )
        self.assertEqual(
            oracle_pipeline._dashboard_stage_cell({
                "current_stage": "C",
                "error": "Stage C stuck: joint Oracle+Claude gate exhausted",
            }),
            "FAILED",
        )

    def test_stage_a_block_board_detail_does_not_cut_words_mid_reason(self):
        self._write_board("P0")
        state = oracle_pipeline.PaperState(
            paper_dir=str(self.root / "2026_current_overlap"),
            paper_name="2026_current_overlap",
        )

        oracle_pipeline._stage_a_block(
            state,
            "A2 produced no substantive theorem change: FAKE EXTENSION: "
            "no new theorems added, content delta only +261 chars "
            "(threshold: 500). Codex likely rephrased without adding substance.",
            dry_run=False,
        )

        board = oracle_pipeline.PROGRAM_BOARD_MACHINE.read_text(encoding="utf-8")
        self.assertIn("A-BLOCKED", board)
        self.assertIn("fake extension", board.lower())
        self.assertIn("delta +261 < threshold 500", board)
        self.assertNotIn("thresho)", board)
        self.assertNotIn("thresh)", board)

    def test_stage_a_fake_extension_negative_delta_is_not_double_signed(self):
        self._write_board("P0")
        state = oracle_pipeline.PaperState(
            paper_dir=str(self.root / "2026_current_overlap"),
            paper_name="2026_current_overlap",
        )

        reason = (
            "A2 produced no substantive theorem change: FAKE EXTENSION: "
            "no new theorems added, content delta only -829 chars "
            "(threshold: 500). Codex likely rephrased without adding substance."
        )
        oracle_pipeline._stage_a_block(state, reason, dry_run=False)

        board = oracle_pipeline.PROGRAM_BOARD_MACHINE.read_text(encoding="utf-8")
        self.assertIn("delta -829 < threshold 500", board)
        self.assertNotIn("+-829", board)
        self.assertNotIn("delta +-", board)

    def test_substantive_change_negative_delta_is_not_double_signed(self):
        paper = self._write_paper(
            "2026_current_overlap",
            "\\documentclass{article}\n"
            "\\begin{document}\n"
            "\\begin{theorem}\\label{thm:base}Short result.\\end{theorem}\n"
            "\\end{document}\n",
        )
        pre = [(
            "thm:base",
            "This prior theorem body is deliberately much longer than the "
            "new extracted body so the delta becomes negative.",
        )]

        ok, reason = oracle_pipeline.verify_substantive_change(paper, pre)

        self.assertFalse(ok)
        self.assertIn("content delta only -", reason)
        self.assertNotIn("+-", reason)

    def test_stage_a_runs_dedup_after_proof_gap_theoremization(self):
        paper = self._write_paper(
            "2026_current_overlap",
            "\\documentclass{article}\n"
            "\\begin{document}\n"
            "\\begin{theorem}\\label{thm:base}Base statement with enough text "
            "for extraction and comparison.\\end{theorem}\n"
            "\\end{document}\n",
        )
        (paper / "scope_contract.md").write_text(
            "Scope contract.\n" + ("This paper keeps the stated theorem scope. " * 30),
            encoding="utf-8",
        )
        (paper / "scope_contract.json").write_text(json.dumps({
            "valid": True,
            "research_question": "Test question",
            "target_journal_bar": "Test Journal",
            "main_project_bindings": [],
            "in_scope": [{"id": "scope"}],
            "must_prove_in_this_paper": [{"id": "proof"}],
            "supporting_only": [],
            "out_of_scope": [],
            "split_policy": "no split",
            "failure_modes_to_control": [],
        }), encoding="utf-8")
        self._write_board("P0")
        state = oracle_pipeline.PaperState(
            paper_dir=str(paper),
            paper_name=paper.name,
            target_journal="Test Journal",
            stage_a_scope_done=True,
        )
        inventory = {
            "in_scope_present": [],
            "missing_in_scope_results": [],
            "weak_in_scope_core_results": [],
            "proof_gaps": [{"id": "gap-1"}],
            "supporting_appendix_or_background": [],
            "out_of_scope_strong_results": [],
            "split_candidates": [],
            "irrelevant_or_remove": [],
            "naive_truncation_risks": [],
            "journal_style_gaps": [],
        }
        dedup_calls = []
        class StopAfterDedup(Exception):
            pass

        def fake_inventory(*args, **kwargs):
            del args, kwargs
            return inventory

        def fake_dedup(state_arg, **kwargs):
            dedup_calls.append((state_arg.paper_name, kwargs.get("round_num")))
            raise StopAfterDedup()

        old_max_rounds = oracle_pipeline.MAX_STAGE_A_ROUNDS
        try:
            oracle_pipeline.MAX_STAGE_A_ROUNDS = 1
            with mock.patch.object(
                oracle_pipeline,
                "_run_stage_a_inventory",
                side_effect=fake_inventory,
            ), mock.patch.object(
                oracle_pipeline,
                "codex_exec",
                return_value="proof gaps closed",
            ), mock.patch.object(
                oracle_pipeline,
                "compile_gate",
                return_value=True,
            ), mock.patch.object(
                oracle_pipeline,
                "git_commit",
                return_value="abc123",
            ), mock.patch.object(
                oracle_pipeline,
                "run_stage_a_dedup",
                side_effect=fake_dedup,
            ):
                with self.assertRaises(StopAfterDedup):
                    oracle_pipeline.run_stage_a(state, dry_run=False)
        finally:
            oracle_pipeline.MAX_STAGE_A_ROUNDS = old_max_rounds

        self.assertEqual(dedup_calls, [(paper.name, 1)])

    def test_discover_skips_done_state_even_if_board_status_is_stale(self):
        paper = self._write_paper("2026_done_but_stale_board", "Done paper.")
        oracle_pipeline.PROGRAM_BOARD.write_text(
            "\n".join([
                "| Directory | Target journal | Status | Reroute |",
                "|------|---------|------|---------|",
                "| `2026_done_but_stale_board` | Test J. | B-PAUSED | — |",
            ]),
            encoding="utf-8",
        )
        oracle_pipeline._invalidate_board_cache()
        oracle_pipeline.STATE_DIR.mkdir(parents=True, exist_ok=True)
        state = oracle_pipeline.PaperState(
            paper_dir=str(paper),
            paper_name=paper.name,
            current_stage="DONE",
        )
        oracle_pipeline.save_state(state)

        papers = oracle_pipeline.discover_papers(respect_assignment=False)

        self.assertEqual(papers, [])

    def test_discovery_summary_explains_gate_exhaustion(self):
        self._write_paper("2026_blocked", "Blocked paper.")
        self._write_paper("2026_unregistered", "Unregistered paper.")
        oracle_pipeline.PROGRAM_BOARD.write_text(
            "\n".join([
                "| Directory | Target journal | Status | Reroute |",
                "|------|---------|------|---------|",
                "| `2026_blocked` | Test J. | C-STUCK | — |",
            ]),
            encoding="utf-8",
        )
        oracle_pipeline._invalidate_board_cache()

        summary = oracle_pipeline.discover_paper_summary(
            respect_assignment=False
        )

        self.assertEqual(summary["runnable_count"], 0)
        self.assertEqual(summary["skipped_status_count"], 1)
        self.assertEqual(summary["skipped_unregistered_count"], 1)
        self.assertEqual(summary["diagnosis"], "gate_exhausted")

    def test_discovery_ignores_newmath_intake_seed_directories(self):
        intake_seed = (
            self.root
            / "newmath_intake"
            / "seeds"
            / "bedc_automation_pipeline"
        )
        intake_seed.mkdir(parents=True)
        (intake_seed / "seed_packet.md").write_text(
            "intake only; not an active paper\n",
            encoding="utf-8",
        )
        self._write_paper("2026_registered_active", "Active paper.")
        oracle_pipeline.PROGRAM_BOARD.write_text(
            "\n".join([
                "| Directory | Target journal | Status | Reroute |",
                "|------|---------|------|---------|",
                "| `2026_registered_active` | Test J. | A-0 | - |",
            ]),
            encoding="utf-8",
        )
        oracle_pipeline._invalidate_board_cache()

        summary = oracle_pipeline.discover_paper_summary(
            respect_assignment=False
        )

        self.assertEqual(summary["candidate_count"], 1)
        self.assertEqual(summary["papers"], [str(self.root / "2026_registered_active")])
        self.assertFalse(any("newmath_intake" in p for p in summary["papers"]))

    def test_publication_sibling_scan_ignores_newmath_intake(self):
        current = self._write_paper("2026_current_overlap", "Current paper.")
        sibling = self._write_paper("submitted_2026_prior_overlap", "Prior paper.")
        intake_seed = (
            self.root
            / "newmath_intake"
            / "seeds"
            / "bedc_automation_pipeline"
        )
        intake_seed.mkdir(parents=True)
        (intake_seed / "seed_packet.md").write_text(
            "intake only; not an active paper\n",
            encoding="utf-8",
        )

        siblings = oracle_pipeline._publication_sibling_papers(current)

        self.assertEqual(siblings, [sibling])
        self.assertFalse(any("newmath_intake" in str(path) for path in siblings))

class OraclePipelineStateMigrationTests(unittest.TestCase):
    def setUp(self):
        import tempfile
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._real_state_dir = oracle_pipeline.STATE_DIR
        oracle_pipeline.STATE_DIR = self.root / "pipeline_state"

    def tearDown(self):
        oracle_pipeline.STATE_DIR = self._real_state_dir
        self.tmp.cleanup()

    def test_load_state_normalizes_legacy_stage_a_metrics_list(self):
        paper_name = "legacy_state_paper"
        oracle_pipeline.STATE_DIR.mkdir(parents=True, exist_ok=True)
        state_file = oracle_pipeline._state_file(paper_name)
        state_file.write_text(json.dumps({
            "paper_name": paper_name,
            "paper_dir": str(self.root / paper_name),
            "current_stage": "B",
            "stage_a_passed": True,
            "stage_a_audit_metrics": [],
            "stage_a_inventory": [],
            "stage_b_issue_streaks": [],
        }), encoding="utf-8")

        state = oracle_pipeline.load_state(paper_name)

        self.assertIsNotNone(state)
        self.assertEqual(state.stage_a_audit_metrics, {})
        self.assertEqual(state.stage_a_inventory, {})
        self.assertEqual(state.stage_b_issue_streaks, {})
        self.assertFalse(oracle_pipeline.stage_a_ready_for_b(state))

    def test_save_state_uses_atomic_replace_without_truncating_existing_state(self):
        paper_name = "atomic_state_paper"
        original = oracle_pipeline.PaperState(
            paper_dir=str(self.root / paper_name),
            paper_name=paper_name,
        )
        original.current_stage = "A"
        oracle_pipeline.save_state(original)
        state_file = oracle_pipeline._state_file(paper_name)
        before = json.loads(state_file.read_text(encoding="utf-8"))

        updated = oracle_pipeline.PaperState(
            paper_dir=str(self.root / paper_name),
            paper_name=paper_name,
        )
        updated.current_stage = "B"
        real_replace = oracle_pipeline.os.replace

        def fail_replace(src, dst):
            raise OSError("simulated replace failure")

        try:
            oracle_pipeline.os.replace = fail_replace
            with self.assertRaises(OSError):
                oracle_pipeline.save_state(updated)
        finally:
            oracle_pipeline.os.replace = real_replace

        after = json.loads(state_file.read_text(encoding="utf-8"))
        self.assertEqual(after, before)
        self.assertEqual(after["current_stage"], "A")
        self.assertFalse(list(oracle_pipeline.STATE_DIR.glob("*.tmp")))


class OraclePipelineStageAAuditClassificationTests(unittest.TestCase):
    def test_stage_a_source_reader_expands_local_input_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper = Path(tmp)
            (paper / "sections").mkdir()
            (paper / "source").mkdir()
            (paper / "main.tex").write_text(
                "\\documentclass{article}\n"
                "\\begin{document}\n"
                "\\input{sections/intro}\n"
                "\\input{source/thm__core}\n"
                "\\end{document}\n",
                encoding="utf-8",
            )
            (paper / "sections" / "intro.tex").write_text(
                "\\section{Introduction}\nBody.\n",
                encoding="utf-8",
            )
            (paper / "source" / "thm__core.tex").write_text(
                "\\begin{theorem}\\label{thm:core}Core result.\\end{theorem}\n",
                encoding="utf-8",
            )

            text = oracle_pipeline._read_stage_a_source_text(paper)

        self.assertIn("\\section{Introduction}", text)
        self.assertIn("\\begin{theorem}", text)
        self.assertIn("Core result", text)

    def test_read_json_artifact_accepts_utf8_bom(self):
        with tempfile.TemporaryDirectory() as tmp:
            paper = Path(tmp)
            payload = {
                "valid": True,
                "in_scope_present": [],
                "missing_in_scope_results": [],
                "weak_in_scope_core_results": [],
                "proof_gaps": [],
                "supporting_appendix_or_background": [],
                "out_of_scope_strong_results": [],
                "split_candidates": [],
                "irrelevant_or_remove": [],
                "naive_truncation_risks": [],
                "journal_style_gaps": [],
            }
            (paper / "theorem_inventory.json").write_text(
                json.dumps(payload),
                encoding="utf-8-sig",
            )

            artifact = oracle_pipeline._read_json_artifact(
                paper,
                "theorem_inventory.json",
            )

            self.assertEqual(artifact, payload)

    def test_parse_json_from_output_handles_journal_fit_json_with_suggestions(self):
        text = (
            "Here is the journal fit assessment:\n"
            "```json\n"
            "{\n"
            "  \"fit_score\": 7,\n"
            "  \"fit_verdict\": \"good\",\n"
            "  \"subject_match\": 8,\n"
            "  \"depth_match\": 7,\n"
            "  \"style_match\": 6,\n"
            "  \"rationale\": \"The topic is a plausible fit.\",\n"
            "  \"suggested_journals\": [\n"
            "    {\n"
            "      \"name\": \"Ergodic Theory and Dynamical Systems\",\n"
            "      \"fit_score\": 8,\n"
            "      \"reason\": \"better subject match\"\n"
            "    },\n"
            "    {\n"
            "      \"name\": \"Dynamical Systems\",\n"
            "      \"fit_score\": 7,\n"
            "      \"reason\": \"specialized scope\"\n"
            "    }\n"
            "  ]\n"
            "}\n"
            "```\n"
            "No edits were made."
        )

        parsed = oracle_pipeline.parse_json_from_output(text)

        self.assertEqual(parsed["fit_score"], 7)
        self.assertEqual(
            parsed["suggested_journals"][0]["name"],
            "Ergodic Theory and Dynamical Systems",
        )

    def test_parse_json_from_output_handles_bare_journal_fit_json_with_suggestions(self):
        text = (
            "Assessment follows.\n"
            "{"
            "\"fit_score\": 5,"
            "\"fit_verdict\": \"marginal\","
            "\"subject_match\": 5,"
            "\"depth_match\": 6,"
            "\"style_match\": 5,"
            "\"rationale\": \"Possible but not ideal.\","
            "\"suggested_journals\": ["
            "{\"name\": \"Journal of Algebra\", \"fit_score\": 7,"
            "\"reason\": \"better algebra audience\"}"
            "]"
            "}"
            "\nDone."
        )

        parsed = oracle_pipeline.parse_json_from_output(text)

        self.assertEqual(parsed["fit_score"], 5)
        self.assertEqual(parsed["suggested_journals"][0]["fit_score"], 7)

    def test_parse_json_from_output_handles_bare_nested_stage_a_audit(self):
        text = (
            "Here is the requested audit:\n"
            "{"
            "\"metrics\": {"
            "\"scope_coverage\": 8,"
            "\"journal_fit\": 8,"
            "\"split_hygiene\": 8"
            "},"
            "\"verdict\": \"pass\","
            "\"work_packages\": ["
            "{"
            "\"owner\": \"codex_math\","
            "\"priority\": \"high\","
            "\"task\": \"tighten theorem dependency\""
            "}"
            "],"
            "\"ready_for_oracle_review\": true"
            "}"
            "\nEnd."
        )

        parsed = oracle_pipeline.parse_json_from_output(text)

        self.assertEqual(parsed["metrics"]["scope_coverage"], 8)
        self.assertEqual(parsed["work_packages"][0]["owner"], "codex_math")

    def test_stage_a_audit_codex_calls_have_log_tags(self):
        import tempfile
        tmp = tempfile.TemporaryDirectory()
        root = Path(tmp.name)
        old_state_dir = oracle_pipeline.STATE_DIR
        old_codex_exec = oracle_pipeline.codex_exec
        old_claude_enabled = oracle_pipeline.CLAUDE_ENABLED
        calls = []

        def fake_codex_exec(prompt, **kwargs):
            del prompt
            calls.append(kwargs)
            if kwargs.get("agent_role") == "stage_a_structural_audit":
                metrics = {
                    "scope_coverage": 8,
                    "journal_fit": 8,
                    "split_hygiene": 8,
                }
                extra = '"work_packages": [],'
            else:
                metrics = {
                    "theorem_completeness": 8,
                    "proof_integrity": 8,
                    "depth_novelty": 8,
                }
                extra = ""
            return (
                "```json\n"
                "{"
                f"\"metrics\": {json.dumps(metrics)},"
                "\"verdict\": \"pass\","
                "\"blockers\": [],"
                "\"required_revisions\": [],"
                f"{extra}"
                "\"split_required\": false,"
                "\"split_reasons\": [],"
                "\"ready_for_oracle_review\": true"
                "}\n"
                "```"
            )

        try:
            oracle_pipeline.STATE_DIR = root / "pipeline_state"
            oracle_pipeline.CLAUDE_ENABLED = False
            oracle_pipeline.codex_exec = fake_codex_exec
            paper_dir = root / "paper"
            paper_dir.mkdir()
            state = oracle_pipeline.PaperState(
                paper_dir=str(paper_dir),
                paper_name="paper_with_logged_audit",
            )

            oracle_pipeline._run_stage_a_audit_once(state, 1)
        finally:
            oracle_pipeline.STATE_DIR = old_state_dir
            oracle_pipeline.codex_exec = old_codex_exec
            oracle_pipeline.CLAUDE_ENABLED = old_claude_enabled
            tmp.cleanup()

        log_tags = {
            call.get("agent_role"): call.get("log_tag")
            for call in calls
        }
        self.assertIn("stage_a_codex_math_audit", log_tags)
        self.assertIn("stage_a_structural_audit", log_tags)
        self.assertTrue(log_tags["stage_a_codex_math_audit"])
        self.assertTrue(log_tags["stage_a_structural_audit"])
        self.assertNotEqual(
            log_tags["stage_a_codex_math_audit"],
            log_tags["stage_a_structural_audit"],
        )

    def test_partial_unparseable_audit_with_real_blockers_is_real_block(self):
        audit = {
            "metrics": {
                "theorem_completeness": 6,
                "proof_integrity": 5,
                "depth_novelty": 6,
            },
            "verdict": "revise",
            "audit_unparseable": True,
            "blockers": [
                {"auditor": "codex", "reason": "central theorem unproved"},
                {"auditor": "codex", "reason": "downstream theorem depends on gap"},
                {
                    "auditor": "structural_fallback",
                    "reason": "audit JSON was empty or missing required metrics",
                },
            ],
            "required_revisions": [
                {"auditor": "codex", "reason": "add self-contained proof"},
            ],
        }
        state = oracle_pipeline.PaperState(
            paper_dir=".",
            paper_name="partial_stage_a_audit",
        )

        classification = oracle_pipeline._classify_stage_a_failure(state, audit)

        self.assertEqual(classification, "real_block")


class OraclePipelineJournalSelectionTests(unittest.TestCase):
    def setUp(self):
        import tempfile
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._real_papers_pub_dir = oracle_pipeline.PAPERS_PUB_DIR
        self._real_program_board = oracle_pipeline.PROGRAM_BOARD
        self._real_state_dir = oracle_pipeline.STATE_DIR
        oracle_pipeline.PAPERS_PUB_DIR = self.root / "publication"
        oracle_pipeline.PROGRAM_BOARD = oracle_pipeline.PAPERS_PUB_DIR / "PROGRAM_BOARD.md"
        oracle_pipeline.STATE_DIR = self.root / "state"
        oracle_pipeline.PAPERS_PUB_DIR.mkdir(parents=True)
        oracle_pipeline.STATE_DIR.mkdir(parents=True)
        oracle_pipeline._invalidate_board_cache()

    def tearDown(self):
        oracle_pipeline.PAPERS_PUB_DIR = self._real_papers_pub_dir
        oracle_pipeline.PROGRAM_BOARD = self._real_program_board
        oracle_pipeline.STATE_DIR = self._real_state_dir
        oracle_pipeline._invalidate_board_cache()
        self.tmp.cleanup()

    def test_detect_target_journal_treats_board_dash_as_missing(self):
        paper = oracle_pipeline.PAPERS_PUB_DIR / "2026_dash_journal"
        paper.mkdir()
        (paper / "main.tex").write_text(
            "\\title{Dash Journal Test}\n",
            encoding="utf-8",
        )
        oracle_pipeline.PROGRAM_BOARD.write_text(
            "\n".join([
                "| Directory | Target journal | Status | Reroute |",
                "|------|---------|------|---------|",
                "| `2026_dash_journal` | — | P0 | — |",
            ]),
            encoding="utf-8",
        )
        oracle_pipeline._invalidate_board_cache()

        self.assertEqual(oracle_pipeline.detect_target_journal(str(paper)), "")

    def test_run_paper_pipeline_selects_journal_when_board_target_missing(self):
        paper = oracle_pipeline.PAPERS_PUB_DIR / "2026_select_journal"
        paper.mkdir()
        (paper / "main.tex").write_text(
            "\\title{Symbolic Dynamics Test}\n"
            "\\begin{abstract}A paper about symbolic dynamics.\\end{abstract}\n",
            encoding="utf-8",
        )
        oracle_pipeline.PROGRAM_BOARD.write_text(
            "\n".join([
                "| Directory | Target journal | Status | Reroute |",
                "|------|---------|------|---------|",
                "| `2026_select_journal` | — | P0 | — |",
            ]),
            encoding="utf-8",
        )
        oracle_pipeline._invalidate_board_cache()

        calls = []
        old_codex_exec = oracle_pipeline.codex_exec
        old_stage_f = oracle_pipeline.STAGE_RUNNERS["F"]
        old_stage_a = oracle_pipeline.STAGE_RUNNERS["A"]
        try:
            def fake_codex_exec(prompt, **kwargs):
                calls.append((prompt, kwargs))
                return (
                    "```json\n"
                    "{\"recommended_journal\": \"Ergodic Theory and Dynamical Systems\","
                    "\"fit_score\": 8,"
                    "\"rationale\": \"Best scope match.\","
                    "\"alternatives\": []}\n"
                    "```"
                )

            def fake_stage_f(state, **kwargs):
                del kwargs
                state.stage_f_passed = True
                state.log_event("F", "stub", detail=state.target_journal)
                oracle_pipeline.save_state(state)
                return True

            def fake_stage_a(state, **kwargs):
                del kwargs
                state.current_stage = "A"
                oracle_pipeline.save_state(state)
                return False

            oracle_pipeline.codex_exec = fake_codex_exec
            oracle_pipeline.STAGE_RUNNERS["F"] = fake_stage_f
            oracle_pipeline.STAGE_RUNNERS["A"] = fake_stage_a

            ok, state = oracle_pipeline.run_paper_pipeline(
                str(paper),
                dry_run=False,
            )
        finally:
            oracle_pipeline.codex_exec = old_codex_exec
            oracle_pipeline.STAGE_RUNNERS["F"] = old_stage_f
            oracle_pipeline.STAGE_RUNNERS["A"] = old_stage_a

        self.assertFalse(ok)
        self.assertEqual(
            state.target_journal,
            "Ergodic Theory and Dynamical Systems",
        )
        self.assertTrue(calls)
        self.assertIn("select the best target journal", calls[0][0].lower())

    def test_missing_journal_state_reruns_stage_f_after_selection(self):
        paper = oracle_pipeline.PAPERS_PUB_DIR / "2026_resume_missing_journal"
        paper.mkdir()
        (paper / "main.tex").write_text(
            "\\title{Resume Missing Journal Test}\n"
            "\\begin{abstract}A paper about ergodic rigidity.\\end{abstract}\n",
            encoding="utf-8",
        )
        oracle_pipeline.PROGRAM_BOARD.write_text(
            "\n".join([
                "| Directory | Target journal | Status | Reroute |",
                "|------|---------|------|---------|",
                "| `2026_resume_missing_journal` | â€” | P0 | â€” |",
            ]),
            encoding="utf-8",
        )
        oracle_pipeline._invalidate_board_cache()
        old_state = oracle_pipeline.PaperState(
            paper_dir=str(paper),
            paper_name="2026_resume_missing_journal",
            target_journal="â€”",
            current_stage="A",
            stage_f_original_journal="â€”",
            stage_f_passed=True,
            stage_a_rounds=1,
        )
        oracle_pipeline.save_state(old_state)

        calls = []
        old_codex_exec = oracle_pipeline.codex_exec
        old_stage_f = oracle_pipeline.STAGE_RUNNERS["F"]
        old_stage_a = oracle_pipeline.STAGE_RUNNERS["A"]
        try:
            def fake_codex_exec(prompt, **kwargs):
                calls.append(("codex", prompt, kwargs))
                return (
                    "```json\n"
                    "{\"recommended_journal\": \"Ergodic Theory and Dynamical Systems\","
                    "\"fit_score\": 8,"
                    "\"rationale\": \"Best scope match.\","
                    "\"alternatives\": []}\n"
                    "```"
                )

            def fake_stage_f(state, **kwargs):
                calls.append(("F", state.current_stage, state.target_journal))
                del kwargs
                state.stage_f_passed = True
                oracle_pipeline.save_state(state)
                return True

            def fake_stage_a(state, **kwargs):
                calls.append(("A", state.current_stage, state.target_journal))
                del kwargs
                return False

            oracle_pipeline.codex_exec = fake_codex_exec
            oracle_pipeline.STAGE_RUNNERS["F"] = fake_stage_f
            oracle_pipeline.STAGE_RUNNERS["A"] = fake_stage_a

            ok, state = oracle_pipeline.run_paper_pipeline(
                str(paper),
                dry_run=False,
            )
        finally:
            oracle_pipeline.codex_exec = old_codex_exec
            oracle_pipeline.STAGE_RUNNERS["F"] = old_stage_f
            oracle_pipeline.STAGE_RUNNERS["A"] = old_stage_a

        self.assertFalse(ok)
        self.assertEqual(
            state.target_journal,
            "Ergodic Theory and Dynamical Systems",
        )
        self.assertIn(
            ("F", "F", "Ergodic Theory and Dynamical Systems"),
            calls,
        )
        self.assertIn(
            ("A", "A", "Ergodic Theory and Dynamical Systems"),
            calls,
        )

    def test_missing_journal_selection_resets_stage_a_evidence(self):
        paper = oracle_pipeline.PAPERS_PUB_DIR / "2026_resume_stale_a_rounds"
        paper.mkdir()
        (paper / "main.tex").write_text(
            "\\title{Resume Stale A Rounds Test}\n"
            "\\begin{abstract}A paper about arithmetic rigidity.\\end{abstract}\n",
            encoding="utf-8",
        )
        oracle_pipeline.PROGRAM_BOARD.write_text(
            "\n".join([
                "| Directory | Target journal | Status | Reroute |",
                "|------|---------|------|---------|",
                "| `2026_resume_stale_a_rounds` | — | P0 | — |",
            ]),
            encoding="utf-8",
        )
        oracle_pipeline._invalidate_board_cache()
        old_state = oracle_pipeline.PaperState(
            paper_dir=str(paper),
            paper_name="2026_resume_stale_a_rounds",
            target_journal="—",
            current_stage="A",
            stage_f_original_journal="—",
            stage_f_passed=True,
            stage_a_rounds=5,
            current_round=5,
            stage_a_inventory={"in_scope_present": [{"id": "old"}]},
            stage_a_scores=[4],
            stage_a_audit_rounds=1,
            stage_a_audit_metrics={"score": 4},
        )
        oracle_pipeline.save_state(old_state)

        calls = []
        old_codex_exec = oracle_pipeline.codex_exec
        old_stage_f = oracle_pipeline.STAGE_RUNNERS["F"]
        old_stage_a = oracle_pipeline.STAGE_RUNNERS["A"]
        try:
            def fake_codex_exec(prompt, **kwargs):
                calls.append(("codex", prompt, kwargs))
                return (
                    "```json\n"
                    "{\"recommended_journal\": \"Journal of Number Theory\","
                    "\"fit_score\": 8,"
                    "\"rationale\": \"Best scope match.\","
                    "\"alternatives\": []}\n"
                    "```"
                )

            def fake_stage_f(state, **kwargs):
                calls.append(("F", state.current_stage, state.stage_a_rounds))
                del kwargs
                state.stage_f_passed = True
                oracle_pipeline.save_state(state)
                return True

            def fake_stage_a(state, **kwargs):
                calls.append(("A", state.current_stage, state.stage_a_rounds,
                              state.current_round, state.stage_a_inventory,
                              state.stage_a_scores,
                              state.stage_a_audit_metrics))
                del kwargs
                return False

            oracle_pipeline.codex_exec = fake_codex_exec
            oracle_pipeline.STAGE_RUNNERS["F"] = fake_stage_f
            oracle_pipeline.STAGE_RUNNERS["A"] = fake_stage_a

            ok, state = oracle_pipeline.run_paper_pipeline(
                str(paper),
                dry_run=False,
            )
        finally:
            oracle_pipeline.codex_exec = old_codex_exec
            oracle_pipeline.STAGE_RUNNERS["F"] = old_stage_f
            oracle_pipeline.STAGE_RUNNERS["A"] = old_stage_a

        self.assertFalse(ok)
        self.assertEqual(state.target_journal, "Journal of Number Theory")
        stage_a_calls = [call for call in calls if call[0] == "A"]
        self.assertEqual(len(stage_a_calls), 1)
        _, _, stage_a_rounds, current_round, inventory, scores, metrics = (
            stage_a_calls[0]
        )
        self.assertEqual(stage_a_rounds, 0)
        self.assertEqual(current_round, 0)
        self.assertEqual(inventory, {})
        self.assertEqual(scores, [])
        self.assertEqual(metrics, {})


class OraclePipelineClaudeFallbackTests(unittest.TestCase):
    def tearDown(self):
        oracle_pipeline.CLAUDE_ENABLED = True

    def test_claude_health_failure_enables_codex_fallback(self):
        oracle_pipeline.CLAUDE_ENABLED = True

        ok = oracle_pipeline._configure_claude_startup_mode(
            dry_run=False,
            no_claude=False,
            health_check=lambda: (False, "Claude quota exhausted"),
        )

        self.assertTrue(ok)
        self.assertFalse(oracle_pipeline.CLAUDE_ENABLED)

    def test_explicit_no_claude_keeps_codex_fallback_enabled(self):
        oracle_pipeline.CLAUDE_ENABLED = True

        ok = oracle_pipeline._configure_claude_startup_mode(
            dry_run=False,
            no_claude=True,
            health_check=lambda: (_ for _ in ()).throw(
                AssertionError("health check should not run")
            ),
        )

        self.assertTrue(ok)
        self.assertFalse(oracle_pipeline.CLAUDE_ENABLED)

class OraclePipelineOracleResponseValidationTests(unittest.TestCase):
    def test_short_labelled_verdict_review_is_valid(self):
        response = (
            "展开收起ChatGPT 说：I will focus on the remaining local issue. "
            "Thought for 2m 35s"
            "Overall verdict: Minor revision\n"
            "The manuscript meets the target journal bar mathematically. "
            "The theorem architecture is now clear, the main estimates are "
            "auditable, and the remaining concern is a local revision in the "
            "references and final displayed coefficient. This is not a "
            "blocker and does not require a new structural contribution. "
            "Correct the named reference entries and keep the current proof "
            "spine. After that correction I would recommend acceptance. "
            "These comments identify the issue, explain the revision, and "
            "state why the paper remains within scope for the journal."
        )

        self.assertLess(len(response), 2000)
        self.assertEqual(oracle_pipeline.extract_verdict(response),
                         "minor revision")
        self.assertTrue(oracle_pipeline.is_oracle_response_valid(response))

    def test_short_unlabelled_preamble_is_invalid(self):
        response = "I will review the manuscript and then provide a verdict."

        self.assertFalse(oracle_pipeline.is_oracle_response_valid(response))

class OracleServerMultiTurnTests(unittest.TestCase):
    """Spin up oracle_server in-process on an ephemeral port and exercise multi-turn."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix="oracle_multiturn_")
        cls._real_oracle_dir = oracle_server.ORACLE_DIR
        cls._real_queue_path = oracle_server.QUEUE_STATE_PATH
        cls._real_results_path = oracle_server.RESULTS_RING_PATH
        cls._real_sessions_dir = oracle_server.SESSIONS_DIR
        oracle_server.ORACLE_DIR = Path(cls.tmp.name)
        oracle_server.QUEUE_STATE_PATH = oracle_server.ORACLE_DIR / "queue_state.json"
        oracle_server.RESULTS_RING_PATH = oracle_server.ORACLE_DIR / "results_ring.json"
        oracle_server.SESSIONS_DIR = oracle_server.ORACLE_DIR / "sessions"

        # Reset module-level state so the class is order-independent.
        oracle_server.task_queue.clear()
        oracle_server.results.clear()
        oracle_server.pending_tasks.clear()
        oracle_server.dispatch_times.clear()
        oracle_server.active_start_times.clear()
        oracle_server.agent_poll_times.clear()
        oracle_server.sessions.clear()

        # Bind to ephemeral port to avoid clashing with the real server.
        cls.server = HTTPServer(("127.0.0.1", 0), oracle_server.OracleHandler)
        cls.port = cls.server.server_address[1]
        cls.thread = threading.Thread(target=cls.server.serve_forever, daemon=True)
        cls.thread.start()
        cls.base = f"http://127.0.0.1:{cls.port}"

    @classmethod
    def tearDownClass(cls):
        cls.server.shutdown()
        cls.server.server_close()
        oracle_server.ORACLE_DIR = cls._real_oracle_dir
        oracle_server.QUEUE_STATE_PATH = cls._real_queue_path
        oracle_server.RESULTS_RING_PATH = cls._real_results_path
        oracle_server.SESSIONS_DIR = cls._real_sessions_dir
        oracle_server.task_queue.clear()
        oracle_server.results.clear()
        oracle_server.pending_tasks.clear()
        oracle_server.dispatch_times.clear()
        oracle_server.active_start_times.clear()
        oracle_server.agent_poll_times.clear()
        oracle_server.sessions.clear()
        cls.tmp.cleanup()

    def setUp(self):
        oracle_server.task_queue.clear()
        oracle_server.results.clear()
        oracle_server.pending_tasks.clear()
        oracle_server.dispatch_times.clear()
        oracle_server.active_start_times.clear()
        oracle_server.agent_poll_times.clear()
        oracle_server.sessions.clear()

    def _post(self, path: str, payload: dict) -> dict:
        req = urllib.request.Request(
            self.base + path,
            data=json.dumps(payload).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        with urllib.request.urlopen(req, timeout=5) as r:
            return json.loads(r.read().decode("utf-8"))

    def _get(self, path: str) -> dict:
        with urllib.request.urlopen(self.base + path, timeout=5) as r:
            return json.loads(r.read().decode("utf-8"))

    def test_status_carries_diagnosis_and_port(self):
        status = self._get("/status")
        self.assertEqual(status["port"], oracle_server.PORT)
        self.assertIn(status["diagnosis"], {"idle", "running", "queue_waiting_for_browser_agent"})

    def test_idle_agent_poll_is_visible_in_status(self):
        task = self._get("/task?agent=oracle_2")
        self.assertEqual(task["status"], "idle")

        status = self._get("/status")

        self.assertIn("oracle_2", status["idle_agents"])
        self.assertIn("oracle_2", status["active_recent_agents"])
        self.assertEqual(status["registered_agents"], 1)

    def test_submit_with_conversation_id_is_multi_turn_capable(self):
        real_queue_path = self.__class__._real_queue_path
        real_before = (
            real_queue_path.stat().st_mtime_ns
            if real_queue_path.exists()
            else None
        )
        ack = self._post("/submit", {
            "task_id": "smoke_new",
            "prompt": "first turn",
            "conversation_id": "",  # ask server to issue
            "tag": "smoke",
            "project_url": "https://chatgpt.com/g/g-p-test/project",
        })
        self.assertEqual(ack["status"], "queued")
        self.assertTrue(ack["conversation_id"].startswith("conv_"))
        self.conv_id = ack["conversation_id"]
        self.assertTrue(oracle_server.QUEUE_STATE_PATH.exists())
        real_after = (
            real_queue_path.stat().st_mtime_ns
            if real_queue_path.exists()
            else None
        )
        self.assertEqual(real_before, real_after)

    def test_continue_requires_known_conversation(self):
        # Bad conv id rejected
        try:
            self._post("/continue", {
                "task_id": "smoke_bad_continue",
                "prompt": "follow-up",
                "conversation_id": "conv_doesnotexist",
            })
        except urllib.error.HTTPError as exc:
            self.assertEqual(exc.code, 404)
            return
        self.fail("/continue with unknown conversation_id should 404")

    def test_continue_after_new_submit_threads_session(self):
        ack_new = self._post("/submit", {
            "task_id": "smoke_pair_new",
            "prompt": "first turn",
            "conversation_id": "",
        })
        conv_id = ack_new["conversation_id"]
        ack_cont = self._post("/continue", {
            "task_id": "smoke_pair_cont",
            "prompt": "follow-up",
            "conversation_id": conv_id,
        })
        self.assertEqual(ack_cont["status"], "queued")
        self.assertEqual(ack_cont["conversation_id"], conv_id)
        sess = self._get(f"/session/{conv_id}")
        self.assertEqual(sess["conversation_id"], conv_id)

    def test_phase_heartbeat_refreshes_active_task_status(self):
        oracle_server.task_queue.append({
            "task_id": "smoke_phase",
            "prompt": "first turn",
        })
        task = self._get("/task?agent=oracle_1")
        self.assertEqual(task["task_id"], "smoke_phase")
        oracle_server.dispatch_times["oracle_1"] = time.time() - 120
        oracle_server.active_start_times["oracle_1"] = time.time() - 120

        ack = self._post("/phase", {
            "task_id": "smoke_phase",
            "agent_id": "oracle_1",
            "phase": "waiting_response",
            "detail": "elapsed=60s; extracted=1200",
        })

        self.assertEqual(ack["status"], "ok")
        status = self._get("/task_status/smoke_phase")
        self.assertEqual(status["phase"], "waiting_response")
        self.assertEqual(status["detail"], "elapsed=60s; extracted=1200")
        self.assertGreaterEqual(status["elapsed"], 120)
        self.assertLess(status["last_activity_s"], 10)

    def test_phase_heartbeat_does_not_persist_queue_state_each_time(self):
        oracle_server.task_queue.append({
            "task_id": "smoke_phase_no_persist",
            "prompt": "first turn",
        })
        task = self._get("/task?agent=oracle_1")
        self.assertEqual(task["task_id"], "smoke_phase_no_persist")
        before = oracle_server.QUEUE_STATE_PATH.stat().st_mtime_ns

        time.sleep(0.01)
        ack = self._post("/phase", {
            "task_id": "smoke_phase_no_persist",
            "agent_id": "oracle_1",
            "phase": "response_observed",
            "detail": "elapsed=60s; extracted=1200",
        })

        self.assertEqual(ack["status"], "ok")
        after = oracle_server.QUEUE_STATE_PATH.stat().st_mtime_ns
        self.assertEqual(before, after)
        status = self._get("/task_status/smoke_phase_no_persist")
        self.assertEqual(status["phase"], "response_observed")
        self.assertLess(status["last_activity_s"], 10)

    def test_phase_heartbeat_does_not_reset_active_elapsed(self):
        oracle_server.task_queue.append({
            "task_id": "smoke_phase_elapsed",
            "prompt": "first turn",
        })
        task = self._get("/task?agent=oracle_1")
        self.assertEqual(task["task_id"], "smoke_phase_elapsed")
        oracle_server.active_start_times["oracle_1"] = time.time() - 7205
        oracle_server.dispatch_times["oracle_1"] = time.time() - 120

        self._post("/phase", {
            "task_id": "smoke_phase_elapsed",
            "agent_id": "oracle_1",
            "phase": "waiting_response",
            "detail": "elapsed=7205s; extracted=1200",
        })

        status = self._get("/task_status/smoke_phase_elapsed")
        self.assertGreaterEqual(status["elapsed"], 7200)
        self.assertLess(status["last_activity_s"], 10)

    def test_release_requeues_active_task_and_frees_agent(self):
        oracle_server.task_queue.append({
            "task_id": "smoke_release",
            "prompt": "first turn",
        })
        task = self._get("/task?agent=oracle_1")
        self.assertEqual(task["task_id"], "smoke_release")

        released = self._post("/release", {
            "task_id": "smoke_release",
            "agent_id": "oracle_1",
            "reason": "tab_not_foreground",
        })

        self.assertEqual(released["status"], "released")
        self.assertNotIn("oracle_1", oracle_server.pending_tasks)
        self.assertEqual(len(oracle_server.task_queue), 1)
        self.assertEqual(oracle_server.task_queue[0]["task_id"], "smoke_release")

    def test_close_marks_conversation_closed(self):
        ack_new = self._post("/submit", {
            "task_id": "smoke_close_new",
            "prompt": "first turn",
            "conversation_id": "",
        })
        conv_id = ack_new["conversation_id"]
        closed = self._post("/close", {"conversation_id": conv_id})
        self.assertEqual(closed["status"], "closed")
        sess = self._get(f"/session/{conv_id}")
        self.assertTrue(sess.get("closed_at"))

    def test_status_advertises_source_sha_when_set(self):
        # SOURCE_SHA is populated by main(); in tests we set it manually so we
        # can exercise drift detection on the supervisor side.
        oracle_server.SOURCE_SHA = "abc123def456"
        try:
            status = self._get("/status")
            self.assertEqual(status["source_sha"], "abc123def456")
        finally:
            oracle_server.SOURCE_SHA = ""


class PersistenceTests(unittest.TestCase):
    """Round-trip queue/results persistence so kill-9 doesn't drop work."""

    def setUp(self):
        # Use real on-disk files but isolate to a tmp path so we don't
        # clobber a real running server's state.
        import tempfile
        self.tmp = tempfile.mkdtemp(prefix="oracle_persist_")
        self._real_oracle_dir = oracle_server.ORACLE_DIR
        self._real_queue_path = oracle_server.QUEUE_STATE_PATH
        self._real_results_path = oracle_server.RESULTS_RING_PATH
        self._real_sessions_dir = oracle_server.SESSIONS_DIR
        oracle_server.ORACLE_DIR = Path(self.tmp)
        oracle_server.QUEUE_STATE_PATH = oracle_server.ORACLE_DIR / "queue_state.json"
        oracle_server.RESULTS_RING_PATH = oracle_server.ORACLE_DIR / "results_ring.json"
        oracle_server.SESSIONS_DIR = oracle_server.ORACLE_DIR / "sessions"
        oracle_server.task_queue.clear()
        oracle_server.results.clear()
        oracle_server.pending_tasks.clear()
        oracle_server.dispatch_times.clear()
        oracle_server.active_start_times.clear()

    def tearDown(self):
        import shutil
        oracle_server.ORACLE_DIR = self._real_oracle_dir
        oracle_server.QUEUE_STATE_PATH = self._real_queue_path
        oracle_server.RESULTS_RING_PATH = self._real_results_path
        oracle_server.SESSIONS_DIR = self._real_sessions_dir
        oracle_server.task_queue.clear()
        oracle_server.results.clear()
        oracle_server.pending_tasks.clear()
        oracle_server.dispatch_times.clear()
        oracle_server.active_start_times.clear()
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_queue_round_trip(self):
        oracle_server.task_queue.append({"task_id": "q1", "prompt": "x"})
        oracle_server.task_queue.append({"task_id": "q2", "prompt": "y"})
        oracle_server.pending_tasks["oracle_1"] = {"task_id": "p1", "prompt": "z"}
        oracle_server.dispatch_times["oracle_1"] = time.time()
        oracle_server._persist_queue_state()

        # Wipe in-memory state then hydrate.
        oracle_server.task_queue.clear()
        oracle_server.pending_tasks.clear()
        oracle_server.dispatch_times.clear()
        oracle_server.active_start_times.clear()
        oracle_server._hydrate_queue_state()

        self.assertEqual(len(oracle_server.task_queue), 2)
        self.assertIn("oracle_1", oracle_server.pending_tasks)

    def test_orphan_pending_requeues_on_hydrate(self):
        # Simulate a pending task whose dispatch is past the timeout: hydrate
        # should re-queue it instead of silently dropping it.
        old_ts = time.time() - oracle_server.TASK_TIMEOUT - 60
        oracle_server.pending_tasks["oracle_1"] = {"task_id": "stale", "prompt": "x"}
        oracle_server.dispatch_times["oracle_1"] = old_ts
        oracle_server._persist_queue_state()

        oracle_server.task_queue.clear()
        oracle_server.pending_tasks.clear()
        oracle_server.dispatch_times.clear()
        oracle_server.active_start_times.clear()
        oracle_server._hydrate_queue_state()

        self.assertEqual(len(oracle_server.task_queue), 1)
        self.assertEqual(oracle_server.task_queue[0]["task_id"], "stale")
        self.assertNotIn("oracle_1", oracle_server.pending_tasks)

    def test_results_ring_round_trip(self):
        oracle_server.results["t1"] = {"task_id": "t1", "response": "r1", "timestamp": "2026-01-01T00:00:00+00:00"}
        oracle_server.results["t2"] = {"task_id": "t2", "response": "r2", "timestamp": "2026-01-02T00:00:00+00:00"}
        oracle_server._persist_results_ring()

        oracle_server.results.clear()
        oracle_server._hydrate_results_ring()

        self.assertEqual(len(oracle_server.results), 2)
        self.assertEqual(oracle_server.results["t2"]["response"], "r2")


class DriftDetectionTests(unittest.TestCase):
    def test_disk_source_sha_matches_compute(self):
        """supervisor.disk_source_sha and server._compute_source_sha should agree."""
        # We can't test the live server's SOURCE_SHA without booting one,
        # but the helpers must produce the same digest for the same file.
        from_supervisor = pipeline_supervisor.disk_source_sha(
            pipeline_supervisor.ORACLE_SERVER_SCRIPT
        )
        # _compute_source_sha hashes oracle_server.py (its own __file__).
        from_server = oracle_server._compute_source_sha()
        self.assertTrue(from_supervisor)
        self.assertEqual(from_supervisor, from_server)

    def test_supervisor_drift_logs_when_disk_changes(self):
        emitted = []

        with mock.patch.object(pipeline_supervisor, "disk_source_sha",
                               return_value="disk-new"), \
             mock.patch.object(pipeline_supervisor, "_now",
                               return_value=2_000.0), \
             mock.patch.object(pipeline_supervisor, "supervisor_log",
                               side_effect=emitted.append):
            last_alert = pipeline_supervisor.maybe_log_supervisor_drift(
                running_sha="running-old",
                last_alert_ts=0.0,
            )

        self.assertEqual(last_alert, 2_000.0)
        self.assertEqual(len(emitted), 1)
        self.assertIn("DRIFT: pipeline_supervisor.py on disk", emitted[0])
        self.assertIn("restart supervisor", emitted[0])

    def test_supervisor_drift_debounces_recent_alert(self):
        emitted = []

        with mock.patch.object(pipeline_supervisor, "disk_source_sha",
                               return_value="disk-new"), \
             mock.patch.object(pipeline_supervisor, "_now",
                               return_value=2_000.0), \
             mock.patch.object(pipeline_supervisor, "supervisor_log",
                               side_effect=emitted.append):
            last_alert = pipeline_supervisor.maybe_log_supervisor_drift(
                running_sha="running-old",
                last_alert_ts=1_500.0,
            )

        self.assertEqual(last_alert, 1_500.0)
        self.assertEqual(emitted, [])


class PIReviewTests(unittest.TestCase):
    def test_pi_review_dry_run_produces_record(self):
        import pi_review
        record = pi_review.run_pi_review(dry_run=True)
        self.assertIn(record["status"], {"ok", "codex_failed", "claude_failed"})
        self.assertIn("captured_at", record)
        # Dry run does not call the CLIs but still synthesizes verdicts.
        if record["status"] == "ok":
            self.assertEqual(record["codex_verdict"]["loop_health"], "healthy")

    def test_evidence_payload_collects_states_and_log(self):
        import pi_review
        evidence = pi_review._evidence_payload()
        self.assertIn("captured_at", evidence)
        self.assertIn("pipeline_states", evidence)
        self.assertIn("recent_supervisor_log", evidence)
        self.assertIsInstance(evidence["pipeline_states"], list)

    def test_safe_json_handles_fenced_response(self):
        import pi_review
        fenced = '```json\n{"loop_health":"healthy","summary":"ok"}\n```'
        parsed = pi_review._safe_json(fenced)
        self.assertEqual(parsed["loop_health"], "healthy")

    def test_safe_json_returns_empty_on_garbage(self):
        import pi_review
        self.assertEqual(pi_review._safe_json("no json here"), {})
        self.assertEqual(pi_review._safe_json(""), {})


if __name__ == "__main__":
    unittest.main()
