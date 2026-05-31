"""Tests for the read-only pipeline health summarizer."""

from __future__ import annotations

import sys
import tempfile
import unittest
import json
from pathlib import Path

SCRIPT_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_ROOT))

import pipeline_health  # noqa: E402


class PipelineHealthTests(unittest.TestCase):
    def test_parse_manual_submission_queue(self):
        board_text = """
## 手动投稿队列 (2026-05-10 快照)

| 论文 | 目标期刊 | 备注 |
|------|---------|------|
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | Journal of Spectral Theory | C-DONE round 4: needs cover letter + metadata |

## 全量状态表
"""

        queue = pipeline_health.parse_manual_submission_queue(board_text)

        self.assertEqual(len(queue), 1)
        self.assertEqual(
            queue[0]["paper"],
            "2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst",
        )
        self.assertEqual(queue[0]["journal"], "Journal of Spectral Theory")

    def test_parse_ready_submission_entries_from_board(self):
        board_text = """
## 手动投稿队列 (2026-05-10 快照)

| 论文 | 目标期刊 | 备注 |
|------|---------|------|
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | Journal of Spectral Theory | C-DONE round 4 |

## 全量状态表

| 目录 | 目标期刊 | 状态 | 改投记录 |
|------|---------|------|---------|
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | J. Spectral Theory | C-DONE round 4: Oracle accept + Codex submit | synced |
| `2026_scan_error_prefix_partitions_convergence_rates_etds` | ETDS | ✅ 可投稿 — C-8 (Oracle accept + Claude submit) | needs metadata |
| `2026_done` | ETDS | 已投 05-10 | done |
"""

        ready = pipeline_health.parse_ready_submission_entries(board_text)

        self.assertEqual(
            [item["paper"] for item in ready],
            [
                "2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst",
                "2026_scan_error_prefix_partitions_convergence_rates_etds",
            ],
        )
        self.assertEqual(ready[1]["journal"], "ETDS")

    def test_board_parsers_do_not_require_chinese_section_titles(self):
        board_text = """
## Queue

| paper | journal | note |
|------|---------|------|
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | Journal of Spectral Theory | C-DONE round 4 |

## Status

| dir | journal | status | note |
|------|---------|------|---------|
| `2026_scan_error_prefix_partitions_convergence_rates_etds` | ETDS | ✅ 可投稿 — C-8 | needs metadata |
"""

        manual = pipeline_health.parse_manual_submission_queue(board_text)
        ready = pipeline_health.parse_ready_submission_entries(board_text)

        self.assertEqual(
            manual[0]["paper"],
            "2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst",
        )
        self.assertEqual(
            ready[0]["paper"],
            "2026_scan_error_prefix_partitions_convergence_rates_etds",
        )

    def test_latest_supervisor_start_ts_uses_newest_start_line(self):
        lines = [
            "[2026-05-13T22:48:34+00:00] supervisor starting (branch=x)",
            "[2026-05-13T22:48:41+00:00] no runnable papers",
            "[2026-05-13T22:50:26+00:00] supervisor starting (branch=x)",
        ]

        ts = pipeline_health.latest_supervisor_start_ts(lines)

        self.assertEqual(
            ts,
            pipeline_health._parse_iso_ts("2026-05-13T22:50:26+00:00"),
        )

    def test_latest_supervisor_exit_ts_uses_newest_exit_line(self):
        lines = [
            "[2026-05-13T22:48:34+00:00] supervisor exiting",
            "[2026-05-13T22:50:26+00:00] supervisor starting (branch=x)",
            "[2026-05-13T22:52:26+00:00] supervisor exiting",
        ]

        ts = pipeline_health.latest_supervisor_exit_ts(lines)

        self.assertEqual(
            ts,
            pipeline_health._parse_iso_ts("2026-05-13T22:52:26+00:00"),
        )

    def test_latest_supervisor_tick_estimate_uses_start_poll_and_last_log_line(self):
        lines = [
            "[2026-05-14T09:38:41+00:00] supervisor starting "
            "(branch=x poll=300s server_spawn=on)",
            "[2026-05-14T09:38:47+00:00] no runnable papers "
            "(diagnosis=gate_exhausted; candidates=43; runnable=0)",
            "[2026-05-14T09:38:47+00:00] refill disabled: "
            "--refill-project-url not set; backlog drained",
        ]

        self.assertEqual(pipeline_health.latest_supervisor_poll_s(lines), 300)
        self.assertEqual(
            pipeline_health.latest_supervisor_log_ts(lines),
            pipeline_health._parse_iso_ts("2026-05-14T09:38:47+00:00"),
        )

    def test_categorize_skipped_status_entries_summarizes_gate_exhaustion(self):
        entries = [
            "  2026_a: 已投 05-10",
            "  submitted_2026_b: 归档；submitted legacy route；不处理",
            "  2026_c: A-BLOCKED (overlap needs_human_resolution before Stage A)",
            "  2026_d: A-BLOCKED (overlap deferred; wait for prior submitted sibling feedback)",
            "  2026_e: C-STUCK (Oracle+Claude exhausted 15 rounds)",
            "  2026_f: A-BLOCKED (A2 fake extension: no new theorems)",
            "  2026_g: ✅ 可投稿 — C-8 (Oracle accept + Claude submit)",
            "  2026_h: C-DONE round 4: Oracle accept + Codex submit; needs cover letter",
            "  2026_i: A-BLOCKED (max Stage A rounds exhausted; final audit real block)",
        ]

        counts = pipeline_health.categorize_skipped_status_entries(entries)

        self.assertEqual(counts["submitted"], 1)
        self.assertEqual(counts["archive_or_parked"], 1)
        self.assertEqual(counts["overlap_needs_human_resolution"], 1)
        self.assertEqual(counts["overlap_deferred"], 1)
        self.assertEqual(counts["stuck_needs_review"], 1)
        self.assertEqual(counts["fake_extension"], 1)
        self.assertEqual(counts["publication_ready"], 2)
        self.assertEqual(counts["stage_a_blocked_other"], 1)

    def test_ready_not_in_manual_queue_is_reported(self):
        report = pipeline_health.build_health_report(
            oracle_status={
                "diagnosis": "idle",
                "queue_length": 0,
                "agents_busy": 0,
                "max_agents": 3,
            },
            discovery_summary={
                "diagnosis": "gate_exhausted",
                "candidate_count": 43,
                "runnable_count": 0,
                "skipped_status_count": 43,
            },
            supervisor_tail=[],
            now_ts=1_000.0,
            supervisor_log_mtime=995.0,
            refill_queue_exists=False,
            refill_project_url="",
            manual_submission_queue=[
                {
                    "paper": "2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst",
                    "journal": "Journal of Spectral Theory",
                    "note": "C-DONE round 4",
                }
            ],
            ready_submission_entries=[
                {
                    "paper": "2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst",
                    "journal": "J. Spectral Theory",
                    "status": "C-DONE round 4",
                    "note": "synced",
                },
                {
                    "paper": "2026_scan_error_prefix_partitions_convergence_rates_etds",
                    "journal": "ETDS",
                    "status": "✅ 可投稿 — C-8",
                    "note": "needs metadata",
                },
            ],
            supervisor_code_mtime=700.0,
            supervisor_started_ts=800.0,
            supervisor_exited_ts=0.0,
            supervisor_last_log_ts=800.0,
            supervisor_poll_s=300,
            supervisor_pid=2464,
            supervisor_pid_started_ts=800.0,
            supervisor_pid_script="pipeline_supervisor.py",
            supervisor_pid_alive=True,
        )

        self.assertEqual(report["health"], "attention")
        self.assertEqual(report["reason"], "ready_not_in_manual_queue")
        self.assertEqual(report["ready_not_in_manual_count"], 1)
        self.assertEqual(
            report["ready_not_in_manual_queue"][0]["paper"],
            "2026_scan_error_prefix_partitions_convergence_rates_etds",
        )
        self.assertTrue(
            any("ready not in manual queue" in action for action in report["actions"])
        )
        self.assertTrue(
            any(
                "triage ready-not-manual" in action
                and "add to manual queue" in action
                and "mark submitted" in action
                and "park explicitly" in action
                for action in report["actions"]
            )
        )

    def test_exit_code_for_report_treats_ready_not_manual_as_attention(self):
        report = {
            "health": "healthy_idle",
            "ready_not_in_manual_count": 1,
        }

        self.assertEqual(pipeline_health.exit_code_for_report(report), 1)

    def test_exit_code_for_report_keeps_blocked_above_ready_not_manual(self):
        report = {
            "health": "blocked",
            "ready_not_in_manual_count": 1,
        }

        self.assertEqual(pipeline_health.exit_code_for_report(report), 2)

    def test_read_supervisor_pid_record_supports_json_metadata(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / ".pipeline_supervisor.pid"
            path.write_text(
                '{"pid": 21976, "started_ts": 1778742027.0, "script": "pipeline_supervisor.py"}\n',
                encoding="utf-8",
            )

            record = pipeline_health.read_supervisor_pid_record(path)

        self.assertEqual(record["pid"], 21976)
        self.assertEqual(record["started_ts"], 1778742027.0)
        self.assertEqual(record["script"], "pipeline_supervisor.py")

    def test_read_supervisor_pid_record_supports_legacy_integer(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / ".pipeline_supervisor.pid"
            path.write_text("21976\n", encoding="utf-8")

            record = pipeline_health.read_supervisor_pid_record(path)

        self.assertEqual(record["pid"], 21976)
        self.assertIsNone(record["started_ts"])

    def test_classifies_supervisor_code_drift_as_attention(self):
        report = pipeline_health.build_health_report(
            oracle_status={
                "diagnosis": "idle",
                "queue_length": 0,
                "agents_busy": 0,
                "max_agents": 3,
            },
            discovery_summary={
                "diagnosis": "gate_exhausted",
                "candidate_count": 43,
                "runnable_count": 0,
                "skipped_status_count": 43,
                "skipped_done_count": 0,
                "skipped_unregistered_count": 0,
                "skipped_assignment_count": 0,
                "skipped_status": [
                    "2026_a: 已投 05-10",
                    "2026_b: A-BLOCKED (overlap deferred; wait for prior submitted sibling feedback)",
                ],
            },
            supervisor_tail=[
                "[2026-05-14T06:15:32+00:00] no runnable papers "
                "(diagnosis=gate_exhausted; candidates=43; runnable=0)",
            ],
            now_ts=1_000.0,
            supervisor_log_mtime=995.0,
            refill_queue_exists=False,
            refill_project_url="",
            manual_submission_queue=[
                {
                    "paper": "2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst",
                    "journal": "Journal of Spectral Theory",
                    "note": "C-DONE round 4: needs cover letter + metadata",
                }
            ],
            supervisor_code_mtime=900.0,
            supervisor_started_ts=800.0,
            supervisor_exited_ts=0.0,
            supervisor_last_log_ts=800.0,
            supervisor_poll_s=300,
            supervisor_pid=2464,
            supervisor_pid_started_ts=800.0,
            supervisor_pid_script="pipeline_supervisor.py",
            supervisor_pid_alive=True,
        )

        self.assertEqual(report["health"], "attention")
        self.assertEqual(report["reason"], "supervisor_code_changed")
        self.assertTrue(
            any("restart supervisor" in action for action in report["actions"])
        )

    def test_gate_exhausted_without_code_drift_is_healthy_idle(self):
        report = pipeline_health.build_health_report(
            oracle_status={
                "diagnosis": "idle",
                "queue_length": 0,
                "agents_busy": 0,
                "max_agents": 3,
            },
            discovery_summary={
                "diagnosis": "gate_exhausted",
                "candidate_count": 43,
                "runnable_count": 0,
                "skipped_status_count": 43,
                "skipped_done_count": 0,
                "skipped_unregistered_count": 0,
                "skipped_assignment_count": 0,
                "skipped_status": [
                    "2026_a: 已投 05-10",
                    "2026_b: A-BLOCKED (overlap deferred; wait for prior submitted sibling feedback)",
                ],
            },
            supervisor_tail=[
                "[2026-05-14T06:15:32+00:00] no runnable papers "
                "(diagnosis=gate_exhausted; candidates=43; runnable=0)",
            ],
            now_ts=1_000.0,
            supervisor_log_mtime=995.0,
            refill_queue_exists=False,
            refill_project_url="",
            manual_submission_queue=[
                {
                    "paper": "2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst",
                    "journal": "Journal of Spectral Theory",
                    "note": "C-DONE round 4: needs cover letter + metadata",
                }
            ],
            supervisor_code_mtime=700.0,
            supervisor_started_ts=800.0,
            supervisor_exited_ts=0.0,
            supervisor_last_log_ts=800.0,
            supervisor_poll_s=300,
            supervisor_pid=2464,
            supervisor_pid_started_ts=800.0,
            supervisor_pid_script="pipeline_supervisor.py",
            supervisor_pid_alive=True,
        )

        self.assertEqual(report["health"], "healthy_idle")
        self.assertEqual(report["reason"], "gate_exhausted")
        self.assertEqual(report["manual_submission_count"], 1)
        self.assertEqual(report["discovery"]["skip_categories"]["submitted"], 1)
        self.assertEqual(report["discovery"]["skip_categories"]["overlap_deferred"], 1)
        self.assertTrue(
            any("refill local-context producer" in action for action in report["actions"])
        )
        self.assertTrue(
            any("manual submission candidate" in action for action in report["actions"])
        )

    def test_report_includes_oracle_activity_counters(self):
        report = pipeline_health.build_health_report(
            oracle_status={
                "diagnosis": "idle",
                "queue_length": 0,
                "queued": [],
                "queued_tasks": [],
                "agents": {"oracle_1": {}, "oracle_2": {}},
                "active_recent_agents": ["oracle_1"],
                "completed": 200,
                "active_sessions": 128,
            },
            discovery_summary={
                "diagnosis": "gate_exhausted",
                "candidate_count": 43,
                "runnable_count": 0,
                "skipped_status_count": 43,
            },
            supervisor_tail=[
                "[2026-05-14T08:18:47+00:00] refill disabled: "
                "--refill-project-url not set; backlog drained",
            ],
            now_ts=1_000.0,
            supervisor_log_mtime=995.0,
            refill_queue_exists=False,
            refill_project_url="",
            manual_submission_queue=[],
            supervisor_code_mtime=700.0,
            supervisor_started_ts=800.0,
            supervisor_exited_ts=0.0,
            supervisor_last_log_ts=800.0,
            supervisor_poll_s=300,
            supervisor_pid=2464,
            supervisor_pid_started_ts=800.0,
            supervisor_pid_script="pipeline_supervisor.py",
            supervisor_pid_alive=True,
        )

        self.assertEqual(report["oracle"]["completed"], 200)
        self.assertEqual(report["oracle"]["active_sessions"], 128)
        self.assertEqual(report["oracle"]["queued_count"], 0)
        self.assertEqual(report["oracle"]["queued_tasks_count"], 0)
        self.assertEqual(report["oracle"]["registered_agents"], 2)
        self.assertEqual(report["oracle"]["active_recent_agents"], 1)

    def test_report_uses_server_registered_agent_count_when_idle(self):
        report = pipeline_health.build_health_report(
            oracle_status={
                "diagnosis": "idle",
                "queue_length": 0,
                "queued": [],
                "queued_tasks": [],
                "agents": {},
                "idle_agents": {
                    "oracle_1": {"state": "idle", "last_poll_s": 10},
                    "oracle_2": {"state": "idle", "last_poll_s": 400},
                },
                "registered_agents": 2,
                "active_recent_agents": ["oracle_1"],
                "completed": 200,
                "active_sessions": 128,
            },
            discovery_summary={
                "diagnosis": "gate_exhausted",
                "candidate_count": 43,
                "runnable_count": 0,
                "skipped_status_count": 43,
            },
            supervisor_tail=[
                "[2026-05-14T08:18:47+00:00] refill disabled: "
                "--refill-project-url not set; backlog drained",
            ],
            now_ts=1_000.0,
            supervisor_log_mtime=995.0,
            refill_queue_exists=False,
            refill_project_url="",
            manual_submission_queue=[],
            supervisor_code_mtime=700.0,
            supervisor_started_ts=800.0,
            supervisor_exited_ts=0.0,
            supervisor_last_log_ts=800.0,
            supervisor_poll_s=300,
            supervisor_pid=2464,
            supervisor_pid_started_ts=800.0,
            supervisor_pid_script="pipeline_supervisor.py",
            supervisor_pid_alive=True,
        )

        self.assertEqual(report["oracle"]["registered_agents"], 2)
        self.assertEqual(report["oracle"]["active_recent_agents"], 1)

    def test_classifies_stale_supervisor_log(self):
        report = pipeline_health.build_health_report(
            oracle_status={"diagnosis": "idle", "queue_length": 0},
            discovery_summary={
                "diagnosis": "gate_exhausted",
                "candidate_count": 43,
                "runnable_count": 0,
                "skipped_status_count": 43,
            },
            supervisor_tail=[],
            now_ts=10_000.0,
            supervisor_log_mtime=1_000.0,
            refill_queue_exists=False,
            refill_project_url="",
            manual_submission_queue=[],
            supervisor_code_mtime=0.0,
            supervisor_started_ts=0.0,
            supervisor_exited_ts=0.0,
            supervisor_last_log_ts=0.0,
            supervisor_poll_s=0,
            supervisor_pid=None,
            supervisor_pid_started_ts=None,
            supervisor_pid_script="",
            supervisor_pid_alive=True,
        )

        self.assertEqual(report["health"], "attention")
        self.assertEqual(report["reason"], "supervisor_log_stale")

    def test_classifies_oracle_down(self):
        report = pipeline_health.build_health_report(
            oracle_status={},
            discovery_summary={"diagnosis": "gate_exhausted"},
            supervisor_tail=[],
            now_ts=1_000.0,
            supervisor_log_mtime=999.0,
            refill_queue_exists=False,
            refill_project_url="",
            manual_submission_queue=[],
            supervisor_code_mtime=0.0,
            supervisor_started_ts=0.0,
            supervisor_exited_ts=0.0,
            supervisor_last_log_ts=0.0,
            supervisor_poll_s=0,
            supervisor_pid=None,
            supervisor_pid_started_ts=None,
            supervisor_pid_script="",
            supervisor_pid_alive=True,
        )

        self.assertEqual(report["health"], "blocked")
        self.assertEqual(report["reason"], "oracle_down")

    def test_classifies_missing_supervisor_process_as_attention(self):
        report = pipeline_health.build_health_report(
            oracle_status={"diagnosis": "idle", "queue_length": 0},
            discovery_summary={
                "diagnosis": "gate_exhausted",
                "candidate_count": 43,
                "runnable_count": 0,
                "skipped_status_count": 43,
            },
            supervisor_tail=[
                "[2026-05-14T06:45:08+00:00] refill disabled: "
                "--refill-project-url not set; backlog drained",
            ],
            now_ts=1_000.0,
            supervisor_log_mtime=995.0,
            refill_queue_exists=False,
            refill_project_url="",
            manual_submission_queue=[],
            supervisor_code_mtime=700.0,
            supervisor_started_ts=800.0,
            supervisor_exited_ts=0.0,
            supervisor_last_log_ts=800.0,
            supervisor_poll_s=300,
            supervisor_pid=2464,
            supervisor_pid_started_ts=800.0,
            supervisor_pid_script="pipeline_supervisor.py",
            supervisor_pid_alive=False,
        )

        self.assertEqual(report["health"], "attention")
        self.assertEqual(report["reason"], "supervisor_process_dead")
        self.assertEqual(report["supervisor"]["pid"], 2464)
        self.assertFalse(report["supervisor"]["pid_alive"])
        self.assertTrue(
            any("restart pipeline_supervisor.py" in action for action in report["actions"])
        )

    def test_classifies_missing_supervisor_pid_record_as_attention(self):
        report = pipeline_health.build_health_report(
            oracle_status={"diagnosis": "idle", "queue_length": 0},
            discovery_summary={
                "diagnosis": "gate_exhausted",
                "candidate_count": 43,
                "runnable_count": 0,
                "skipped_status_count": 43,
            },
            supervisor_tail=[
                "[2026-05-14T07:21:16+00:00] refill disabled: "
                "--refill-project-url not set; backlog drained",
            ],
            now_ts=1_000.0,
            supervisor_log_mtime=995.0,
            refill_queue_exists=False,
            refill_project_url="",
            manual_submission_queue=[],
            supervisor_code_mtime=700.0,
            supervisor_started_ts=900.0,
            supervisor_exited_ts=0.0,
            supervisor_last_log_ts=900.0,
            supervisor_poll_s=300,
            supervisor_pid=None,
            supervisor_pid_started_ts=None,
            supervisor_pid_script="",
            supervisor_pid_alive=False,
        )

        self.assertEqual(report["health"], "attention")
        self.assertEqual(report["reason"], "supervisor_pid_missing")

    def test_classifies_stale_supervisor_pid_record_as_attention(self):
        report = pipeline_health.build_health_report(
            oracle_status={"diagnosis": "idle", "queue_length": 0},
            discovery_summary={
                "diagnosis": "gate_exhausted",
                "candidate_count": 43,
                "runnable_count": 0,
                "skipped_status_count": 43,
            },
            supervisor_tail=[
                "[2026-05-14T07:00:34+00:00] refill disabled: "
                "--refill-project-url not set; backlog drained",
            ],
            now_ts=1_000.0,
            supervisor_log_mtime=995.0,
            refill_queue_exists=False,
            refill_project_url="",
            manual_submission_queue=[],
            supervisor_code_mtime=700.0,
            supervisor_started_ts=900.0,
            supervisor_exited_ts=0.0,
            supervisor_last_log_ts=900.0,
            supervisor_poll_s=300,
            supervisor_pid=2464,
            supervisor_pid_started_ts=800.0,
            supervisor_pid_script="pipeline_supervisor.py",
            supervisor_pid_alive=True,
        )

        self.assertEqual(report["health"], "attention")
        self.assertEqual(report["reason"], "supervisor_pid_stale")
        self.assertTrue(
            any("restart pipeline_supervisor.py" in action for action in report["actions"])
        )

    def test_classifies_supervisor_pid_script_mismatch_as_attention(self):
        report = pipeline_health.build_health_report(
            oracle_status={"diagnosis": "idle", "queue_length": 0},
            discovery_summary={
                "diagnosis": "gate_exhausted",
                "candidate_count": 43,
                "runnable_count": 0,
                "skipped_status_count": 43,
            },
            supervisor_tail=[
                "[2026-05-14T07:00:34+00:00] refill disabled: "
                "--refill-project-url not set; backlog drained",
            ],
            now_ts=1_000.0,
            supervisor_log_mtime=995.0,
            refill_queue_exists=False,
            refill_project_url="",
            manual_submission_queue=[],
            supervisor_code_mtime=700.0,
            supervisor_started_ts=900.0,
            supervisor_exited_ts=0.0,
            supervisor_last_log_ts=900.0,
            supervisor_poll_s=300,
            supervisor_pid=2464,
            supervisor_pid_started_ts=900.0,
            supervisor_pid_script="oracle_server.py",
            supervisor_pid_alive=True,
        )

        self.assertEqual(report["health"], "attention")
        self.assertEqual(report["reason"], "supervisor_pid_script_mismatch")
        self.assertTrue(
            any("restart pipeline_supervisor.py" in action for action in report["actions"])
        )

    def test_windows_process_alive_uses_get_process_when_kill_zero_denied(self):
        calls: list[list[str]] = []

        def fake_run(cmd, **kwargs):
            calls.append(cmd)

            class Result:
                returncode = 0
                stdout = "python\n"

            return Result()

        alive = pipeline_health.process_alive(
            21976,
            platform="win32",
            run=fake_run,
        )

        self.assertTrue(alive)
        self.assertEqual(calls[0][:3], ["powershell", "-NoProfile", "-Command"])
        self.assertIn("Get-Process -Id 21976", calls[0][3])

    def test_text_report_includes_supervisor_pid_liveness(self):
        report = {
            "health": "healthy_idle",
            "reason": "gate_exhausted",
            "oracle": {
                "diagnosis": "idle",
                "queue_length": 0,
                "agents_busy": 0,
                "max_agents": 3,
            },
            "discovery": {
                "diagnosis": "gate_exhausted",
                "candidates": 43,
                "runnable": 0,
                "status_skipped": 43,
                "skip_categories": {"publication_ready": 2, "overlap_deferred": 3},
            },
            "supervisor": {
                "log_age_s": 54,
                "pid": 21976,
                "pid_alive": True,
                "pid_started_ts": 1778742027.0,
                "pid_script": "pipeline_supervisor.py",
                "code_changed_since_start": False,
                "next_tick_eta_s": 42,
            },
            "manual_submission_count": 0,
            "manual_submission_queue": [],
            "actions": [],
        }

        text = pipeline_health.format_text_report(report)

        self.assertIn("supervisor_pid=21976 alive=true", text)
        self.assertIn("script=pipeline_supervisor.py", text)
        self.assertIn("supervisor_next_tick_eta_s=42", text)
        self.assertIn("skip_categories=overlap_deferred=3 publication_ready=2", text)

    def test_classifies_latest_supervisor_exit_as_attention(self):
        report = pipeline_health.build_health_report(
            oracle_status={"diagnosis": "idle", "queue_length": 0},
            discovery_summary={
                "diagnosis": "gate_exhausted",
                "candidate_count": 43,
                "runnable_count": 0,
                "skipped_status_count": 43,
            },
            supervisor_tail=[
                "[2026-05-14T06:43:31+00:00] supervisor exiting",
            ],
            now_ts=1_000.0,
            supervisor_log_mtime=995.0,
            refill_queue_exists=False,
            refill_project_url="",
            manual_submission_queue=[],
            supervisor_code_mtime=700.0,
            supervisor_started_ts=800.0,
            supervisor_exited_ts=900.0,
            supervisor_last_log_ts=900.0,
            supervisor_poll_s=300,
            supervisor_pid=None,
            supervisor_pid_started_ts=None,
            supervisor_pid_script="",
            supervisor_pid_alive=False,
        )

        self.assertEqual(report["health"], "attention")
        self.assertEqual(report["reason"], "supervisor_not_running")

    def test_exit_code_for_report_supports_check_mode(self):
        self.assertEqual(pipeline_health.exit_code_for_report(
            {"health": "healthy_idle"}), 0)
        self.assertEqual(pipeline_health.exit_code_for_report(
            {"health": "running_or_ready"}), 0)
        self.assertEqual(pipeline_health.exit_code_for_report(
            {"health": "attention"}), 1)
        self.assertEqual(pipeline_health.exit_code_for_report(
            {"health": "blocked"}), 2)

    def test_append_health_snapshot_writes_jsonl(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "health.jsonl"
            pipeline_health.append_health_snapshot(
                {
                    "health": "healthy_idle",
                    "reason": "gate_exhausted",
                    "oracle": {"diagnosis": "idle"},
                },
                path=path,
            )
            pipeline_health.append_health_snapshot(
                {
                    "health": "attention",
                    "reason": "supervisor_log_stale",
                    "oracle": {"diagnosis": "idle"},
                },
                path=path,
            )

            lines = path.read_text(encoding="utf-8").splitlines()

        self.assertEqual(len(lines), 2)
        first = json.loads(lines[0])
        second = json.loads(lines[1])
        self.assertEqual(first["health"], "healthy_idle")
        self.assertEqual(second["reason"], "supervisor_log_stale")
        self.assertIn("captured_ts", first)
        self.assertIn("captured_iso", first)

    def test_read_health_snapshots_returns_recent_valid_records(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "health.jsonl"
            path.write_text(
                "\n".join([
                    '{"captured_iso": "2026-05-14T08:00:00+00:00", "health": "attention", "reason": "old"}',
                    "not json",
                    '{"captured_iso": "2026-05-14T08:05:00+00:00", "health": "healthy_idle", "reason": "gate_exhausted"}',
                    '{"captured_iso": "2026-05-14T08:10:00+00:00", "health": "healthy_idle", "reason": "gate_exhausted"}',
                ]),
                encoding="utf-8",
            )

            snapshots = pipeline_health.read_health_snapshots(path=path, limit=2)

        self.assertEqual(len(snapshots), 2)
        self.assertEqual(snapshots[0]["captured_iso"], "2026-05-14T08:05:00+00:00")
        self.assertEqual(snapshots[1]["captured_iso"], "2026-05-14T08:10:00+00:00")

    def test_format_history_report_summarizes_health_trend(self):
        text = pipeline_health.format_history_report([
            {
                "captured_iso": "2026-05-14T08:05:00+00:00",
                "health": "healthy_idle",
                "reason": "gate_exhausted",
                "oracle": {"queue_length": 0, "agents_busy": 0},
                "discovery": {"runnable": 0},
                "supervisor": {"log_age_s": 33},
            },
            {
                "captured_iso": "2026-05-14T08:10:00+00:00",
                "health": "attention",
                "reason": "supervisor_log_stale",
                "oracle": {"queue_length": 0, "agents_busy": 0},
                "discovery": {"runnable": 0},
                "supervisor": {"log_age_s": 901},
            },
        ])

        self.assertIn("history_count=2", text)
        self.assertIn("healthy_idle=1", text)
        self.assertIn("attention=1", text)
        self.assertIn("reason_counts=gate_exhausted=1 supervisor_log_stale=1", text)
        self.assertIn("latest=2026-05-14T08:10:00+00:00 attention/supervisor_log_stale", text)

    def test_format_history_report_can_show_latest_snapshot_age(self):
        text = pipeline_health.format_history_report(
            [
                {
                    "captured_ts": 100.0,
                    "captured_iso": "2026-05-14T08:10:00+00:00",
                    "health": "healthy_idle",
                    "reason": "gate_exhausted",
                "oracle": {"queue_length": 0, "agents_busy": 0},
                "discovery": {"runnable": 0},
                "supervisor": {"log_age_s": 24, "next_tick_eta_s": 276},
                "ready_not_in_manual_count": 1,
            },
        ],
            now_ts=145.6,
        )

        self.assertIn("latest_age_s=45", text)
        self.assertIn("next_tick_eta_s=276", text)
        self.assertIn("ready_not_manual=1", text)

    def test_exit_code_for_history_uses_latest_snapshot(self):
        snapshots = [
            {"health": "healthy_idle"},
            {"health": "attention"},
        ]

        self.assertEqual(pipeline_health.exit_code_for_history(snapshots), 1)
        self.assertEqual(
            pipeline_health.exit_code_for_history([{"health": "blocked"}]),
            2,
        )
        self.assertEqual(
            pipeline_health.exit_code_for_history([{"health": "healthy_idle"}]),
            0,
        )
        self.assertEqual(pipeline_health.exit_code_for_history([]), 1)

    def test_exit_code_for_history_keeps_blocked_above_ready_not_manual(self):
        snapshots = [
            {
                "health": "blocked",
                "ready_not_in_manual_count": 1,
            },
        ]

        self.assertEqual(pipeline_health.exit_code_for_history(snapshots), 2)

    def test_exit_code_for_history_can_require_fresh_latest_snapshot(self):
        snapshots = [
            {
                "health": "healthy_idle",
                "captured_ts": 100.0,
            },
        ]

        self.assertEqual(
            pipeline_health.exit_code_for_history(
                snapshots,
                now_ts=200.0,
                max_age_s=120,
            ),
            0,
        )
        self.assertEqual(
            pipeline_health.exit_code_for_history(
                snapshots,
                now_ts=250.0,
                max_age_s=120,
            ),
            1,
        )

    def test_build_current_report_uses_runtime_readers(self):
        report = pipeline_health.build_current_report(
            oracle_status_reader=lambda: {"diagnosis": "idle", "queue_length": 0},
            discovery_reader=lambda: {
                "diagnosis": "gate_exhausted",
                "candidate_count": 43,
                "runnable_count": 0,
                "skipped_status_count": 43,
            },
            supervisor_log_reader=lambda: [
                "[2026-05-14T08:18:47+00:00] supervisor starting",
                "[2026-05-14T08:18:47+00:00] refill disabled: "
                "--refill-project-url not set; backlog drained",
            ],
            now_ts=1_000.0,
            supervisor_log_mtime_reader=lambda: 995.0,
            refill_queue_exists_reader=lambda: False,
            manual_submission_reader=lambda: [],
            ready_submission_reader=lambda: [],
            supervisor_code_mtime_reader=lambda: 900.0,
            supervisor_pid_record_reader=lambda: {
                "pid": 2464,
                "started_ts": pipeline_health._parse_iso_ts("2026-05-14T08:18:47+00:00"),
                "script": "pipeline_supervisor.py",
            },
            process_alive_reader=lambda pid: True,
            refill_project_url="",
        )

        self.assertEqual(report["health"], "healthy_idle")
        self.assertEqual(report["reason"], "gate_exhausted")
        self.assertEqual(report["supervisor"]["pid"], 2464)


if __name__ == "__main__":
    unittest.main()
