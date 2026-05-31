import unittest

import pipeline_health


class PipelineHealthTests(unittest.TestCase):
    def base_kwargs(self):
        now_ts = 100_000.0
        return {
            "oracle_status": {
                "diagnosis": "idle",
                "queue_length": 0,
                "agents_busy": 0,
                "max_agents": 5,
            },
            "discovery_summary": {
                "diagnosis": "ok",
                "candidate_count": 10,
                "runnable_count": 1,
                "skipped_status_count": 0,
            },
            "supervisor_tail": ["[1970-01-01T00:00:00+00:00] old supervisor line"],
            "now_ts": now_ts,
            "supervisor_log_mtime": now_ts - 2_000,
            "refill_queue_exists": False,
            "refill_project_url": "",
            "manual_submission_queue": [],
            "ready_submission_entries": [],
            "supervisor_code_mtime": 0,
            "supervisor_started_ts": now_ts - 10_000,
            "supervisor_exited_ts": 0,
            "supervisor_last_log_ts": now_ts - 2_000,
            "supervisor_poll_s": 120,
            "supervisor_pid": 1234,
            "supervisor_pid_started_ts": now_ts - 10_000,
            "supervisor_pid_script": "pipeline_supervisor.py",
            "supervisor_pid_alive": True,
        }

    def test_fresh_inner_activity_prevents_supervisor_stale_attention(self):
        kwargs = self.base_kwargs()
        kwargs["inner_log_mtime"] = kwargs["now_ts"] - 30
        kwargs["inner_worker_alive"] = True
        kwargs["supervisor_pid_started_ts"] = kwargs["supervisor_started_ts"]

        report = pipeline_health.build_health_report(**kwargs)

        self.assertEqual(report["health"], "running_or_ready")
        self.assertEqual(report["reason"], "runnable_backlog")


if __name__ == "__main__":
    unittest.main()
