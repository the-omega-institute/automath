"""Smoke tests for tools/chatgpt-oracle/pipeline_supervisor and oracle_server multi-turn glue.

These tests exercise the cross-platform helpers and the multi-turn server
pieces that were added on dev-automation-integration. They do not require a
live ChatGPT browser tab — the oracle_server is exercised in-process.
"""

from __future__ import annotations

import json
import os
import sys
import threading
import time
import unittest
import urllib.request
from http.server import HTTPServer
from pathlib import Path

SCRIPT_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_ROOT))

import oracle_server  # noqa: E402
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

    def test_install_signal_handlers_does_not_raise(self):
        pipeline_supervisor._install_signal_handlers()  # idempotent

    def test_discover_runnable_papers_returns_path_list(self):
        papers = pipeline_supervisor.discover_runnable_papers()
        self.assertIsInstance(papers, list)
        for p in papers:
            self.assertTrue(p.is_dir())
            self.assertTrue((p / "main.tex").exists())


class OracleServerMultiTurnTests(unittest.TestCase):
    """Spin up oracle_server in-process on an ephemeral port and exercise multi-turn."""

    @classmethod
    def setUpClass(cls):
        # Reset module-level state so the class is order-independent.
        oracle_server.task_queue.clear()
        oracle_server.results.clear()
        oracle_server.pending_tasks.clear()
        oracle_server.dispatch_times.clear()
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

    def test_submit_with_conversation_id_is_multi_turn_capable(self):
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


if __name__ == "__main__":
    unittest.main()
