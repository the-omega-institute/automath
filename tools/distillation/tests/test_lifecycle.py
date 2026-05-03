import unittest

from tools.distillation import lifecycle


class LifecycleTests(unittest.TestCase):
    def test_done_contract_classifies_complete(self):
        meta = lifecycle.annotate({"done_contract": {"passed": True}})

        self.assertEqual(meta["failure_kind"], "none")
        self.assertEqual(meta["next_action"], "complete")

    def test_blocked_semantic_scan_is_retriable_once(self):
        meta = lifecycle.annotate(
            {
                "done_contract": {"passed": False},
                "next_policy_action": {
                    "action": "blocked",
                    "gate": "semantic_scan_relevance",
                    "reason": "Stage S produced no relevant section matches",
                },
            }
        )

        self.assertEqual(meta["failure_kind"], "semantic_scan_empty")
        self.assertEqual(meta["retry_budget"], 1)
        self.assertEqual(meta["next_action"], "retry_resume")

    def test_writeback_review_failure_is_retriable(self):
        meta = lifecycle.annotate(
            {
                "done_contract": {"passed": False},
                "blocked": {"stage": "W", "status": "review_failed"},
            }
        )

        self.assertEqual(meta["failure_kind"], "writeback_review_failed")
        self.assertTrue(lifecycle.should_run_pipeline(meta))

    def test_retry_budget_exhaustion_alerts_user(self):
        meta = lifecycle.annotate(
            {
                "attempts": 4,
                "done_contract": {"passed": False},
                "oracle_status": {"reason": "oracle task timeout"},
            }
        )

        self.assertEqual(meta["failure_kind"], "oracle_timeout")
        self.assertEqual(meta["next_action"], "alert_user")
        self.assertTrue(meta["needs_user_intervention"])

    def test_policy_blocked_requires_user_intervention(self):
        meta = lifecycle.annotate(
            {
                "done_contract": {"passed": False},
                "next_policy_action": {
                    "action": "blocked",
                    "gate": "done_contract",
                    "reason": "unclassified completion failure",
                },
            }
        )

        self.assertEqual(meta["failure_kind"], "policy_blocked")
        self.assertEqual(meta["next_action"], "alert_user")
        self.assertTrue(meta["needs_user_intervention"])


if __name__ == "__main__":
    unittest.main()
