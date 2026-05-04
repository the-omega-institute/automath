from datetime import datetime
import unittest

from tools.distillation import distill


class ClaudeQuotaTests(unittest.TestCase):
    def test_parse_score_response_treats_extra_usage_as_non_retryable(self):
        result = distill._parse_score_response(
            "You're out of extra usage · resets 2:10am (Asia/Singapore)"
        )

        self.assertEqual(result["score"], 0)
        self.assertEqual(result["verdict"], "unavailable")
        self.assertTrue(result["unavailable"])
        self.assertFalse(result["retryable"])
        self.assertIn("out of extra usage", result["issues"][0])

    def test_claude_quota_reset_delay_parses_reset_time(self):
        delay = distill._claude_quota_reset_delay(
            "You're out of extra usage · resets 2:10am (Asia/Singapore)",
            now=datetime(2026, 5, 5, 1, 48, 0),
        )

        self.assertEqual(delay, 23 * 60)


if __name__ == "__main__":
    unittest.main()
