import unittest

from tools.distillation import distill


class ReviewFeedbackTests(unittest.TestCase):
    def test_compact_review_feedback_preserves_actionable_claude_feedback(self):
        review = {
            "codex": {
                "score": 0,
                "verdict": "unavailable",
                "issues": ["Reviewer not configured for this backend"],
                "required_changes": [],
                "unavailable": True,
            },
            "claude": {
                "score": 5,
                "verdict": "revise",
                "issues": [
                    "Proof is thin relative to the theorem setup.",
                    "Target file may exceed the line budget.",
                ],
                "required_changes": [
                    r"Replace \Eta with a valid macro.",
                    "Move interpretive prose out of the proposition.",
                ],
            },
            "minimum_score": 5,
            "gate_passed": False,
            "review_backend": "claude",
        }

        summary = distill._compact_review_feedback(review)

        self.assertIn("backend=claude", summary)
        self.assertIn("claude score=5 verdict=revise", summary)
        self.assertIn("issue: Proof is thin", summary)
        self.assertIn(r"required_change: Replace \Eta", summary)
        self.assertNotIn("Reviewer not configured", summary)


if __name__ == "__main__":
    unittest.main()
