import json
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

    def test_prior_feedback_includes_last_blocked_review_after_restart(self):
        old_distillation_dir = distill.DISTILLATION_DIR
        try:
            with distill._temporary_directory(prefix="blocked_feedback_") as tmp:
                distill.DISTILLATION_DIR = old_distillation_dir.__class__(tmp)
                state = distill.DistillState("Bourgain")
                state_dir = distill._state_dir(state.name)
                state_dir.mkdir(parents=True)
                (state_dir / "blocked.json").write_text(
                    json.dumps(
                        {
                            "status": "review_failed",
                            "last_review": {
                                "claude": {
                                    "score": 5,
                                    "verdict": "revise",
                                    "issues": ["Packet terminology is ungrounded."],
                                    "required_changes": [
                                        "Define packet in target vocabulary."
                                    ],
                                },
                                "minimum_score": 5,
                                "review_backend": "claude",
                            },
                        }
                    ),
                    encoding="utf-8",
                )

                block = distill._build_prior_feedback_block(state)
        finally:
            distill.DISTILLATION_DIR = old_distillation_dir

        self.assertIn("Last blocked review", block)
        self.assertIn("Packet terminology is ungrounded", block)
        self.assertIn("Define packet in target vocabulary", block)


if __name__ == "__main__":
    unittest.main()
