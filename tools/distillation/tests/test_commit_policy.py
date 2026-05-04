import unittest
from types import SimpleNamespace

from tools.distillation import distill


class DistillCommitPolicyTests(unittest.TestCase):
    def test_stage_e_looping_to_next_family_commits_completed_family(self):
        state = SimpleNamespace(
            current_stage="W",
            completed_families=["illegal-turn elimination and train-track normal form"],
        )

        label = distill._batch_commit_label_after_stage("E", state)

        self.assertEqual(
            label,
            "family illegal-turn elimination and train-track normal form complete",
        )

    def test_stage_w_does_not_commit_before_registry_export(self):
        state = SimpleNamespace(
            current_stage="E",
            completed_families=["illegal-turn elimination and train-track normal form"],
        )

        self.assertIsNone(distill._batch_commit_label_after_stage("W", state))


if __name__ == "__main__":
    unittest.main()
