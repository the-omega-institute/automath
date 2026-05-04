import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
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

    def test_existing_stallings_growth_content_closes_growth_family(self):
        with TemporaryDirectory() as tmp:
            body_root = Path(tmp)
            target = body_root / "fold_residual_time" / "subsec__protocol-screening-fold-survivor.tex"
            target.parent.mkdir(parents=True)
            target.write_text(
                "\\label{def:distill-stallings-fold-survivor-transition-growth-ledger}\n"
                "\\label{prop:distill-stallings-fold-survivor-transition-growth-ledger}\n"
                "\\label{distill:stallings_foldings_and_bestvina_handel_train_tracks-"
                "finite_descent_to_folded_core-transition-growth-critical-core-trimming}\n",
                encoding="utf-8",
            )
            state = SimpleNamespace(
                name="Stallings foldings and Bestvina-Handel train tracks"
            )

            completed = distill._existing_content_completed_families(
                state,
                body_root=body_root,
            )

        self.assertEqual(
            completed,
            ["growth-classification from legal survivors"],
        )


if __name__ == "__main__":
    unittest.main()
