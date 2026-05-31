import tempfile
import unittest
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_intake


class NewmathIntakeGuardTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.publication_root = Path(self.tmp.name)
        self.root = self.publication_root / "newmath_intake"
        (self.root / "seeds").mkdir(parents=True)
        self._write_indexes()
        self._write_seed_dirs()

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def _write_indexes(self) -> None:
        seed_rows = "\n".join(
            f"| `newmath_intake/seeds/{name}` | row |"
            for name in sorted(check_intake.KNOWN_SEEDS)
        )
        (self.root / "README.md").write_text(
            "not an active paper pipeline\nmust not run Stage A\nCURRENT_STATUS.md\n",
            encoding="utf-8",
        )
        (self.root / "CURRENT_STATUS.md").write_text(
            "\n".join(
                [
                    "not a promotion command",
                    "promotion <seed> as <active_slug>",
                    "bedc_automation_pipeline",
                    "bedc_finite_kernel_calculus",
                    "bedc_rule110_finite_witness",
                    "do not run Stage A",
                ]
            ),
            encoding="utf-8",
        )
        (self.root / "BOARD.md").write_text(
            "INTAKE-NOT-ACTIVE\nmust not be picked up\n" + seed_rows,
            encoding="utf-8",
        )
        (self.root / "P0_GATE_AUDIT.md").write_text(
            "\n".join(
                [
                    "promotion-decision gate",
                    "source-theorem gate",
                    "artifact-rerun gate",
                    "Do not promote",
                    "must not promote or queue",
                    "promotion <seed> as <active_slug>",
                ]
            ),
            encoding="utf-8",
        )
        (self.root / "AGENT_WORK_QUEUE.md").write_text(
            "P0_GATE_AUDIT.md\nCURRENT_STATUS.md\nnot a daemon queue\n",
            encoding="utf-8",
        )
        (self.root / "P0_DECISION_PACKET.md").write_text(
            "\n".join(
                [
                    "not a promotion command",
                    "bedc_automation_pipeline",
                    "bedc_finite_kernel_calculus",
                    "bedc_rule110_finite_witness",
                    "promotion bedc_automation_pipeline as 2026_auditable_theory_to_paper_pipeline",
                    "do not create `papers/publication/2026_*`",
                ]
            ),
            encoding="utf-8",
        )
        (self.root / "PROMOTION_HANDOFF.md").write_text(
            "\n".join(
                [
                    "not a promotion command",
                    "do not create any `papers/publication/2026_*`",
                    "do not add `main.tex`",
                    "do not add `PIPELINE.md`",
                    "promotion <seed> as <active_slug>",
                ]
            ),
            encoding="utf-8",
        )
        (self.publication_root / "PROGRAM_BOARD.md").write_text(
            "active paper track\nStage A/P0-P7\n" + seed_rows,
            encoding="utf-8",
        )
        (self.publication_root / "PROGRAM_BOARD_MACHINE.md").write_text(
            "INTAKE-NOT-ACTIVE\ndo not run Stage A\n" + seed_rows,
            encoding="utf-8",
        )

    def _write_seed_dirs(self) -> None:
        for name in check_intake.KNOWN_SEEDS:
            seed_dir = self.root / "seeds" / name
            seed_dir.mkdir()
            for filename in check_intake.REQUIRED_SEED_FILES.get(name, set()):
                text = "required evidence\n"
                if filename == "promotion_checklist.md":
                    text += "promotion <seed> as <active_slug>\n"
                (seed_dir / filename).write_text(text, encoding="utf-8")

    def test_valid_intake_tree_passes(self):
        errors, warnings = check_intake.run_check(self.root)

        self.assertEqual(errors, [])
        self.assertEqual(warnings, [])

    def test_active_trigger_file_fails(self):
        (self.root / "seeds" / "bedc_automation_pipeline" / "main.tex").write_text(
            "not allowed\n",
            encoding="utf-8",
        )

        errors, _warnings = check_intake.run_check(self.root)

        self.assertTrue(any("active-paper trigger file" in error for error in errors))

    def test_active_trigger_file_case_variant_fails(self):
        (self.root / "seeds" / "bedc_automation_pipeline" / "Main.TEX").write_text(
            "not allowed\n",
            encoding="utf-8",
        )
        (self.root / "seeds" / "bedc_automation_pipeline" / "pipeline.md").write_text(
            "not allowed\n",
            encoding="utf-8",
        )

        errors, _warnings = check_intake.run_check(self.root)

        trigger_errors = [
            error for error in errors if "active-paper trigger file" in error
        ]
        self.assertEqual(len(trigger_errors), 2, errors)

    def test_promotion_only_file_fails_before_promotion(self):
        (
            self.root
            / "seeds"
            / "bedc_automation_pipeline"
            / "research_directive.md"
        ).write_text(
            "not allowed\n",
            encoding="utf-8",
        )

        errors, _warnings = check_intake.run_check(self.root)

        self.assertTrue(any("active-paper trigger file" in error for error in errors))

    def test_missing_p0_required_file_fails(self):
        (
            self.root
            / "seeds"
            / "bedc_automation_pipeline"
            / "source_decision_note.md"
        ).unlink()

        errors, _warnings = check_intake.run_check(self.root)

        self.assertTrue(
            any("source_decision_note.md" in error for error in errors),
            errors,
        )

    def test_seed_promotion_checklist_requires_exact_command_boundary(self):
        (
            self.root
            / "seeds"
            / "bedc_automation_pipeline"
            / "promotion_checklist.md"
        ).write_text("required evidence\n", encoding="utf-8")

        errors, _warnings = check_intake.run_check(self.root)

        self.assertTrue(
            any("promotion <seed> as <active_slug>" in error for error in errors),
            errors,
        )

    def test_missing_top_level_board_seed_row_fails(self):
        (self.publication_root / "PROGRAM_BOARD_MACHINE.md").write_text(
            "INTAKE-NOT-ACTIVE\ndo not run Stage A\n",
            encoding="utf-8",
        )

        errors, _warnings = check_intake.run_check(self.root)

        self.assertTrue(
            any("metacic_closed_normal_consistency" in error for error in errors),
            errors,
        )

    def test_missing_current_status_fails(self):
        (self.root / "CURRENT_STATUS.md").unlink()

        errors, _warnings = check_intake.run_check(self.root)

        self.assertTrue(
            any("CURRENT_STATUS.md" in error for error in errors),
            errors,
        )


if __name__ == "__main__":
    unittest.main()
