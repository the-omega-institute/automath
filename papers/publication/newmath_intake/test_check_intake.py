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
            "not an active paper pipeline\nmust not run Stage A\n",
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
                ]
            ),
            encoding="utf-8",
        )
        (self.root / "AGENT_WORK_QUEUE.md").write_text(
            "P0_GATE_AUDIT.md\nnot a daemon queue\n",
            encoding="utf-8",
        )
        (self.root / "PROMOTION_HANDOFF.md").write_text(
            "\n".join(
                [
                    "not a promotion command",
                    "do not create any `papers/publication/2026_*`",
                    "do not add `main.tex`",
                    "do not add `PIPELINE.md`",
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
                (seed_dir / filename).write_text("required evidence\n", encoding="utf-8")

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


if __name__ == "__main__":
    unittest.main()
