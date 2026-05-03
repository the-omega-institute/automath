import unittest

from tools.distillation import supervisor


class SupervisorSelectionTests(unittest.TestCase):
    def test_runnable_records_skip_done_sources(self):
        records = [
            {
                "name": "Done",
                "done": True,
                "next_action": "complete",
                "splits": 1,
                "debts": 0,
            },
            {
                "name": "Active",
                "done": False,
                "next_action": "run_pipeline",
                "splits": 0,
                "debts": 1,
            },
        ]

        runnable = supervisor.runnable_records(records)

        self.assertEqual([record["name"] for record in runnable], ["Active"])

    def test_backlog_records_include_done_split_candidates(self):
        records = [
            {"name": "A", "done": True, "splits": 2, "debts": 0},
            {"name": "B", "done": True, "splits": 0, "debts": 0},
            {"name": "C", "done": False, "splits": 0, "debts": 3},
        ]

        backlog = supervisor.backlog_records(records)

        self.assertEqual([record["name"] for record in backlog], ["A", "C"])

    def test_dashboard_mentions_expansion_backlog(self):
        text = supervisor.format_dashboard(
            [
                {
                    "name": "Grothendieck",
                    "stage": "DONE",
                    "families_done": 5,
                    "families_total": 5,
                    "debts": 2,
                    "splits": 2,
                    "failure_kind": "none",
                    "next_action": "complete",
                    "done": True,
                }
            ],
            branch="distill-clean",
            sync={"status": "up_to_date"},
        )

        self.assertIn("branch: distill-clean", text)
        self.assertIn("expansion backlog: 1 source", text)
        self.assertIn("Grothendieck", text)


if __name__ == "__main__":
    unittest.main()
