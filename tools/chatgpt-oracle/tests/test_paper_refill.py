from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPT_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_ROOT))

import paper_refill  # noqa: E402


class PaperRefillTests(unittest.TestCase):
    def test_build_refill_prompt_uses_local_ledger_context(self):
        prompt = paper_refill.build_refill_prompt(
            2,
            existing_papers=["submitted_2026_prior"],
            existing_proposals=[],
            ledger_seeds=[
                {
                    "candidate_title": "Central 2-Rank Obstructions",
                    "source_paper": "2026_window6",
                }
            ],
            context_mode="local",
        )

        self.assertIn("local research ledger seeds", prompt)
        self.assertIn("Central 2-Rank Obstructions", prompt)
        self.assertIn("do not invent unrelated papers", prompt)
        self.assertIn("submitted_2026_prior", prompt)

    def test_load_ledger_seed_candidates_deduplicates_by_fingerprint(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger = Path(tmp) / "research_ledger.jsonl"
            rows = [
                {
                    "category": "split_candidates",
                    "fingerprint": "abc",
                    "source_paper": "paper_a",
                    "item": {
                        "candidate_title": "Old Title",
                        "reason": "old",
                    },
                },
                {
                    "category": "split_candidates",
                    "fingerprint": "abc",
                    "source_paper": "paper_b",
                    "item": {
                        "candidate_title": "New Title",
                        "reason": "new",
                    },
                },
                {"category": "stage_event", "item": {"candidate_title": "Ignore"}},
            ]
            ledger.write_text(
                "\n".join(json.dumps(row) for row in rows) + "\n",
                encoding="utf-8",
            )

            with mock.patch.object(paper_refill, "RESEARCH_LEDGER_PATH", ledger):
                seeds = paper_refill._load_ledger_seed_candidates()

        self.assertEqual(len(seeds), 1)
        self.assertEqual(seeds[0]["candidate_title"], "New Title")
        self.assertEqual(seeds[0]["source_paper"], "paper_b")

    def test_run_refill_without_project_url_dispatches_local_context(self):
        response = json.dumps({
            "candidates": [
                {
                    "proposed_title": "A New Split",
                    "topic": "Prove one clean theorem from a ledger seed.",
                    "outline": ["Definitions", "Main theorem"],
                    "anchor_theorems": ["For every audited object, X holds."],
                    "target_journal": "Example Journal",
                    "fit_score": 8,
                    "novelty_score": 8,
                    "rationale": "Strong enough for a split.",
                    "risks": ["overlap"],
                }
            ]
        })
        with tempfile.TemporaryDirectory() as tmp:
            queue_path = Path(tmp) / "_refill_queue.json"
            with mock.patch.object(paper_refill, "QUEUE_PATH", queue_path), \
                 mock.patch.object(paper_refill, "PUBLICATION_DIR", Path(tmp)), \
                 mock.patch.object(paper_refill, "_existing_paper_names",
                                   return_value=[]), \
                 mock.patch.object(paper_refill, "_load_ledger_seed_candidates",
                                   return_value=[{"candidate_title": "Seed"}]), \
                 mock.patch.object(
                     paper_refill.oracle_dispatch,
                     "dispatch_direct_record",
                     return_value={"response": response, "conversation_id": "conv_1"},
                 ) as dispatch:
                result = paper_refill.run_refill(
                    project_url="",
                    limit=1,
                    timeout=30,
                    model="chatgpt-5.4-pro",
                    dry_run=False,
                )

            dispatch.assert_called_once()
            self.assertEqual(dispatch.call_args.kwargs["project_url"], "")
            self.assertEqual(result["status"], "ok")
            data = json.loads(queue_path.read_text(encoding="utf-8"))

        self.assertEqual(len(data["candidates"]), 1)
        self.assertEqual(data["candidates"][0]["proposed_title"], "A New Split")

    def test_main_allows_non_dry_run_without_project_url(self):
        with mock.patch.object(
            paper_refill,
            "run_refill",
            return_value={"status": "ok", "accepted": 0},
        ) as run:
            rc = paper_refill.main(["--limit", "1", "--timeout", "1"])

        self.assertEqual(rc, 0)
        self.assertEqual(run.call_args.kwargs["project_url"], "")


if __name__ == "__main__":
    unittest.main()
