import unittest

from tools.distillation import source_queue


class SourceQueueTests(unittest.TestCase):
    def test_discovery_seeds_from_memory_create_oracle_ready_seed(self):
        seeds = source_queue.discovery_seeds_from_memory(
            [
                {
                    "id": "memory:1",
                    "kind": "split_candidate",
                    "status": "open",
                    "source": "Bourgain",
                    "target_sections": ["pom"],
                    "reason": "payload target was outside current scope",
                }
            ]
        )

        self.assertEqual(len(seeds), 1)
        self.assertEqual(seeds[0]["status"], "needs_oracle")
        self.assertEqual(seeds[0]["next_step"], "oracle_source_discovery")
        self.assertEqual(seeds[0]["target_sections"], ["pom"])

    def test_discovery_seeds_deduplicate_same_source_section(self):
        seeds = source_queue.discovery_seeds_from_memory(
            [
                {
                    "id": "memory:1",
                    "kind": "split_candidate",
                    "status": "open",
                    "source": "Euclid Elements",
                    "target_sections": ["folding"],
                    "reason": "first",
                },
                {
                    "id": "memory:2",
                    "kind": "split_candidate",
                    "status": "open",
                    "source": "Euclid-Elements",
                    "target_sections": ["folding"],
                    "reason": "second",
                },
            ]
        )

        self.assertEqual(len(seeds), 1)

    def test_normalize_oracle_candidate_filters_low_scores(self):
        candidate = source_queue._normalize_oracle_candidate(
            {
                "proposed_source": "Example source",
                "fit_score": 6,
                "novelty_score": 9,
                "target_sections": ["folding"],
            }
        )

        self.assertIsNone(candidate)

    def test_normalize_oracle_candidate_accepts_high_quality_source(self):
        candidate = source_queue._normalize_oracle_candidate(
            {
                "proposed_source": "Perelman Ricci-flow surgery papers",
                "source_type": "paper",
                "fit_score": 9,
                "novelty_score": 8,
                "priority": 91,
                "target_sections": ["physical_spacetime_skeleton"],
                "omega_mechanisms": ["surgery", "canonical neighborhoods"],
                "why_now": "tests geometric flow interfaces",
                "source_material": ["Ricci flow with surgery"],
                "seed_ids": ["seed:1"],
            }
        )

        self.assertIsNotNone(candidate)
        self.assertEqual(candidate["status"], "open")
        self.assertEqual(candidate["priority"], 91)
        self.assertEqual(candidate["next_step"], "distill_source")

    def test_merge_candidates_preserves_existing_created_at(self):
        merged = source_queue._merge_candidates(
            [
                {
                    "id": "oracle:abc",
                    "status": "open",
                    "priority": 20,
                    "proposed_source": "Old",
                    "created_at": "old-time",
                    "updated_at": "old-time",
                }
            ],
            [
                {
                    "id": "oracle:abc",
                    "status": "open",
                    "priority": 30,
                    "proposed_source": "New",
                }
            ],
        )

        self.assertEqual(len(merged), 1)
        self.assertEqual(merged[0]["created_at"], "old-time")
        self.assertEqual(merged[0]["priority"], 30)

    def test_merge_candidates_collapses_duplicate_seed_rows(self):
        merged = source_queue._merge_candidates(
            [
                {
                    "id": "seed:1",
                    "status": "needs_oracle",
                    "source_type": "discovery_seed",
                    "priority": 20,
                    "seed_source": "Gromov",
                    "target_sections": ["pom"],
                    "origin_entry_ids": ["a"],
                },
                {
                    "id": "seed:2",
                    "status": "needs_oracle",
                    "source_type": "discovery_seed",
                    "priority": 30,
                    "seed_source": "Gromov",
                    "target_sections": ["pom"],
                    "origin_entry_ids": ["b"],
                },
            ],
            [],
        )

        self.assertEqual(len(merged), 1)
        self.assertEqual(merged[0]["priority"], 30)
        self.assertEqual(merged[0]["origin_entry_ids"], ["a", "b"])

    def test_queue_counts_groups_statuses(self):
        counts = source_queue.queue_counts(
            {
                "candidates": [
                    {"status": "open"},
                    {"status": "needs_oracle"},
                    {"status": "open"},
                ]
            }
        )

        self.assertEqual(counts, {"open": 2, "needs_oracle": 1})


if __name__ == "__main__":
    unittest.main()
