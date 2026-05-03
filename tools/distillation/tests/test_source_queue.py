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
        self.assertEqual(candidate["oracle_rank"], 91)
        self.assertEqual(candidate["next_step"], "distill_source")

    def test_normalize_oracle_candidate_converts_small_rank_to_high_priority(self):
        candidate = source_queue._normalize_oracle_candidate(
            {
                "proposed_source": "Stallings foldings",
                "source_type": "topic_cluster",
                "fit_score": 10,
                "novelty_score": 7,
                "priority": 1,
                "target_sections": ["folding"],
            }
        )

        self.assertIsNotNone(candidate)
        self.assertEqual(candidate["priority"], 99)
        self.assertEqual(candidate["oracle_rank"], 1)

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

    def test_merge_candidates_preserves_covered_seed_status(self):
        merged = source_queue._merge_candidates(
            [
                {
                    "id": "seed:1",
                    "status": "covered_by_oracle",
                    "source_type": "discovery_seed",
                    "seed_source": "Gromov",
                    "target_sections": ["pom"],
                    "covered_by_candidates": ["oracle:1"],
                    "next_step": "distill_source_candidate_opened",
                }
            ],
            [
                {
                    "id": "seed:1",
                    "status": "needs_oracle",
                    "source_type": "discovery_seed",
                    "seed_source": "Gromov",
                    "target_sections": ["pom"],
                    "next_step": "oracle_source_discovery",
                }
            ],
        )

        self.assertEqual(merged[0]["status"], "covered_by_oracle")
        self.assertEqual(merged[0]["covered_by_candidates"], ["oracle:1"])

    def test_mark_covered_seeds_links_oracle_candidates(self):
        marked = source_queue.mark_covered_seeds(
            [
                {
                    "id": "seed:1",
                    "status": "needs_oracle",
                    "next_step": "oracle_source_discovery",
                },
                {
                    "id": "seed:2",
                    "status": "needs_oracle",
                    "next_step": "oracle_source_discovery",
                },
            ],
            [
                {
                    "id": "oracle:1",
                    "origin_entry_ids": ["seed:1"],
                }
            ],
        )

        self.assertEqual(marked[0]["status"], "covered_by_oracle")
        self.assertEqual(marked[0]["covered_by_candidates"], ["oracle:1"])
        self.assertEqual(marked[1]["status"], "needs_oracle")

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
