import unittest

from tools.distillation import distill


class RegistryMergeTests(unittest.TestCase):
    def test_merge_registry_entries_normalizes_slug_and_preserves_old_knowledge(self):
        existing = {
            "source_slug": "euclid_elements",
            "source_type": "classical_geometry_methodology",
            "integration_mode": "knowledge_node",
            "date_created": "2026-04-09",
            "primary_note": "papers/publication/backflow/euclid_geometry_backflow_2026-04-09.md",
            "primary_targets": ["pom", "folding"],
            "integrated_writebacks": ["primitive_discipline"],
            "expansion_queue": [{"kernel": "bookII", "status": "active"}],
        }
        incoming = {
            "source_slug": "euclid-elements",
            "source_type": "distilled_mathematical_methodology",
            "integration_mode": "distillation_pipeline",
            "date_created": "2026-04-23",
            "primary_note": "papers/publication/backflow/.distillation/euclid_elements/generated_payload.json",
            "primary_targets": ["folding", "zeta_finite_part"],
            "integrated_writebacks": ["primitive_discipline", "distill:new"],
            "expansion_queue": [{"kernel": "bookII", "status": "active"}, {"kernel": "new", "status": "active"}],
        }

        merged = distill._merge_registry_entries(existing, incoming)

        self.assertEqual(merged["source_slug"], "euclid_elements")
        self.assertEqual(merged["date_created"], "2026-04-09")
        self.assertEqual(
            merged["source_type"],
            "classical_geometry_methodology+distilled_mathematical_methodology",
        )
        self.assertEqual(
            merged["integration_mode"],
            "knowledge_node+distillation_pipeline",
        )
        self.assertEqual(
            merged["primary_notes"],
            [
                "papers/publication/backflow/euclid_geometry_backflow_2026-04-09.md",
                "papers/publication/backflow/.distillation/euclid_elements/generated_payload.json",
            ],
        )
        self.assertEqual(merged["primary_targets"], ["pom", "folding", "zeta_finite_part"])
        self.assertEqual(merged["integrated_writebacks"], ["primitive_discipline", "distill:new"])
        self.assertEqual(len(merged["expansion_queue"]), 2)

    def test_board_block_uses_chinese_headers_and_status_labels(self):
        board = distill._board_block(
            [
                {
                    "source_slug": "cech_cohomology",
                    "status": "active",
                    "primary_targets": ["typed_address_biaxial_completion", "conclusion"],
                    "integrated_writebacks": ["prop:one", "prop:two"],
                    "expansion_queue": [{"queue_id": "abc123", "status": "active"}],
                }
            ]
        )

        self.assertIn("| 来源 | 状态 | 目标章节 | 写回数 | 待扩张数 |", board)
        self.assertIn("| `cech_cohomology` | 进行中 |", board)

    def test_oracle_relevant_evidence_pack_prioritizes_target_sections_and_limits_rows(self):
        pack = {
            "terms": ["holonomy", "budget", "sticky"],
            "source_theorem_families": [
                {
                    "name": "holonomy-residue classification",
                    "target_sections": ["spg", "physical_spacetime_skeleton"],
                    "key_results": ["r1", "r2", "r3", "r4"],
                }
            ],
            "section_index": [
                {"section": "spg", "python_score": 4},
                {"section": "folding", "python_score": 10},
                {"section": "physical_spacetime_skeleton", "python_score": 3},
            ],
            "high_signal_claims": [
                {"section": "folding", "score": 9, "label": "a"},
                {"section": "spg", "score": 2, "label": "b", "snippet": "x" * 1000},
            ],
            "existing_distillation_claims": [
                {"section": "recursive_addressing", "score": 8, "label": "x"},
                {"section": "physical_spacetime_skeleton", "score": 1, "label": "y"},
            ],
            "frontier_interfaces": [
                {"section": "folding", "score": 5, "term": "budget"},
                {"section": "spg", "score": 1, "term": "holonomy"},
            ],
            "distillation_memory": [
                {"id": "m1", "kind": "split_candidate", "target_sections": ["folding"]},
                {"id": "m2", "kind": "oracle_sidecar", "target_sections": ["spg"]},
            ],
        }

        compact = distill._oracle_relevant_evidence_pack(
            pack,
            {"name": "holonomy-residue classification", "target_sections": ["spg"]},
            [{"section": "physical_spacetime_skeleton"}],
        )

        self.assertEqual(
            compact["focused_target_sections"],
            ["physical_spacetime_skeleton", "spg"],
        )
        self.assertEqual(compact["high_signal_claims"][0]["section"], "spg")
        self.assertLessEqual(
            len(compact["high_signal_claims"][0]["snippet"]),
            distill.ORACLE_EVIDENCE_SNIPPET_CHARS + 3,
        )
        self.assertEqual(
            compact["existing_distillation_claims"][0]["section"],
            "physical_spacetime_skeleton",
        )
        self.assertEqual(compact["frontier_interfaces"][0]["section"], "spg")
        self.assertEqual(compact["distillation_memory"][0]["id"], "m2")
        self.assertEqual(
            compact["source_theorem_families"][0]["key_results"],
            ["r1", "r2", "r3"],
        )


if __name__ == "__main__":
    unittest.main()
