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


if __name__ == "__main__":
    unittest.main()
