import string
import unittest

from tools.distillation import distill


class PromptTemplateTests(unittest.TestCase):
    def test_writeback_prompt_has_only_declared_format_fields(self):
        text = distill._load_prompt("writeback")
        fields = {
            field
            for _, field, _, _ in string.Formatter().parse(text)
            if field is not None
        }

        self.assertEqual(
            fields,
            {
                "mathematician",
                "payload",
                "targets",
                "section_contexts",
                "global_evidence_pack",
                "oracle_deepening_context",
                "schema",
            },
        )

    def test_deepen_prompt_has_only_declared_format_fields(self):
        text = distill._load_prompt("deepen")
        fields = {
            field
            for _, field, _, _ in string.Formatter().parse(text)
            if field is not None
        }

        self.assertEqual(
            fields,
            {
                "mathematician",
                "depth_cycle",
                "family_name",
                "current_datetime",
                "next_number",
                "key_results",
                "method_operators",
                "targets",
                "section_contexts",
                "global_evidence_pack",
                "oracle_deepening_context",
                "completed_families",
                "deep_research_directive",
                "schema",
                "source_slug",
                "family_slug",
            },
        )

    def test_stallings_growth_contract_blocks_wrong_target_hosts(self):
        contract = distill._family_specific_deepening_contract(
            {"name": "growth-classification from legal survivors"}
        )

        self.assertIn("subsec__protocol-screening-fold-survivor.tex", contract)
        self.assertIn("subsec__group-unification-audit-pointers.tex", contract)
        self.assertIn("transition matrix", contract)

    def test_stallings_subgroup_contract_blocks_zeckendorf_cyclic_route(self):
        contract = distill._family_specific_deepening_contract(
            {"name": "subgroup reconstruction from canonical finite automata"}
        )

        self.assertIn("folded labelled core graph", contract)
        self.assertIn("Do not translate it into", contract)
        self.assertIn("Zeckendorf", contract)
        self.assertIn("subsec__folding-map.tex", contract)


if __name__ == "__main__":
    unittest.main()
