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
        self.assertIn("subsec__group-unification-audit-pointers.tex", contract)
        self.assertIn("A={a}", contract)

    def test_stallings_subgroup_family_uses_group_unification_section_host(self):
        targets = distill._family_specific_writeback_targets(
            {"name": "subgroup reconstruction from canonical finite automata"}
        )

        self.assertEqual(len(targets), 1)
        self.assertEqual(
            targets[0]["tex_file"],
            "group_unification/subsec__group-unification-spectral-alignment.tex",
        )

    def test_connes_frobenius_family_avoids_grand_chain_conclusion_host(self):
        state = distill.DistillState("Connes-Consani arithmetic site")

        targets = distill._source_specific_writeback_targets(
            state,
            {"name": "Frobenius-correspondence spacetime skeleton"},
        )

        self.assertEqual(len(targets), 1)
        self.assertEqual(
            targets[0]["tex_file"],
            "physical_spacetime_skeleton/"
            "subsec__physical-spacetime-skeleton-nonretroactive-resolution.tex",
        )
        self.assertNotIn("grand-chain", targets[0]["tex_file"])

    def test_connes_source_contract_blocks_heavy_tautological_writebacks(self):
        state = distill.DistillState("Connes-Consani arithmetic site")

        contract = distill._source_specific_writeback_contract(state, None)

        self.assertIn("CONNES--CONSANI LAST-MILE CONTRACT", contract)
        self.assertIn("Output at most one writeback", contract)
        self.assertIn("Do not introduce a new action category", contract)
        self.assertIn("Sem/C/T^(2)", contract)
        self.assertIn("non-tautological", contract)
        self.assertIn("first-break fiber", contract)

    def test_source_contract_is_empty_for_generic_source(self):
        state = distill.DistillState("Generic Source")

        self.assertEqual(distill._source_specific_writeback_contract(state, None), "")

    def test_review_prompts_do_not_let_target_language_override_chinese(self):
        for prompt_name in ("review_codex", "review_claude"):
            text = distill._load_prompt(prompt_name)
            collapsed = " ".join(text.split())
            self.assertIn("Do not require translation to English", collapsed)
            self.assertIn("Chinese writeback rule overrides target-file language", collapsed)

    def test_writeback_prompts_keep_heuristics_out_of_formal_environments(self):
        for prompt_name in ("writeback", "deepen"):
            text = distill._load_prompt(prompt_name)
            collapsed = " ".join(text.split())
            self.assertIn("Do not put heuristic or interpretive commentary inside", collapsed)
            self.assertIn("definition, theorem, lemma, proposition, or proof environments", collapsed)
            self.assertIn("move it to a separate remark outside the formal environment", collapsed)
            self.assertIn("include an existence witness or make existence an explicit hypothesis", collapsed)

    def test_writeback_prompts_block_decorative_source_mechanisms(self):
        for prompt_name in ("writeback", "deepen"):
            text = distill._load_prompt(prompt_name)
            collapsed = " ".join(text.split())
            self.assertIn("source mechanism is active in the proof", collapsed)
            self.assertIn("source theory is only decorative", collapsed)
            self.assertIn("mechanical parameter substitution", collapsed)
            self.assertIn("conclusion follows immediately from the definition", collapsed)

    def test_review_prompts_do_not_hard_block_on_truncated_context_line_budget(self):
        for prompt_name in ("review_codex", "review_claude"):
            text = distill._load_prompt(prompt_name)
            collapsed = " ".join(text.split())
            self.assertIn("Do not reject solely because supplied section context is truncated", collapsed)
            self.assertIn("line-count gate is enforced by the application planner", collapsed)


if __name__ == "__main__":
    unittest.main()
