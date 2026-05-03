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


if __name__ == "__main__":
    unittest.main()
