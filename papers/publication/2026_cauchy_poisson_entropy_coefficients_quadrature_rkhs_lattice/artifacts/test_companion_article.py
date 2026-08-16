from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[1]


class CompanionArticleTests(unittest.TestCase):
    def test_article_has_required_branches(self) -> None:
        main = (ROOT / "main.tex").read_text(encoding="utf-8")
        for source in (
            "sec_entropy_asymptotics",
            "sec_verified_A2_results",
            "sec_entropy_30_eighth_defect_layer",
            "sec_gram_space",
            "sec_strip_00_poisson_image",
            "sec_strip_10_hardy_aux_lattice",
            "sec_strip_20_symbol_sampling",
            "sec_strip_30_cardinal_observation",
        ):
            self.assertIn(rf"\input{{{source}}}", main)

    def test_no_printed_relocation_proof_path_is_active(self) -> None:
        main = (ROOT / "main.tex").read_text(encoding="utf-8")
        self.assertNotIn("relocatedproof", main)
        self.assertNotIn("Supplementary Material", main)

    def test_bibliography_matches_citations(self) -> None:
        aux = (ROOT / "main.aux").read_text(encoding="utf-8")
        bibliography = (ROOT / "bibliography_companion.tex").read_text(
            encoding="utf-8"
        )
        cited = set(re.findall(r"\\citation\{([^}]+)\}", aux))
        items = set(re.findall(r"\\bibitem\{([^}]+)\}", bibliography))
        self.assertEqual(cited, items)

    def test_metadata_records_unassessed_status(self) -> None:
        metadata = (ROOT / "submission_metadata.md").read_text(encoding="utf-8")
        self.assertIn("separated from", metadata)
        self.assertIn("No venue assessment has yet been made", metadata)
        self.assertIn("No target journal or acceptance probability", metadata)

    def test_numbering_is_automatic_and_sources_fit_limit(self) -> None:
        active = "\n".join(
            path.read_text(encoding="utf-8") for path in ROOT.glob("*.tex")
        )
        self.assertNotRegex(active, r"\\tag\s*\{")
        self.assertNotRegex(active, r"\\setcounter\s*\{")
        for path in ROOT.glob("*.tex"):
            self.assertLess(len(path.read_text(encoding="utf-8").splitlines()), 800)


if __name__ == "__main__":
    unittest.main()
