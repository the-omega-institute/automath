from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]


class StableSpineManuscriptTests(unittest.TestCase):
    def test_main_article_keeps_the_restored_article_architecture(self) -> None:
        main = (ROOT / "main.tex").read_text(encoding="utf-8")

        self.assertIn(r"\input{sec_verified_A2_results}", main)
        self.assertIn(r"\input{bibliography_shared}", main)
        self.assertNotIn(r"\input{sec_stable_entropy_spine}", main)
        for article_input in (
            r"\input{sec_entropy_asymptotics}",
            r"\input{sec_entropy_30_eighth_defect_layer}",
            r"\input{sec_gram_space}",
            r"\input{sec_strip_00_poisson_image}",
            r"\input{sec_strip_20_symbol_sampling}",
            r"\input{sec_strip_30_cardinal_observation}",
        ):
            self.assertIn(article_input, main)

    def test_stable_tail_decomposition_is_stated_and_proved(self) -> None:
        theorem_path = ROOT / "sec_verified_A2_results.tex"
        theorem_source = theorem_path.read_text(encoding="utf-8")

        required = (
            r"\label{thm:stable-law-by-law-decomposition}",
            r"\mathcal Q_{\alpha,d}(\Sigma)s^{-4}",
            r"\int_{\{|x|>s\}}",
            r"\frac{p_1^{(\alpha,d)}(y-x/s)}",
            r"\Phi(V_s^\nu)",
            r"o(s^{-4})",
            r"\|R_s\|_\infty+\|R_s\|_{L^1(\Omega_{\alpha,d})}=o(s^{-2})",
            r"\int V_s^\nu\dd\Omega_{\alpha,d}=\tau_s",
            r"No regular-variation, absolute-continuity, or moment hypothesis above order two",
        )
        for text in required:
            self.assertIn(text, theorem_source)

    def test_decomposition_theorem_has_one_source(self) -> None:
        label = r"\label{thm:stable-law-by-law-decomposition}"
        sources = list(ROOT.glob("*.tex"))
        occurrences = sum(
            path.read_text(encoding="utf-8").count(label) for path in sources
        )
        self.assertEqual(occurrences, 1)

    def test_literature_audit_names_all_requested_indexes(self) -> None:
        audit = (ROOT / "artifacts" / "literature_check.md").read_text(
            encoding="utf-8"
        )
        for index in ("arXiv", "Crossref", "Semantic Scholar", "zbMATH"):
            self.assertIn(index, audit)
        self.assertIn("Ishige--Kawakami--Michihisa", audit)


if __name__ == "__main__":
    unittest.main()
