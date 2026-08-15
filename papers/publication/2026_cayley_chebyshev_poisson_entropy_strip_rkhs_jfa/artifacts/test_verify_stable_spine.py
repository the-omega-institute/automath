from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[1]
INPUT_RE = re.compile(r"\\input\{([^}]+)\}")


def read_tex_source(path: Path) -> str:
    """Read a TeX source together with any local input wrappers."""

    source = path.read_text(encoding="utf-8")

    def expand(match: re.Match[str]) -> str:
        child = ROOT / match.group(1)
        if child.suffix == "":
            child = child.with_suffix(".tex")
        return read_tex_source(child)

    return INPUT_RE.sub(expand, source)


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
        theorem_source = read_tex_source(theorem_path)

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

    def test_arbitrary_order_proxy_proof_closure_is_explicit(self) -> None:
        source = read_tex_source(ROOT / "sec_verified_A2_results.tex")
        required = (
            "Two-background KL perturbation",
            r"H'(t)",
            r"H''(t)",
            r"H'''(t)",
            r"\|A_s^\lambda-1\|_{L^1(\Omega_{\alpha,d})}",
            r"\|A_s^\nu-A_s^\eta\|_{L^1(\Omega_{\alpha,d})}",
            r"\label{eq:arbitrary-tail-proxy-positive-entropy-finite}",
            r"\label{cor:arbitrary-tail-defect-positive-moment-condition}",
            r"\label{cor:arbitrary-tail-defect-nonvacuousness}",
        )
        for text in required:
            self.assertIn(text, source)

    def test_active_tex_sources_obey_presentation_constraints(self) -> None:
        for path in ROOT.glob("*.tex"):
            source = path.read_text(encoding="utf-8")
            self.assertLess(
                len(source.splitlines()),
                800,
                f"{path.name} must remain below 800 lines",
            )
            self.assertNotRegex(source, r"(?i)TODO[^\n]*revision")

    def test_literature_audit_names_all_requested_indexes(self) -> None:
        audit = (ROOT / "artifacts" / "literature_check.md").read_text(
            encoding="utf-8"
        )
        for index in ("arXiv", "Crossref", "Semantic Scholar", "zbMATH"):
            self.assertIn(index, audit)
        self.assertIn("Ishige--Kawakami--Michihisa", audit)

    def test_named_problem_audit_records_printed_questions_and_status(self) -> None:
        audit = (ROOT / "artifacts" / "tier2_named_problem_audit.md").read_text(
            encoding="utf-8"
        )
        required = (
            "Johnson, Open Problem 1",
            "corresponding result for the MMSE score",
            "Johnson, Open Problem 4",
            "representation of $D(f \\Vert g_s^{(\\alpha)})$ as an integral",
            "Johnson, Open Problem 6",
            "more general (non-symmetric) families of stable laws",
            "No later source located",
            "Finite-variance Cauchy case proved",
        )
        for text in required:
            self.assertIn(text, audit)

    def test_cauchy_interpolation_integral_representation_is_complete(self) -> None:
        source = read_tex_source(ROOT / "sec_doob_phi_entropy.tex")
        required = (
            r"\label{thm:johnson-cauchy-integral-representation}",
            r"g_q=P_{q+s}=P_q*P_s",
            r"D_{\rm KL}(\mu\|P_s)",
            r"\int_0^\infty \mathcal J_{\mu,s}(q)\dd q",
            r"q=\frac{st}{1-t}",
            r"\frac{s}{(1-t)^2}",
            r"joint lower semicontinuity",
            r"data-processing inequality",
            r"\|u_q-1\|_\infty\longrightarrow0",
            r"Proposition~\ref{prop:compact-window-bregman-identity}",
        )
        for text in required:
            self.assertIn(text, source)

        intro = (ROOT / "sec_introduction.tex").read_text(encoding="utf-8")
        self.assertIn(r"Johnson's integral-representation problem", intro)
        self.assertNotIn(
            r"Theorem~\ref{thm:johnson-cauchy-integral-representation}", intro
        )
        self.assertIn(r"the finite-variance Cauchy statement proved in", intro)


if __name__ == "__main__":
    unittest.main()
