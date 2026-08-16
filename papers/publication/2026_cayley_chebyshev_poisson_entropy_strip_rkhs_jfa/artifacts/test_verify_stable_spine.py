from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[1]
INPUT_RE = re.compile(r"\\input\{([^}]+)\}")


def expand(path: Path, seen: set[Path] | None = None) -> str:
    seen = set() if seen is None else seen
    resolved = path.resolve()
    if resolved in seen:
        return ""
    seen.add(resolved)
    source = path.read_text(encoding="utf-8")

    def replace(match: re.Match[str]) -> str:
        child = ROOT / match.group(1)
        if child.suffix == "":
            child = child.with_suffix(".tex")
        return expand(child, seen)

    return INPUT_RE.sub(replace, source)


class StableResubmissionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.main = (ROOT / "main.tex").read_text(encoding="utf-8")
        cls.active = expand(ROOT / "main.tex")

    def test_active_graph_is_stable_only(self) -> None:
        required = (
            r"\input{sec_fractional_heat_relative_entropy}",
            r"\input{sec_verified_A2_results}",
            r"\input{sec_sharpness_poisson_application}",
            r"\input{sec_stable_convention_appendix}",
        )
        removed = (
            "sec_cayley_gate",
            "sec_haar_pullback",
            "sec_entropy_asymptotics",
            "sec_entropy_30_eighth_defect_layer",
            "sec_gram_space",
            "sec_strip_00_poisson_image",
            "sec_strip_20_symbol_sampling",
            "sec_strip_30_cardinal_observation",
        )
        for item in required:
            self.assertIn(item, self.main)
        for item in removed:
            self.assertNotIn(item, self.main)

    def test_no_supplement_or_relocation_interface_remains(self) -> None:
        self.assertNotIn(r"\relocatedproof", self.active)
        self.assertNotIn("Supplementary Material", self.active)
        self.assertNotIn("supplement", self.main.lower())

    def test_retained_flagship_results_are_present(self) -> None:
        for label in (
            "thm:two-stable-heat-flow-relative-entropy",
            "thm:high-dimensional-kl-moment-threshold",
            "thm:all-order-stable-first-unmatched-moment",
            "thm:abstract-positive-tail-jet-kernel",
            "thm:stable-arbitrary-order-law-by-law-decomposition",
        ):
            self.assertEqual(self.active.count(rf"\label{{{label}}}"), 1)

    def test_named_proof_chain_is_integrated(self) -> None:
        required = (
            "Stable critical translation remainder",
            "Two-background critical Bregman transfer",
            "Two-background KL perturbation",
            "Bounded-score translate entropy",
            "Moving-ball probability separation",
            "Annular fractional Green closure",
            "Abstract positive tail-jet kernel theorem",
        )
        for title in required:
            start = self.active.index(title)
            self.assertIn(r"\begin{proof}", self.active[start:])

    def test_abstract_has_requested_size_and_scope(self) -> None:
        abstract = self.main.split(r"\begin{abstract}", 1)[1].split(
            r"\end{abstract}", 1
        )[0]
        plain = re.sub(r"\\[A-Za-z]+(?:\[[^]]*\])?", " ", abstract)
        plain = re.sub(r"[^A-Za-z0-9-]+", " ", plain)
        words = [word for word in plain.split() if word]
        self.assertGreaterEqual(len(words), 200)
        self.assertLessEqual(len(words), 250)
        for excluded in (
            "Cayley",
            "Laurent",
            "rigidity",
            "Gaussian mechanism",
            "not claimed",
            "no uniqueness",
        ):
            self.assertNotIn(excluded, abstract)

    def test_critical_exponent_is_stated_verbatim(self) -> None:
        self.assertIn(
            r"\frac{2r(d+\alpha)}{d+\alpha+2r}",
            self.main + self.active,
        )

    def test_convention_machinery_is_reduced(self) -> None:
        self.assertIn("hard or a smooth fixed-scale retention", self.active)
        self.assertIn("additive or multiplicative normalization", self.active)
        for excluded in (
            "arbitrary measurable, nonradial",
            "Asymptotic coefficient rigidity inside",
            "infinite-dimensional family",
        ):
            self.assertNotIn(excluded, self.active)

    def test_active_numbering_is_automatic(self) -> None:
        self.assertNotRegex(self.active, r"\\tag\s*\{")
        self.assertNotRegex(self.active, r"\\setcounter\s*\{")

    def test_all_tex_sources_stay_below_limit(self) -> None:
        for path in ROOT.glob("*.tex"):
            self.assertLess(
                len(path.read_text(encoding="utf-8").splitlines()),
                800,
                path.name,
            )


if __name__ == "__main__":
    unittest.main()
