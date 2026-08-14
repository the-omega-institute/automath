from __future__ import annotations

import subprocess
import sys
import re
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CERTIFICATE = ROOT / "artifacts" / "verify_oracle_A2.py"
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


class OracleA2VerificationTests(unittest.TestCase):
    def test_stable_kernel_exponent_and_claim_interface(self) -> None:
        completed = subprocess.run(
            [sys.executable, str(CERTIFICATE), "--quick"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        self.assertIn("stable-kernel critical exponent algebra", completed.stdout)
        self.assertIn("critical Bregman perturbation bound including q=2", completed.stdout)

        manuscript = read_tex_source(ROOT / "sec_verified_A2_results.tex")
        self.assertIn(r"\label{lem:stable-critical-translation-remainder}", manuscript)
        self.assertIn("Optimal uniform sufficient moment exponent", manuscript)
        self.assertNotIn("[Sharp high-dimensional KL moment threshold]", manuscript)

    def test_all_order_stable_first_unmatched_interface(self) -> None:
        completed = subprocess.run(
            [sys.executable, str(CERTIFICATE), "--quick"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        self.assertIn("all-order stable critical exponent algebra", completed.stdout)
        self.assertIn("finite-difference moment-cancellation blocks", completed.stdout)
        self.assertIn("global cosine Taylor remainder sign", completed.stdout)
        self.assertIn("two-background critical Bregman transfer stress", completed.stdout)
        self.assertIn("fourth-moment-matched KL constant", completed.stdout)

        manuscript = read_tex_source(ROOT / "sec_verified_A2_results.tex")
        self.assertIn(
            r"\label{lem:two-background-critical-bregman-transfer}",
            manuscript,
        )
        self.assertIn(
            r"\label{thm:all-order-stable-first-unmatched-moment}",
            manuscript,
        )
        self.assertIn(
            r"\label{cor:stable-gaussian-quadrature-threshold}",
            manuscript,
        )
        self.assertIn(r"q_{r,\alpha,d}", manuscript)
        self.assertIn(r"p_{r,\alpha,d}", manuscript)
        self.assertIn(r"let \(r\ge1\) be an integer", manuscript)
        self.assertIn(r"\label{lem:stable-finite-difference-blocks}", manuscript)
        self.assertIn(
            r"\label{lem:stable-moving-ball-probability-separation}",
            manuscript,
        )
        self.assertIn(r"\label{lem:bernoulli-kl-linear-separation}", manuscript)

    def test_certificate_and_manuscript_labels(self) -> None:
        completed = subprocess.run(
            [sys.executable, str(CERTIFICATE), "--quick"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        self.assertIn("first-mode Laplace resolvent identity", completed.stdout)
        self.assertIn("critical Lq translation identity", completed.stdout)
        self.assertIn("critical Bregman perturbation bound", completed.stdout)
        self.assertIn("covariance-proxy KL chain identity", completed.stdout)
        self.assertIn("finite-covariance proxy asymptotic stress", completed.stdout)
        self.assertIn("raw-tail Poisson energy decomposition stress", completed.stdout)
        self.assertIn("moving-annulus potential comparability", completed.stdout)
        self.assertIn("pre-Phi thin-shell aggregation scaling", completed.stdout)

        manuscript = "\n".join(
            read_tex_source(ROOT / name)
            for name in (
                "sec_verified_A2_results.tex",
                "sec_covariance_proxy_defect.tex",
            )
        )
        for label in (
            "thm:first-cayley-mode-closure",
            "thm:moment-matched-poisson-kl",
            "thm:gauss-poisson-kl-threshold",
            "cor:two-node-gauss-fourth-moment",
            "thm:gauss-regular-variation-square-law",
            "thm:low-dimensional-finite-covariance-threshold",
            "thm:multidim-l2-moment-threshold",
            "prop:high-dimensional-finite-covariance-obstruction",
            "lem:critical-lq-translation-remainder",
            "lem:critical-lq-kl-perturbation",
            "thm:high-dimensional-kl-moment-threshold",
            "lem:finite-covariance-fatou-lower-bound",
            "thm:critical-vague-tail-nonidentifiability",
            "thm:finite-covariance-proxy-defect-decomposition",
            "cor:critical-rv-proxy-characterization",
            "thm:raw-tail-poisson-energy-decomposition",
            "cor:moving-annulus-tail-criterion",
            "prop:pre-phi-thin-shell-aggregation",
        ):
            self.assertIn(r"\label{" + label + "}", manuscript)


if __name__ == "__main__":
    unittest.main()
