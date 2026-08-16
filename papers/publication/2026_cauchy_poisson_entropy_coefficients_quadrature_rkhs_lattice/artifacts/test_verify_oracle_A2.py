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
    def test_cauchy_coefficient_interface(self) -> None:
        completed = subprocess.run(
            [sys.executable, str(CERTIFICATE), "--quick"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        self.assertIn("pointwise Cayley-mode differential recurrence", completed.stdout)
        self.assertIn("first-mode Laplace resolvent identity", completed.stdout)

        manuscript = read_tex_source(ROOT / "sec_verified_A2_results.tex")
        self.assertIn(r"\label{thm:first-cayley-mode-closure}", manuscript)
        self.assertIn(r"\label{thm:moment-matched-poisson-kl}", manuscript)

    def test_gaussian_quadrature_interface(self) -> None:
        completed = subprocess.run(
            [sys.executable, str(CERTIFICATE), "--quick"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        self.assertIn("two-node Gauss fourth-moment KL constant", completed.stdout)
        self.assertIn("fourth-moment-matched KL constant", completed.stdout)

        manuscript = read_tex_source(ROOT / "sec_verified_A2_results.tex")
        self.assertIn(r"\label{thm:gauss-poisson-kl-threshold}", manuscript)
        self.assertIn(r"\label{cor:two-node-gauss-fourth-moment}", manuscript)
        self.assertIn(r"\label{thm:gauss-regular-variation-square-law}", manuscript)

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
            "thm:finite-covariance-proxy-defect-decomposition",
            "cor:critical-rv-proxy-characterization",
            "thm:raw-tail-poisson-energy-decomposition",
            "cor:moving-annulus-tail-criterion",
            "prop:pre-phi-thin-shell-aggregation",
        ):
            self.assertIn(r"\label{" + label + "}", manuscript)


if __name__ == "__main__":
    unittest.main()
