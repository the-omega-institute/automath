from __future__ import annotations

import subprocess
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CERTIFICATE = ROOT / "artifacts" / "verify_oracle_A2.py"


class OracleA2VerificationTests(unittest.TestCase):
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

        manuscript = (ROOT / "sec_verified_A2_results.tex").read_text(encoding="utf-8")
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
        ):
            self.assertIn(r"\label{" + label + "}", manuscript)


if __name__ == "__main__":
    unittest.main()
