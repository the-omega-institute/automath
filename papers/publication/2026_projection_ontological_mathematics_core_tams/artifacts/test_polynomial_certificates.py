import subprocess
import sys
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("verify_polynomial_certificates.py")


class PolynomialCertificateTest(unittest.TestCase):
    def test_negative_control_rejects_one_wrong_pi_9_coefficient(self):
        completed = subprocess.run(
            [sys.executable, str(SCRIPT), "--negative-control"],
            check=False,
            capture_output=True,
            text=True,
        )

        self.assertEqual(completed.returncode, 1, completed.stdout + completed.stderr)
        self.assertIn(
            "NEGATIVE CONTROL  claimed Pi_9 coefficient of x^5: -62 -> -61",
            completed.stdout,
        )
        self.assertIn(
            "CHECK  modular certificates for unmodified Pi_10..Pi_17: PASS",
            completed.stdout,
        )
        self.assertIn(
            "CHECK  discriminant Legendre values and rank_mod_two == 4: PASS",
            completed.stdout,
        )
        self.assertIn(
            "CLAIM CHECK  modular certificates for mutated Pi_9: FAIL",
            completed.stdout,
        )


if __name__ == "__main__":
    unittest.main()
