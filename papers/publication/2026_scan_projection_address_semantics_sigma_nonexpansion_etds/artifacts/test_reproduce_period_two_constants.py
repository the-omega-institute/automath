import subprocess
import sys
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("reproduce_period_two_constants.py")


class ReproductionScriptTest(unittest.TestCase):
    def test_prints_phase_resolved_values_and_phase_blind_control(self):
        self.assertTrue(SCRIPT.is_file(), f"missing reproduction script: {SCRIPT}")

        completed = subprocess.run(
            [sys.executable, str(SCRIPT)],
            check=False,
            capture_output=True,
            text=True,
        )

        self.assertEqual(completed.returncode, 0, completed.stderr)
        for expected_line in (
            "rho_1 = 1/2",
            "rho_2 = sqrt(5)/12",
            "A_1,0(1) = 53/89",
            "A_1,1(1) = 52/89",
            "A_2,0(1) = 953/7921",
            "A_2,1(1) = 2136/(7921*sqrt(5))",
            "c_2,0 = 953/2809",
            "c_2,1 = 267/(338*sqrt(5))",
            "h_2,H = log(3*sqrt(5)/5)",
            "phase-blind c_2 = 2*(4765 + 2136*sqrt(5))/55125",
            "phase-blind phase 0 = phase-blind phase 1: True",
            "phase-resolved constants distinct: True",
        ):
            self.assertIn(expected_line, completed.stdout)


if __name__ == "__main__":
    unittest.main()
