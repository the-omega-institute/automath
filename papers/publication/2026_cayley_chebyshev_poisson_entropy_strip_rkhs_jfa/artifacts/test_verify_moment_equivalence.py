import unittest

try:
    from . import verify_moment_equivalence as v
except ImportError:  # Direct execution from the artifacts directory.
    import verify_moment_equivalence as v


class MomentEquivalenceVerificationTests(unittest.TestCase):
    def test_known_coefficients(self):
        moments = {2: 2.0, 3: 0.0, 4: 24.0}
        self.assertAlmostEqual(v.entropy_coefficient(2, moments), 0.5)
        self.assertAlmostEqual(v.entropy_coefficient(3, moments), -5.875)

    def test_numeric_battery_and_counterexample_search(self):
        report = v.run_battery(quick=True)
        self.assertEqual(report["failed_checks"], [])
        self.assertEqual(report["counterexamples"], [])
        self.assertGreaterEqual(report["orders_checked"], 3)


if __name__ == "__main__":
    unittest.main()
