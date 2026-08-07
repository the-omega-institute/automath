import unittest

import numpy as np

from verify_general_sft_rigidity import (
    asymptotic_information_variance,
    example_adjacencies,
    parry_transition,
    run_counterexample_search,
)


class GeneralSFTRigidityVerificationTests(unittest.TestCase):
    def test_parry_variance_vanishes_for_every_example(self):
        for name, adjacency in example_adjacencies().items():
            with self.subTest(name=name):
                transition, _ = parry_transition(adjacency)
                variance = asymptotic_information_variance(transition, adjacency)
                self.assertLessEqual(abs(variance), 1.0e-12)

    def test_explicit_non_parry_chains_have_positive_variance(self):
        adjacency = example_adjacencies()["golden_mean_k2"]
        transition = np.array([[0.7, 0.3], [1.0, 0.0]])
        variance = asymptotic_information_variance(transition, adjacency)
        self.assertGreater(variance, 1.0e-8)

    def test_seeded_counterexample_search_is_clean(self):
        report = run_counterexample_search(samples_per_shift=40, seed=20260801)
        self.assertEqual(report.failures, 0)
        self.assertEqual(report.counterexamples, 0)
        self.assertEqual(report.mme_zero_confirmations, 4)
        self.assertEqual(report.non_mme_positive_confirmations, 160)


if __name__ == "__main__":
    unittest.main()
