import unittest

from artifacts.verify_linear_collision_claims import (
    collision_jet_audit,
    odd_prime_realization_audit,
    squarefree_mahler_audit,
)


class LinearCollisionClaimTests(unittest.TestCase):
    def test_squarefree_mahler_bound_and_sharp_family(self):
        audit = squarefree_mahler_audit()
        self.assertEqual(audit["certificates_checked"], 2496)
        self.assertEqual(audit["sharp_cases"], 24)
        self.assertEqual(audit["minimum_slack"], 0)

    def test_collision_jet_inequality_on_positive_rational_cases(self):
        audit = collision_jet_audit()
        self.assertEqual(audit["positive_rational_cases"], 124)
        self.assertEqual(audit["constructed_collision_cases"], 12)

    def test_odd_prime_realization_identities(self):
        audit = odd_prime_realization_audit()
        self.assertEqual(audit["instances"], ((3, 1), (3, 2), (5, 1)))


if __name__ == "__main__":
    unittest.main()
