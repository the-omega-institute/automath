import unittest

from artifacts import verify_pisot_pumping as verifier


class PisotPumpingVerifierTests(unittest.TestCase):
    def test_affine_action_matches_direct_evaluation(self):
        for system in verifier.SYSTEMS:
            with self.subTest(system=system.name):
                verifier.check_affine_action(system, max_length=7)

    def test_two_block_return_gives_square_modulus_congruence(self):
        fib = verifier.system_by_name("fibonacci")
        word = (0, 1, 0, 0, 0, 0, 1)  # 23 in LSD-first Zeckendorf form
        witness = verifier.verify_pump_witness(
            fib,
            word,
            cuts=(2, 3, 4, 5),
            require_canonical=True,
        )
        self.assertEqual(witness.original_value, 23)
        self.assertGreater(witness.pump_exponent, 1)
        self.assertEqual(witness.pumped_value % (23 * 23), 23)
        self.assertGreater(witness.pumped_value, 23)
        self.assertEqual(witness.pumped_value // 23 % 23, 1)

    def test_nonunit_bad_prime_is_rejected(self):
        nonunit = verifier.system_by_name("quadratic_nonunit")
        with self.assertRaises(verifier.NonInvertibleAction):
            verifier.matrix_order(
                verifier.block_matrix(nonunit, (0,)), modulus=2
            )

    def test_counterexample_search_finds_required_hypothesis(self):
        witness = verifier.search_singular_counterexample()
        self.assertEqual(witness["system"], "quadratic_nonunit")
        self.assertEqual(witness["modulus"], 2)
        self.assertEqual(witness["trailing_coefficient"], 2)
        self.assertFalse(witness["invertible"])

    def test_full_verification_suite_has_no_congruence_failures(self):
        report = verifier.run_verification()
        self.assertGreaterEqual(report["systems_checked"], 5)
        self.assertGreater(report["affine_cases"], 100)
        self.assertGreater(report["pump_witnesses"], 0)
        self.assertEqual(report["congruence_failures"], 0)
        self.assertEqual(report["counterexample"]["modulus"], 2)


if __name__ == "__main__":
    unittest.main()
