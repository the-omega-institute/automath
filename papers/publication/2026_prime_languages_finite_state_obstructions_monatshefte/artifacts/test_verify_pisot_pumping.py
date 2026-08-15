import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from artifacts import verify_pisot_pumping as verifier


class PisotPumpingVerifierTests(unittest.TestCase):
    def test_report_rejects_archived_count_drift(self):
        report = verifier.run_verification()
        report["systems_checked"] -= 1

        with self.assertRaisesRegex(RuntimeError, "systems_checked"):
            verifier._format_report(report)

    def test_report_records_reproducibility_provenance(self):
        report = verifier._format_report(verifier.run_verification())

        self.assertIn("script version:", report)
        self.assertIn("script SHA-256:", report)
        self.assertIn("Python version:", report)
        self.assertIn(
            "command: python artifacts/verify_pisot_pumping.py",
            report,
        )
        self.assertIn("random seed: none (deterministic)", report)

    def test_cli_writes_the_archived_report(self):
        with tempfile.TemporaryDirectory() as temporary_directory:
            output_path = Path(temporary_directory) / "verification.txt"
            completed = subprocess.run(
                [
                    sys.executable,
                    str(Path(verifier.__file__)),
                    "--output",
                    str(output_path),
                ],
                check=True,
                capture_output=True,
                text=True,
            )

            self.assertEqual(completed.stdout, "")
            archived = output_path.read_text(encoding="utf-8")
            self.assertIn("systems checked: 6", archived)
            self.assertIn("affine action cases: 2282", archived)
            self.assertTrue(archived.endswith("OVERALL: PASS\n"))

    def test_evertse_support_gives_uniform_prime_ideal_norm_bound(self):
        self.assertEqual(
            verifier.evertse_prime_ideal_norm_bound((2, 3, 5), 4),
            5**4,
        )
        self.assertEqual(
            verifier.evertse_prime_ideal_norm_bound((), 7),
            1,
        )

    def test_linear_perron_decision_accepts_exactly_integer_bases(self):
        decisions = {
            system.name: verifier.has_bounded_outside_support_mcfl(system)
            for system in verifier.SYSTEMS
        }

        self.assertEqual(
            decisions,
            {
                "fibonacci": False,
                "pell": False,
                "tribonacci": False,
                "quadratic_nonunit": False,
                "quadratic_perron_nonpisot": False,
                "integer_base_2": True,
            },
        )

    def test_nonpisot_perron_example_is_strictly_increasing(self):
        system = verifier.system_by_name("quadratic_perron_nonpisot")

        self.assertEqual(system.polynomial, "x^2-5x+5")
        self.assertEqual(
            verifier.weights(system, 8),
            [1, 4, 15, 55, 200, 725, 2625, 9500],
        )

    def test_nonintegral_weak_perron_mixed_radix_family(self):
        self.assertTrue(hasattr(verifier, "mixed_radix_weak_perron_system"))
        for left_radix, right_radix in ((2, 3), (2, 5), (3, 5)):
            with self.subTest(radices=(left_radix, right_radix)):
                system = verifier.mixed_radix_weak_perron_system(
                    left_radix, right_radix
                )
                product_radix = left_radix * right_radix
                expected_weights = [
                    product_radix ** (index // 2)
                    * (left_radix if index % 2 else 1)
                    for index in range(10)
                ]
                self.assertEqual(verifier.weights(system, 10), expected_weights)
                self.assertEqual(system.recurrence, (product_radix, 0))
                self.assertEqual(
                    [
                        verifier.value(system, (0,) * (2 * exponent) + (1,))
                        for exponent in range(6)
                    ],
                    [product_radix**exponent for exponent in range(6)],
                )

    def test_increasing_selection_needs_only_distinct_positive_values(self):
        self.assertTrue(hasattr(verifier, "select_increasing_return"))
        values = (10, 5, 7, 1, 9, 2, 16)

        self.assertEqual(
            verifier.select_increasing_return(values, start_index=0, return_time=2),
            6,
        )

    def test_geometric_ratio_uses_only_tail_primes(self):
        self.assertIsNone(
            verifier.geometric_ratio_support_obstruction(
                trailing_coefficient=2, initial_factor=5, ratio=8
            )
        )
        obstruction = verifier.geometric_ratio_support_obstruction(
            trailing_coefficient=2, initial_factor=5, ratio=6
        )
        self.assertEqual(
            obstruction,
            {
                "prime": 3,
                "modulus": 3,
                "initial_valuation": 0,
            },
        )
        self.assertEqual(
            verifier.geometric_ratio_support_obstruction(
                trailing_coefficient=1, initial_factor=12, ratio=2
            ),
            {"prime": 2, "modulus": 8, "initial_valuation": 2},
        )

    def test_tail_action_starts_after_the_eventual_recurrence_transient(self):
        recurrence = (-10, 7)
        weights = (1, 3, 6, 12, 24, 48, 96, 192)
        prefix = (2,)

        for suffix_length in range(6):
            for suffix_number in range(1 << suffix_length):
                suffix = tuple(
                    (suffix_number >> index) & 1
                    for index in range(suffix_length)
                )
                transformed = verifier.tail_action_state(
                    recurrence, weights, prefix, suffix
                )
                full_word = prefix + suffix
                expected = (
                    sum(
                        digit * weight
                        for digit, weight in zip(full_word, weights)
                    ),
                    *weights[len(full_word) : len(full_word) + len(recurrence)],
                )
                self.assertEqual(transformed, expected)

    def test_explicit_linear_mcfg_ray_realizes_a_geometric_base_two_orbit(self):
        base_two = verifier.system_by_name("integer_base_2")
        values = []
        for exponent in range(13):
            word = verifier.linear_mcfg_ray_word(
                prefix=(),
                constants=((), (1,)),
                left_pumps=((0,),),
                middles=((),),
                right_pumps=((),),
                exponent=exponent,
            )
            self.assertEqual(word, (0,) * exponent + (1,))
            values.append(verifier.value(base_two, word))

        self.assertEqual(values, [2**exponent for exponent in range(13)])

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
        self.assertEqual(report["systems_checked"], 6)
        self.assertEqual(report["affine_cases"], 2282)
        self.assertEqual(report["pump_witnesses"], 5)
        self.assertEqual(report["congruence_failures"], 0)
        self.assertEqual(report["counterexample"]["modulus"], 2)
        self.assertEqual(report["synchronized_orbit_cases"], 159)
        self.assertEqual(report["local_layer_isolation_failures"], 0)
        self.assertEqual(report["deep_chain_failures"], 0)
        self.assertEqual(report["divisibility_tree_failures"], 0)
        self.assertEqual(report["inflated_fibonacci_cases"], 1418)
        self.assertEqual(report["inflated_fibonacci_failures"], 0)
        self.assertEqual(report["tail_prefix_cases"], 63)
        self.assertEqual(report["tail_prefix_failures"], 0)
        self.assertEqual(report["geometric_ray_cases"], 13)
        self.assertEqual(report["geometric_ray_failures"], 0)
        self.assertEqual(report["linear_perron_classification_cases"], 6)
        self.assertEqual(report["linear_perron_classification_failures"], 0)
        self.assertIn("weak_perron_radical_cases", report)
        self.assertEqual(report["weak_perron_radical_cases"], 18)
        self.assertEqual(report["weak_perron_radical_failures"], 0)
        self.assertIn("length_order_free_selection_cases", report)
        self.assertEqual(report["length_order_free_selection_cases"], 1)
        self.assertEqual(report["length_order_free_selection_failures"], 0)
        self.assertEqual(report["geometric_ratio_support_cases"], 4)
        self.assertEqual(report["geometric_ratio_support_failures"], 0)
        self.assertEqual(report["evertse_support_bound_cases"], 4)
        self.assertEqual(report["evertse_support_bound_failures"], 0)

    def test_inflated_fibonacci_has_unit_reachable_action(self):
        report = verifier.verify_inflated_fibonacci_separation(
            primes=(2, 3, 5, 7, 11, 13),
            maximum_power=4,
            maximum_index=24,
        )
        self.assertGreater(report["cases"], 100)
        self.assertEqual(report["failures"], 0)
        self.assertEqual(report["reachable_rank"], 2)
        self.assertEqual(report["reachable_determinant"], -1)

    def test_synchronized_multi_block_orbit_for_all_tested_parameters(self):
        fibonacci = verifier.system_by_name("fibonacci")
        word = (0, 1, 0, 0, 0, 0, 1)
        spans = ((2, 3), (4, 5))
        cases = verifier.check_synchronized_orbit(
            fibonacci,
            word,
            spans,
            moduli=range(2, 21),
            parameters=range(6),
        )
        self.assertEqual(cases, 19 * 6)

        nonunit = verifier.system_by_name("quadratic_nonunit")
        with self.assertRaises(verifier.NonInvertibleAction):
            verifier.check_synchronized_orbit(
                nonunit,
                (1, 0, 0, 1),
                ((1, 2), (2, 3)),
                moduli=(2,),
                parameters=(0,),
            )

    def test_local_layer_isolation_certificate(self):
        n = 2 * 3 * 5**2 * 7
        excluded_primes = (2, 3)
        valuation_bounds = {2: 2, 3: 1}
        modulus = verifier.local_layer_isolation_modulus(
            n, excluded_primes, valuation_bounds
        )
        self.assertEqual(verifier.omega_outside(n, excluded_primes), 2)
        self.assertEqual(verifier.gcd(modulus, 2 * 3), 1)

        congruent_layer_points = [
            m
            for m in range(1, 50_001)
            if verifier.in_local_prime_layer(
                m, 2, excluded_primes, valuation_bounds
            )
            and (m - n) % modulus == 0
        ]
        self.assertEqual(congruent_layer_points, [n])

    def test_deep_chain_has_prescribed_congruence_depth(self):
        specifications = ((6, 1), (30, 2), (210, 1))
        chain = verifier.construct_deep_congruence_chain(2, specifications)
        for current, following, (modulus_factor, depth) in zip(
            chain, chain[1:], specifications
        ):
            quotient = following // current
            self.assertGreater(quotient, 1)
            self.assertEqual(following % current, 0)
            self.assertEqual(
                quotient % (modulus_factor * current**depth), 1
            )

    def test_finite_divisibility_tree_is_induced_and_has_coprime_edges(self):
        nodes = ((), (0,), (1,), (0, 0), (0, 1), (1, 0))
        thresholds = {
            (0,): 3,
            (1,): 5,
            (0, 0): 7,
            (0, 1): 11,
            (1, 0): 13,
        }
        values, edge_quotients = verifier.construct_divisibility_tree(
            root=2, nodes=nodes, thresholds=thresholds
        )
        for left in nodes:
            for right in nodes:
                self.assertEqual(
                    values[right] % values[left] == 0,
                    right[: len(left)] == left,
                )
        quotients = list(edge_quotients.values())
        for index, left in enumerate(quotients):
            for right in quotients[index + 1 :]:
                self.assertEqual(verifier.gcd(left, right), 1)
        for edge, quotient in edge_quotients.items():
            for prime in range(2, thresholds[edge] + 1):
                if verifier.is_prime(prime):
                    self.assertNotEqual(quotient % prime, 0)


if __name__ == "__main__":
    unittest.main()
