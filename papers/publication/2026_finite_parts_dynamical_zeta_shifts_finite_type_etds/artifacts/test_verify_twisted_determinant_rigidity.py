import unittest
from itertools import product
from math import factorial

from artifacts.verify_twisted_determinant_rigidity import (
    BaseGraph,
    abelian_bouquet_necessity_audit,
    bouquet_predicted_fiber_size,
    bouquet_swap_collision,
    cyclic_group,
    determinant_cohomology_multiplicity,
    s3_group,
    determinant_signature,
    first_marked_periodic_witness,
    fourier_recovered_multiplicities,
    gauge_transform,
    label_multiplicities,
    minimal_counterexample_search,
    perron_boundary_signature,
    periodic_class_profile,
    regular_skew_adjacency,
    is_primitive_nonnegative,
)


class TwistedDeterminantRigidityTests(unittest.TestCase):
    def test_minimal_z2_pair_has_equal_exact_determinants(self):
        graph = BaseGraph.full_shift(2)
        group = cyclic_group(2)
        tau = (0, 1)
        tau_prime = (1, 0)

        self.assertEqual(
            determinant_signature(graph, group, tau),
            ("1 - 2*z", "1"),
        )
        self.assertEqual(
            determinant_signature(graph, group, tau),
            determinant_signature(graph, group, tau_prime),
        )
        self.assertNotEqual(
            periodic_class_profile(graph, group, tau, 1, marked=True),
            periodic_class_profile(graph, group, tau_prime, 1, marked=True),
        )

    def test_s3_vertex_gauge_preserves_every_determinant(self):
        graph = BaseGraph.golden_mean()
        group = s3_group()
        identity, transposition, cycle = group.named_elements(
            "()", "(12)", "(123)"
        )
        tau = (identity, transposition, cycle)
        transfer = (transposition, cycle)
        tau_prime = gauge_transform(graph, group, tau, transfer)

        self.assertNotEqual(tau, tau_prime)
        self.assertEqual(
            determinant_signature(graph, group, tau),
            determinant_signature(graph, group, tau_prime),
        )

    def test_search_proves_the_two_loop_z2_example_is_minimal(self):
        result = minimal_counterexample_search()

        self.assertEqual(result.group_order, 2)
        self.assertEqual(result.vertex_count, 1)
        self.assertEqual(result.edge_count, 2)
        self.assertEqual(result.tau, (0, 1))
        self.assertEqual(result.tau_prime, (1, 0))
        self.assertEqual(result.marked_witness_length, 1)
        self.assertTrue(result.base_extension_primitive)
        self.assertTrue(result.all_twisted_blocks_semisimple)

    def test_fourier_inversion_recovers_abelian_bouquet_multiplicities(self):
        group = cyclic_group(3)
        tau = (0, 1, 1, 2)

        self.assertEqual(label_multiplicities(group, tau), (1, 2, 1))
        self.assertEqual(fourier_recovered_multiplicities(group, tau), (1, 2, 1))

    def test_multinomial_formula_is_the_exact_determinant_fiber_size(self):
        graph = BaseGraph.full_shift(3)
        group = cyclic_group(3)
        fibers = {}
        for tau in product(group.elements, repeat=3):
            fibers.setdefault(determinant_signature(graph, group, tau), []).append(tau)

        for fiber in fibers.values():
            for tau in fiber:
                counts = label_multiplicities(group, tau)
                expected = factorial(3)
                for count in counts:
                    expected //= factorial(count)
                self.assertEqual(bouquet_predicted_fiber_size(group, tau), expected)
                self.assertEqual(len(fiber), expected)
                self.assertEqual(
                    determinant_cohomology_multiplicity(graph, group, tau),
                    expected,
                )

    def test_every_nonconstant_abelian_bouquet_labeling_has_swap_collision(self):
        graph = BaseGraph.full_shift(3)
        group = cyclic_group(3)
        checked = 0
        for tau in product(group.elements, repeat=3):
            if len(set(tau)) == 1:
                continue
            tau_prime = bouquet_swap_collision(tau)
            self.assertNotEqual(tau, tau_prime)
            self.assertEqual(
                determinant_signature(graph, group, tau),
                determinant_signature(graph, group, tau_prime),
            )
            self.assertIsNotNone(
                first_marked_periodic_witness(graph, group, tau, tau_prime, 1)
            )
            checked += 1
        self.assertEqual(checked, 24)

    def test_perron_boundary_does_not_determine_rigidity_multiplicity(self):
        graph = BaseGraph.full_two_vertex()
        group = cyclic_group(2)
        colliding = (0, 0, 0, 1)
        rigid = (0, 0, 1, 0)

        self.assertTrue(
            is_primitive_nonnegative(regular_skew_adjacency(graph, group, colliding))
        )
        self.assertTrue(
            is_primitive_nonnegative(regular_skew_adjacency(graph, group, rigid))
        )
        self.assertEqual(
            perron_boundary_signature(graph, group, colliding),
            perron_boundary_signature(graph, group, rigid),
        )
        self.assertEqual(perron_boundary_signature(graph, group, rigid), ("2",))
        self.assertEqual(
            determinant_cohomology_multiplicity(graph, group, colliding), 2
        )
        self.assertEqual(determinant_cohomology_multiplicity(graph, group, rigid), 1)

    def test_complete_bouquet_necessity_audit_has_no_failures(self):
        audit = abelian_bouquet_necessity_audit(
            BaseGraph.full_shift(3), cyclic_group(3)
        )

        self.assertEqual(audit.cocycles, 27)
        self.assertEqual(audit.rigid_cocycles, 3)
        self.assertEqual(audit.nonrigid_cocycles, 24)
        self.assertEqual(audit.formula_failures, 0)
        self.assertEqual(audit.collision_failures, 0)


if __name__ == "__main__":
    unittest.main()
