import unittest

from artifacts.verify_twisted_determinant_rigidity import (
    BaseGraph,
    cyclic_group,
    s3_group,
    determinant_signature,
    gauge_transform,
    minimal_counterexample_search,
    periodic_class_profile,
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


if __name__ == "__main__":
    unittest.main()
