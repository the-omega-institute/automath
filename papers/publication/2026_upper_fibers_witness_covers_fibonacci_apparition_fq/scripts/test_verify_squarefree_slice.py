#!/usr/bin/env python3
"""Regression tests for the squarefree-fiber and sharpness verifier."""

import itertools
import unittest

try:
    from .verify_squarefree_slice import (
        extremal_full_support_profile,
        ladder_obstruction_criterion,
        minimal_covers,
        rank_pure_products,
        sharp_mass_lower_bound,
        squarefree_minimal_generators,
        verify_ladder_obstruction,
        weighted_cover_partition,
    )
except ImportError:
    from verify_squarefree_slice import (
        extremal_full_support_profile,
        ladder_obstruction_criterion,
        minimal_covers,
        rank_pure_products,
        sharp_mass_lower_bound,
        squarefree_minimal_generators,
        verify_ladder_obstruction,
        weighted_cover_partition,
    )


class SquarefreeSliceTests(unittest.TestCase):
    def test_every_nonempty_subset_occurs_in_a_minimal_cover(self):
        for size in range(1, 5):
            vertex_set = frozenset(range(size))
            covers = minimal_covers(size)
            for subset_size in range(1, size + 1):
                for subset in itertools.combinations(vertex_set, subset_size):
                    self.assertTrue(
                        any(frozenset(subset) in cover for cover in covers)
                    )

    def test_sharp_mass_bound_for_small_integer_profiles(self):
        for size in range(1, 4):
            subsets = tuple(
                subset
                for subset_size in range(1, size + 1)
                for subset in map(frozenset, itertools.combinations(range(size), subset_size))
            )
            baseline_mass = len(subsets)
            for excess_locations in itertools.product(range(len(subsets)), repeat=3):
                weights = {subset: 1 for subset in subsets}
                for location in excess_locations:
                    weights[subsets[location]] += 1
                partition = weighted_cover_partition(size, weights)
                self.assertGreaterEqual(
                    partition,
                    sharp_mass_lower_bound(size, baseline_mass + 3),
                )

    def test_full_support_profile_attains_the_bound(self):
        for size in range(1, 5):
            baseline_mass = 2**size - 1
            for excess in (0, 1, 5, 17):
                total_mass = baseline_mass + excess
                weights = extremal_full_support_profile(size, total_mass)
                self.assertEqual(
                    weighted_cover_partition(size, weights),
                    sharp_mass_lower_bound(size, total_mass),
                )

    def test_equality_profile_is_unique_from_k_three(self):
        excess = 3
        for size in (3, 4):
            subsets = tuple(
                subset
                for subset_size in range(1, size + 1)
                for subset in map(frozenset, itertools.combinations(range(size), subset_size))
            )
            full_support = frozenset(range(size))
            lower_bound = sharp_mass_lower_bound(size, len(subsets) + excess)
            equality_profiles = set()
            for excess_locations in itertools.combinations_with_replacement(
                range(len(subsets)), excess
            ):
                weights = {subset: 1 for subset in subsets}
                for location in excess_locations:
                    weights[subsets[location]] += 1
                if weighted_cover_partition(size, weights) == lower_bound:
                    equality_profiles.add(tuple(weights[subset] for subset in subsets))
            expected = {tuple(1 + excess if subset == full_support else 1 for subset in subsets)}
            self.assertEqual(equality_profiles, expected)

        size = 2
        subsets = tuple(
            subset
            for subset_size in range(1, size + 1)
            for subset in map(frozenset, itertools.combinations(range(size), subset_size))
        )
        singleton_profile = {subset: 1 for subset in subsets}
        singleton_profile[frozenset({0})] += excess
        self.assertEqual(
            weighted_cover_partition(size, singleton_profile),
            sharp_mass_lower_bound(size, len(subsets) + excess),
        )

    def test_rank_pure_products_equal_squarefree_minima(self):
        squarefree_indices = (
            3,
            5,
            6,
            7,
            10,
            15,
            21,
            30,
            35,
            42,
            55,
            66,
            70,
            78,
            105,
        )
        for n in squarefree_indices:
            with self.subTest(n=n):
                self.assertEqual(
                    rank_pure_products(n),
                    squarefree_minimal_generators(n),
                )

    def test_squarefree_fiber_criterion_boundary_cases(self):
        obstructed = (6, 12, 25, 30, 36, 50, 91, 125)
        unobstructed = (9, 15, 20, 49, 98, 147)
        for n in obstructed:
            with self.subTest(n=n):
                self.assertTrue(ladder_obstruction_criterion(n))
                self.assertGreater(verify_ladder_obstruction(n), 0)
        for n in unobstructed:
            with self.subTest(n=n):
                self.assertFalse(ladder_obstruction_criterion(n))
                self.assertEqual(verify_ladder_obstruction(n), 0)

    def test_verifier_rejects_a_mutated_criterion(self):
        with self.assertRaisesRegex(AssertionError, "ladder criterion failed at n=91"):
            verify_ladder_obstruction(91, obstruction_test=lambda _: False)


if __name__ == "__main__":
    unittest.main(verbosity=2)
