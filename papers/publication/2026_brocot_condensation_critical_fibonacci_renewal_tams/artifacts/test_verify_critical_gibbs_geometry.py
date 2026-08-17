#!/usr/bin/env python3
"""Tests for the critical Fibonacci Gibbs-geometry simulation."""

from __future__ import annotations

import math
import unittest

import numpy as np

from verify_critical_gibbs_geometry import (
    LetterSampler,
    negative_cf_cost,
    prediction_factor,
    sample_layer,
    sample_spectrally_positive_stable,
)


SIGMA_0 = 2.4787507857339603
ALPHA = SIGMA_0 - 1.0


class WeinsteinDefinitionsTest(unittest.TestCase):
    def test_negative_continued_fraction_costs(self) -> None:
        self.assertEqual(negative_cf_cost(1, 2), 3)
        self.assertEqual(negative_cf_cost(1, 3), 5)
        self.assertEqual(negative_cf_cost(2, 3), 5)
        self.assertEqual(negative_cf_cost(2, 5), 7)
        self.assertEqual(negative_cf_cost(3, 5), 7)

    def test_prediction_mutations_change_sign_and_mu_power(self) -> None:
        mu_c = 21.8
        t = 0.5
        theorem = prediction_factor(t, mu_c, ALPHA, "theorem")
        flipped = prediction_factor(t, mu_c, ALPHA, "flip-sign")
        wrong_mu = prediction_factor(t, mu_c, ALPHA, "mu-power")
        self.assertAlmostEqual(flipped, -theorem)
        self.assertAlmostEqual(abs(wrong_mu / theorem), mu_c)


class StableLawTest(unittest.TestCase):
    def test_sampler_matches_stated_characteristic_exponent(self) -> None:
        rng = np.random.default_rng(319_867)
        values = sample_spectrally_positive_stable(rng, ALPHA, 400_000)
        frequency = 0.35
        observed = np.mean(np.exp(1j * frequency * values))
        exponent = ALPHA * math.gamma(-ALPHA) * (-1j * frequency) ** ALPHA
        predicted = np.exp(exponent)
        self.assertLess(abs(observed - predicted), 0.008)


class FiniteLayerSamplerTest(unittest.TestCase):
    def test_m5_matches_exact_endpoint_and_word_masses(self) -> None:
        rng = np.random.default_rng(991_337)
        sampler = LetterSampler(rng, ALPHA, cap=6, batch_size=50_000)
        samples = sample_layer(rng, sampler, m=5, sample_count=120_000)

        b3 = 2.0 ** (-SIGMA_0)
        b5 = 2.0 * 3.0 ** (-SIGMA_0)
        normalizer = 1.0 + 2.0 * b3 + b5
        predicted = {
            0: 1.0 / normalizer,
            3: 2.0 * b3 / normalizer,
            5: b5 / normalizer,
        }
        for cost, probability in predicted.items():
            observed = np.mean(samples.cost == cost)
            self.assertLess(abs(observed - probability), 0.006)
        self.assertTrue(np.array_equal(samples.length, (samples.cost > 0).astype(int)))


if __name__ == "__main__":
    unittest.main()
