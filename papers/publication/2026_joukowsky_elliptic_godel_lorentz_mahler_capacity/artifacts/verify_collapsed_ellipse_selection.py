#!/usr/bin/env python3
"""Numerical checks for the collapsed-ellipse opening-selection theorem."""

from __future__ import annotations

import argparse
import math

import numpy as np


def direct_energy(
    s: float,
    density,
    *,
    grid_size: int = 2048,
    block_size: int = 128,
) -> float:
    """Staggered product quadrature for I(J_{exp(s)*} eta)."""
    indices = np.arange(grid_size, dtype=float)
    theta = 2.0 * math.pi * (indices + 0.25) / grid_size
    phi = 2.0 * math.pi * (indices + 0.625) / grid_size
    z_theta = np.exp(1j * theta)
    z_phi = np.exp(1j * phi)
    radius = math.exp(s)
    image_theta = radius * z_theta + radius**-1 / z_theta
    image_phi = radius * z_phi + radius**-1 / z_phi
    weight_theta = density(theta)
    weight_phi = density(phi)

    total = 0.0
    for start in range(0, grid_size, block_size):
        stop = min(start + block_size, grid_size)
        distances = np.abs(
            image_theta[start:stop, np.newaxis] - image_phi[np.newaxis, :]
        )
        kernel = np.log(distances)
        total += np.sum(
            weight_theta[start:stop, np.newaxis]
            * weight_phi[np.newaxis, :]
            * kernel
        )
    return float(total / grid_size**2)


def sine_density(theta: np.ndarray) -> np.ndarray:
    return 1.0 + 0.35 * np.sin(theta) - 0.20 * np.sin(3.0 * theta)


def cosine_density(theta: np.ndarray) -> np.ndarray:
    return 1.0 + 0.30 * np.cos(2.0 * theta)


def sine_energy_prediction(s: float) -> float:
    coefficients = {1: 0.35 / 2.0, 3: -0.20 / 2.0}
    deficit = sum(
        (1.0 - math.exp(-2.0 * k * s)) * abs(value) ** 2 / k
        for k, value in coefficients.items()
    )
    return s - deficit


def opening_ratio(s: float) -> float:
    coefficients = {1: 0.35 / 2.0, 3: -0.20 / 2.0}
    return sum(
        ((1.0 - math.exp(-2.0 * k * s)) / (2.0 * k * s))
        * abs(value) ** 2
        for k, value in coefficients.items()
    )


def check_close(label: str, observed: float, expected: float, tolerance: float) -> None:
    error = abs(observed - expected)
    print(
        f"{label}: observed={observed:.10f}, expected={expected:.10f}, "
        f"absolute_error={error:.3e}"
    )
    if error > tolerance:
        raise AssertionError(
            f"{label} exceeded tolerance {tolerance:.3e}: {error:.3e}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--inject-error",
        action="store_true",
        help="perturb one claimed value to confirm that the verifier fails",
    )
    args = parser.parse_args()

    sample = np.linspace(0.0, 2.0 * math.pi, 10001, endpoint=False)
    reflected = (-sample) % (2.0 * math.pi)
    check_close(
        "reflection symmetrization",
        float(np.max(np.abs(sine_density(sample) + sine_density(reflected) - 2.0))),
        0.0,
        2.0e-14,
    )
    if float(np.min(sine_density(sample))) < 0.0:
        raise AssertionError("the endpoint test density is not nonnegative")

    endpoint_sine = direct_energy(0.0, sine_density)
    check_close("endpoint antisymmetric fiber", endpoint_sine, 0.0, 1.0e-3)

    endpoint_cosine = direct_energy(0.0, cosine_density)
    endpoint_cosine_prediction = -(0.30**2) / (2.0 * 2.0)
    check_close(
        "endpoint symmetric mode",
        endpoint_cosine,
        endpoint_cosine_prediction,
        1.0e-3,
    )

    for s in (0.20, 0.08, 0.03):
        observed = direct_energy(s, sine_density)
        expected = sine_energy_prediction(s)
        if args.inject_error and s == 0.08:
            expected += 0.04
        check_close(f"reopened ellipse s={s:.2f}", observed, expected, 1.0e-3)

    limiting_value = (0.35**2 + 0.20**2) / 4.0
    scales = (0.1, 0.01, 0.001, 0.0001)
    errors = [abs(opening_ratio(s) - limiting_value) for s in scales]
    for s, error in zip(scales, errors):
        print(f"opening limit s={s:g}: absolute_error={error:.3e}")
    if not all(later < earlier for earlier, later in zip(errors, errors[1:])):
        raise AssertionError("opening ratios do not converge monotonically to the theorem's limit")
    if errors[-1] > 2.0e-5:
        raise AssertionError("opening ratio did not reach the required limiting accuracy")

    print("all collapsed-ellipse selection checks passed")


if __name__ == "__main__":
    main()
