"""Independent numerical checks for the verified A8 sampled-counter results.

The manuscript contains the proofs.  This script checks the exact physical
image residual, the sharp hidden-mode bound and its diagonal extremizer, the
diagonal counterexample to the oracle's unqualified one-dependence equation,
and the fast-sampling expansion of the rounded two-stage waiting time.
"""

from __future__ import annotations

import math
from typing import Iterable

import mpmath as mp
import numpy as np
from numpy.typing import ArrayLike, NDArray


FloatArray = NDArray[np.float64]


def symmetric_log_divided_difference(p: float, s: float) -> float:
    """Return the symmetric logarithmic divided difference C(p,s)."""
    if not (0.0 < p < 1.0 and 0.0 < s < 1.0):
        raise ValueError("p and s must lie in (0,1)")
    if math.isclose(p, s, rel_tol=1e-10, abs_tol=1e-14):
        m = 0.5 * (p + s)
        d = 0.5 * (p - s)
        return (
            m * (1.0 - math.log(m))
            + d**2 / m * (0.5 + math.log(m) / 3.0)
            + d**4 / m**3 * (1.0 / 12.0 + 4.0 * math.log(m) / 45.0)
        )
    return (s * math.log(p) - p * math.log(s)) / (math.log(p) - math.log(s))


def hidden_mode(x: float, y: float) -> float:
    """Return the continuous secant extension of the hidden eigenvalue."""
    if not (math.isfinite(x) and math.isfinite(y) and x > 0.0 and y > 0.0):
        raise ValueError("x and y must be finite and positive")
    if math.isclose(x, y, rel_tol=1e-10, abs_tol=1e-14):
        midpoint = 0.5 * (x + y)
        return math.exp(-midpoint) * (1.0 - midpoint)
    return (y * math.exp(-y) - x * math.exp(-x)) / (y - x)


def sampled_counter_inclusions(x: float, y: float) -> FloatArray:
    """Return (r0,r1,r2) for dimensionless positive rates x and y."""
    with mp.workdps(50):
        x_mp = mp.mpf(x)
        y_mp = mp.mpf(y)
        p = mp.exp(-x_mp)
        s = mp.exp(-y_mp)
        if mp.almosteq(x_mp, y_mp):
            b = x_mp * p
        else:
            b = y_mp * (p - s) / (y_mp - x_mp)
        a = 1 - s - b
        rho = (1 - p) * (1 - s) / (1 - p + b)
        lam = p - b
        r1 = rho * a
        r2 = rho * rho + lam * (r1 - rho * rho)
        return np.array([rho, r1, r2], dtype=object)


def physical_image_residual(coordinates: ArrayLike) -> float:
    """Evaluate the exact sampled-counter image residual E(r)."""
    with mp.workdps(50):
        r0, r1, r2 = (mp.mpf(value) for value in coordinates)
        if r0 <= 0:
            raise ValueError("r0 must be positive")
        denominator = r1 - r0 * r0
        if denominator == 0:
            raise ValueError("the quotient denominator must be nonzero")
        a = r1 / r0
        lam = (r2 - r0 * r0) / denominator
        sigma1 = 1 - a + lam
        sigma2 = r0 * (1 - lam) - a + lam
        discriminant = sigma1 * sigma1 - 4 * sigma2
        if discriminant < mp.mpf("-2e-40"):
            raise ValueError("the quotient polynomial does not have real roots")
        root_gap = mp.sqrt(max(discriminant, 0))
        p = (sigma1 + root_gap) / 2
        s = (sigma1 - root_gap) / 2
        if mp.almosteq(p, s):
            divided_difference = p * (1 - mp.log(p))
        else:
            divided_difference = (s * mp.log(p) - p * mp.log(s)) / (
                mp.log(p) - mp.log(s)
            )
        return float(a - 1 + divided_difference)


def rounded_cycle_mean(gamma: float, kappa: float, delta: float) -> float:
    """Return E ceil((Exp(kappa)+Exp(gamma))/delta)."""
    if min(gamma, kappa, delta) <= 0.0:
        raise ValueError("gamma, kappa, and delta must be positive")
    x = gamma * delta
    y = kappa * delta
    if math.isclose(gamma, kappa, rel_tol=1e-10, abs_tol=1e-14):
        p = math.exp(-0.5 * (x + y))
        theta = 0.5 * (x + y)
        return 1.0 / (1.0 - p) + theta * p / (1.0 - p) ** 2
    return (
        kappa / (-math.expm1(-x)) - gamma / (-math.expm1(-y))
    ) / (kappa - gamma)


def rounded_cycle_mean_from_tails(
    gamma: float, kappa: float, delta: float, tolerance: float = 1e-16
) -> float:
    """Independently sum the sampled hypoexponential survival probabilities."""
    x = gamma * delta
    y = kappa * delta
    p = math.exp(-x)
    s = math.exp(-y)
    total = 0.0
    for lag in range(1_000_000):
        if math.isclose(x, y, rel_tol=1e-10, abs_tol=1e-14):
            theta = 0.5 * (x + y)
            tail = math.exp(-theta * lag) * (1.0 + theta * lag)
        else:
            tail = (y * p**lag - x * s**lag) / (y - x)
        total += tail
        if lag > 0 and tail < tolerance:
            return total
    raise ArithmeticError("tail sum did not converge")


def _maximum(values: Iterable[float]) -> float:
    return max(abs(value) for value in values)


def main() -> None:
    residuals = []
    spectral_violations = []
    lower = -math.exp(-2.0)
    for x in np.geomspace(0.02, 8.0, 80):
        for y in np.geomspace(0.03, 9.0, 75):
            residuals.append(physical_image_residual(sampled_counter_inclusions(x, y)))
            value = hidden_mode(float(x), float(y))
            spectral_violations.append(max(lower - value, value - 1.0, 0.0))

    gamma, kappa = 0.8, 2.1
    sampling_remainders = []
    for delta in (0.08, 0.04, 0.02):
        exact = delta * rounded_cycle_mean(gamma, kappa, delta)
        expansion = (
            1.0 / gamma
            + 1.0 / kappa
            + delta / 2.0
            + gamma * kappa * (gamma + kappa) * delta**4 / 720.0
        )
        sampling_remainders.append(abs(exact - expansion) / delta**6)

    print("A8 sampled-counter verification")
    print(f"physical-image grid maximum |E|={_maximum(residuals):.3e}")
    print(f"spectral-bound grid maximum violation={_maximum(spectral_violations):.3e}")
    print(f"lambda_hid(2,2)={hidden_mode(2.0, 2.0):.15f}")
    print(f"-exp(-2)={lower:.15f}")
    print(
        "oracle diagonal counterexample: x=y=2, scalar equation true, "
        f"lambda_hid={hidden_mode(2.0, 2.0):.15f}"
    )
    print(
        "scaled fast-sampling |remainder|/Delta^6="
        + np.array2string(np.asarray(sampling_remainders), precision=6)
    )


if __name__ == "__main__":
    main()
