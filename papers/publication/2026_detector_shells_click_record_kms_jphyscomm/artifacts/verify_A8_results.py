"""Independent numerical checks for the verified A8 sampled-counter results.

The manuscript contains the proofs.  This script checks the exact physical
image residual, the sharp hidden-mode bound and its diagonal extremizer, the
diagonal counterexample to the oracle's unqualified one-dependence equation,
the fast-sampling expansion, the A8-r2 joint physical-image test, and the
A8-r3 finite-range Markov-gap specification score.  It also checks the full
fixed-marginal Markov--Palm tangent projection and finite-dimensional basis
used by the A8-r4 omnibus-score result.
"""

from __future__ import annotations

import itertools
import math
from statistics import NormalDist
from typing import Iterable

import mpmath as mp
import numpy as np
from numpy.typing import ArrayLike, NDArray


FloatArray = NDArray[np.float64]


def _analytic_h_and_derivative(w: float) -> tuple[float, float]:
    """Return H(w) and H'(w) on the real analytic branch w < 1."""
    if not math.isfinite(w) or w >= 1.0:
        raise ValueError("w must be finite and less than one")
    if abs(w) < 1e-6:
        value = 1.0 - w / 3.0 - 4.0 * w**2 / 45.0 - 44.0 * w**3 / 945.0
        derivative = -1.0 / 3.0 - 8.0 * w / 45.0 - 44.0 * w**2 / 315.0
        return value, derivative
    if w > 0.0:
        root = math.sqrt(w)
        angle = math.atanh(root)
        value = root / angle
        derivative = (angle - root / (1.0 - root**2)) / (
            2.0 * root * angle**2
        )
        return value, derivative
    root = math.sqrt(-w)
    angle = math.atan(root)
    value = root / angle
    derivative = -(angle - root / (1.0 + root**2)) / (
        2.0 * root * angle**2
    )
    return value, derivative


def analytic_log_divided_difference(sigma1: float, sigma2: float) -> float:
    """Evaluate the real analytic continuation in symmetric coordinates."""
    if not (math.isfinite(sigma1) and math.isfinite(sigma2)):
        raise ValueError("symmetric coordinates must be finite")
    if sigma1 <= 0.0 or sigma2 <= 0.0:
        raise ValueError("sigma1 and sigma2 must be positive")
    w = 1.0 - 4.0 * sigma2 / sigma1**2
    h, _ = _analytic_h_and_derivative(w)
    return 0.5 * sigma1 * (1.0 - 0.5 * math.log(sigma2) * h)


def _analytic_log_divided_difference_gradient(
    sigma1: float, sigma2: float
) -> FloatArray:
    w = 1.0 - 4.0 * sigma2 / sigma1**2
    h, h_prime = _analytic_h_and_derivative(w)
    log_sigma2 = math.log(sigma2)
    dw_dsigma1 = 8.0 * sigma2 / sigma1**3
    dw_dsigma2 = -4.0 / sigma1**2
    common = 1.0 - 0.5 * log_sigma2 * h
    d_sigma1 = 0.5 * common - 0.25 * sigma1 * log_sigma2 * h_prime * dw_dsigma1
    d_sigma2 = -0.25 * sigma1 * (
        h / sigma2 + log_sigma2 * h_prime * dw_dsigma2
    )
    return np.array([d_sigma1, d_sigma2])


def constraint_jacobian(coordinates: ArrayLike) -> FloatArray:
    """Return the Jacobian of (analytic image residual, discriminant)."""
    r0, r1, r2 = np.asarray(coordinates, dtype=float)
    denominator = r1 - r0**2
    if r0 <= 0.0 or denominator == 0.0:
        raise ValueError("coordinates lie outside the quotient chart")
    a = r1 / r0
    lam = (r2 - r0**2) / denominator
    sigma1 = 1.0 - a + lam
    sigma2 = r0 * (1.0 - lam) - a + lam
    da = np.array([-r1 / r0**2, 1.0 / r0, 0.0])
    dlam = np.array(
        [2.0 * r0 * (lam - 1.0) / denominator, -lam / denominator, 1.0 / denominator]
    )
    dphi1 = -da + dlam
    dphi2 = np.array([1.0 - lam, 0.0, 0.0]) - da + (1.0 - r0) * dlam
    dphi = np.vstack([dphi1, dphi2])
    gradient = _analytic_log_divided_difference_gradient(sigma1, sigma2)
    de = da + gradient @ dphi
    ddiscriminant = np.array([2.0 * sigma1, -4.0]) @ dphi
    return np.vstack([de, ddiscriminant])


def _gap_masses(x: float, y: float, tolerance: float = 1e-15) -> FloatArray:
    masses: list[float] = []
    p = math.exp(-x)
    s = math.exp(-y)

    def survival(k: int) -> float:
        if math.isclose(x, y, rel_tol=1e-10, abs_tol=1e-14):
            theta = 0.5 * (x + y)
            return math.exp(-theta * k) * (1.0 + theta * k)
        return (y * p**k - x * s**k) / (y - x)

    previous = survival(0)
    for k in range(1_000_000):
        following = survival(k + 1)
        masses.append(previous - following)
        if following < tolerance:
            return np.asarray(masses)
        previous = following
    raise ArithmeticError("gap-law truncation did not converge")


def regenerative_inclusion_covariance(x: float, y: float) -> tuple[FloatArray, FloatArray]:
    """Deterministically sum the complete-cycle covariance from the gap law."""
    if min(x, y) <= 0.0:
        raise ValueError("dimensionless rates must be positive")
    g = _gap_masses(x, y)
    index = np.arange(g.size)
    mu = float(np.dot(index + 1.0, g))
    r = np.array([1.0 / mu, g[0] / mu, (g[1] + g[0] ** 2) / mu])
    i = index[:, None]
    j = index[None, :]
    reward = np.empty((g.size, g.size, 3))
    reward[:, :, 0] = 1.0
    reward[:, :, 1] = i == 0
    reward[:, :, 2] = (i == 1) + ((i == 0) & (j == 0))
    centered = reward - r[None, None, :] * (i[:, :, None] + 1.0)
    pair_mass = g[:, None] * g[None, :]
    variance = np.einsum("ij,ija,ijb->ab", pair_mass, centered, centered)
    future_mean = np.einsum("k,jka->ja", g, centered)
    adjacent = np.einsum("ij,ija,jb->ab", pair_mass, centered, future_mean)
    return r, (variance + adjacent + adjacent.T) / mu


def cone_wald_distance(e: float, discriminant: float, omega: ArrayLike) -> float:
    """Return the covariance-metric squared distance to {0} x [0,infinity)."""
    covariance = np.asarray(omega, dtype=float)
    if covariance.shape != (2, 2) or np.linalg.eigvalsh(covariance)[0] <= 0.0:
        raise ValueError("omega must be a positive-definite 2 by 2 matrix")
    beta = covariance[0, 1] / covariance[0, 0]
    variance = covariance[1, 1] - covariance[0, 1] ** 2 / covariance[0, 0]
    standardized_inequality = discriminant - beta * e
    return e**2 / covariance[0, 0] + min(standardized_inequality, 0.0) ** 2 / variance


def _chi_square_cdf(value: float, degrees: int) -> float:
    if value <= 0.0:
        return 0.0
    if degrees == 1:
        return math.erf(math.sqrt(value / 2.0))
    if degrees == 2:
        return 1.0 - math.exp(-value / 2.0)
    raise ValueError("only one and two degrees of freedom are used")


def boundary_critical_value(alpha: float) -> float:
    """Return the upper-alpha quantile of 0.5 chi1^2 + 0.5 chi2^2."""
    if not 0.0 < alpha < 1.0:
        raise ValueError("alpha must lie in (0,1)")
    lower, upper = 0.0, 1.0
    target = 1.0 - alpha
    while 0.5 * (_chi_square_cdf(upper, 1) + _chi_square_cdf(upper, 2)) < target:
        upper *= 2.0
    for _ in range(80):
        midpoint = 0.5 * (lower + upper)
        cdf = 0.5 * (_chi_square_cdf(midpoint, 1) + _chi_square_cdf(midpoint, 2))
        if cdf < target:
            lower = midpoint
        else:
            upper = midpoint
    return 0.5 * (lower + upper)


def local_gap_perturbation_basis() -> FloatArray:
    """Rows give the eta_mu, eta_0, eta_1 perturbations on gaps 0,...,3."""
    return np.array(
        [[0.0, 0.0, -1.0, 1.0], [1.0, 0.0, -3.0, 2.0], [0.0, 1.0, -2.0, 1.0]]
    )


def local_power(
    delta: float, tau: float, omega: ArrayLike, alpha: float = 0.05
) -> float:
    """Evaluate the joint image test's two-coordinate local-power integral."""
    covariance = np.asarray(omega, dtype=float)
    beta = covariance[0, 1] / covariance[0, 0]
    variance = covariance[1, 1] - covariance[0, 1] ** 2 / covariance[0, 0]
    a_star = delta / math.sqrt(covariance[0, 0])
    b_star = (tau - beta * delta) / math.sqrt(variance)
    critical = boundary_critical_value(alpha)

    with mp.workdps(40):
        root_critical = mp.sqrt(critical)

        def normal_cdf(value: mp.mpf) -> mp.mpf:
            return (1 + mp.erf(value / mp.sqrt(2))) / 2

        def interval_probability(q: mp.mpf) -> mp.mpf:
            if q <= 0:
                return mp.mpf("0")
            root = mp.sqrt(q)
            return normal_cdf(root - a_star) - normal_cdf(-root - a_star)

        positive_part = normal_cdf(b_star) * interval_probability(critical)
        negative_part = mp.quad(
            lambda value: interval_probability(critical - value**2)
            * mp.exp(-((value - b_star) ** 2) / 2)
            / mp.sqrt(2 * mp.pi),
            [-root_critical, 0],
        )
        return float(1 - positive_part - negative_part)


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


def markov_gap_alternative(
    diagonal_rate: float, eta: float
) -> tuple[FloatArray, FloatArray, FloatArray, float]:
    """Construct the finite-range Markov-gap alternative at an exchange point."""
    if not math.isfinite(diagonal_rate) or diagonal_rate <= 0.0:
        raise ValueError("the diagonal rate must be finite and positive")
    if not math.isfinite(eta) or eta < 0.0:
        raise ValueError("eta must be finite and nonnegative")

    gap_mass = _gap_masses(diagonal_rate, diagonal_rate)
    gap_mass /= gap_mass.sum()
    if gap_mass.size < 3 or min(gap_mass[1], gap_mass[2]) <= 0.0:
        raise ArithmeticError("the truncated gap law does not contain positive masses 1 and 2")

    score = np.zeros_like(gap_mass)
    score[1] = 1.0
    score[2] = -gap_mass[1] / gap_mass[2]
    maximum_eta = gap_mass[2] / gap_mass[1]
    if eta >= maximum_eta:
        raise ValueError(f"eta must be smaller than {maximum_eta:.12g} for positivity")

    transition = gap_mass[None, :] * (
        1.0 + eta * score[:, None] * score[None, :]
    )
    indices = np.arange(gap_mass.size, dtype=float)
    mean_cycle = float((indices + 1.0) @ gap_mass)
    return gap_mass, score, transition, mean_cycle


def markov_gap_inclusions(
    gap_mass: ArrayLike, transition: ArrayLike, mean_cycle: float
) -> FloatArray:
    """Return the first three inclusion coordinates of a stationary gap chain."""
    g = np.asarray(gap_mass, dtype=float)
    q = np.asarray(transition, dtype=float)
    if g.ndim != 1 or g.size < 2 or q.shape != (g.size, g.size):
        raise ValueError("gap_mass and transition have incompatible shapes")
    if not math.isfinite(mean_cycle) or mean_cycle <= 0.0:
        raise ValueError("mean_cycle must be finite and positive")
    return np.array(
        [
            1.0 / mean_cycle,
            g[0] / mean_cycle,
            (g[1] + g[0] * q[0, 0]) / mean_cycle,
        ]
    )


def markov_gap_information(
    gap_mass: ArrayLike, score: ArrayLike, mean_cycle: float
) -> float:
    """Return Fisher information per calendar bin for the Markov-gap path."""
    g = np.asarray(gap_mass, dtype=float)
    h = np.asarray(score, dtype=float)
    if g.shape != h.shape or g.ndim != 1:
        raise ValueError("gap_mass and score must be one-dimensional arrays of equal size")
    if not math.isfinite(mean_cycle) or mean_cycle <= 0.0:
        raise ValueError("mean_cycle must be finite and positive")
    second_moment = float(g @ (h * h))
    return second_moment**2 / mean_cycle


def markov_gap_local_power(
    diagonal_rate: float, local_parameter: float, alpha: float = 0.05
) -> float:
    """Return the one-sided Gaussian local power of the finite-range score."""
    if not math.isfinite(local_parameter) or local_parameter < 0.0:
        raise ValueError("the local parameter must be finite and nonnegative")
    if not 0.0 < alpha < 1.0:
        raise ValueError("alpha must lie in (0,1)")
    g, h, _, mean_cycle = markov_gap_alternative(diagonal_rate, 0.0)
    information = markov_gap_information(g, h, mean_cycle)
    normal = NormalDist()
    critical = normal.inv_cdf(1.0 - alpha)
    return 1.0 - normal.cdf(critical - local_parameter * math.sqrt(information))


def _probability_vector(gap_mass: ArrayLike) -> FloatArray:
    g = np.asarray(gap_mass, dtype=float)
    if g.ndim != 1 or g.size < 2 or not np.all(np.isfinite(g)):
        raise ValueError("gap_mass must be a finite one-dimensional vector")
    if np.min(g) <= 0.0 or not math.isclose(float(g.sum()), 1.0, abs_tol=1e-12):
        raise ValueError("gap_mass must be a strictly positive probability vector")
    return g


def markov_palm_tangent_projection(
    gap_mass: ArrayLike, values: ArrayLike
) -> FloatArray:
    """Project a finite table onto the fixed-marginal, q(0,0)=0 tangent space."""
    g = _probability_vector(gap_mass)
    table = np.asarray(values, dtype=float)
    if table.shape != (g.size, g.size) or not np.all(np.isfinite(table)):
        raise ValueError("values must be a finite square table matching gap_mass")

    row_mean = table @ g
    column_mean = g @ table
    interaction = table - row_mean[:, None] - column_mean[None, :] + g @ row_mean
    zero_contrast = np.zeros_like(g)
    zero_contrast[0] = 1.0
    zero_contrast -= g[0]
    atom_interaction = np.outer(zero_contrast, zero_contrast)
    atom_norm_squared = float(
        np.einsum("i,j,ij->", g, g, atom_interaction * atom_interaction)
    )
    coefficient = float(
        np.einsum("i,j,ij->", g, g, interaction * atom_interaction)
        / atom_norm_squared
    )
    return interaction - coefficient * atom_interaction


def project_markov_tangent(gap_mass: ArrayLike, values: ArrayLike) -> FloatArray:
    """Compatibility alias for :func:`markov_palm_tangent_projection`."""
    return markov_palm_tangent_projection(gap_mass, values)


def markov_palm_transition(
    gap_mass: ArrayLike, score: ArrayLike, parameter: float
) -> FloatArray:
    """Construct Q(l|k)=g(l){1+parameter*q(k,l)} on a finite gap space."""
    g = _probability_vector(gap_mass)
    q = np.asarray(score, dtype=float)
    if q.shape != (g.size, g.size) or not np.all(np.isfinite(q)):
        raise ValueError("score must be a finite square table matching gap_mass")
    if not math.isfinite(parameter):
        raise ValueError("parameter must be finite")
    transition = g[None, :] * (1.0 + parameter * q)
    if np.min(transition) < -1e-14:
        raise ValueError("parameter makes the transition kernel negative")
    return transition


def markov_palm_information(gap_mass: ArrayLike, score: ArrayLike) -> float:
    """Return the fixed-marginal Markov score information per calendar bin."""
    g = _probability_vector(gap_mass)
    q = np.asarray(score, dtype=float)
    if q.shape != (g.size, g.size) or not np.all(np.isfinite(q)):
        raise ValueError("score must be a finite square table matching gap_mass")
    mean_cycle = float((np.arange(g.size, dtype=float) + 1.0) @ g)
    norm_squared = float(np.einsum("i,j,ij->", g, g, q * q))
    return norm_squared / mean_cycle


def _weighted_mean_zero_basis(gap_mass: ArrayLike) -> FloatArray:
    g = _probability_vector(gap_mass)
    candidates = []
    zero_contrast = np.zeros_like(g)
    zero_contrast[0] = 1.0
    candidates.append(zero_contrast - g[0])
    for index in range(1, g.size):
        contrast = np.zeros_like(g)
        contrast[index] = 1.0
        candidates.append(contrast - g[index])

    basis: list[FloatArray] = []
    for candidate in candidates:
        residual = candidate.copy()
        for vector in basis:
            residual -= float(g @ (residual * vector)) * vector
        norm = math.sqrt(float(g @ (residual * residual)))
        if norm > 2e-12:
            basis.append(residual / norm)
        if len(basis) == g.size - 1:
            break
    return np.asarray(basis)


def finite_markov_tangent_basis(gap_mass: ArrayLike) -> FloatArray:
    """Return an orthonormal basis of the finite Markov-Palm tangent space."""
    one_gap_basis = _weighted_mean_zero_basis(gap_mass)
    products = [
        np.outer(left, right)
        for left_index, left in enumerate(one_gap_basis)
        for right_index, right in enumerate(one_gap_basis)
        if (left_index, right_index) != (0, 0)
    ]
    return np.asarray(products)


def equal_rate_gap_tail(rate: float, layer: int) -> float:
    """Return S_layer=exp(-rate*layer)*(1+rate*layer)."""
    if not math.isfinite(rate) or rate <= 0.0 or layer < 0:
        raise ValueError("rate must be positive and layer must be nonnegative")
    return math.exp(-rate * layer) * (1.0 + rate * layer)


def weighted_helmert_partition(rate: float, layer: int) -> tuple[FloatArray, FloatArray]:
    """Evaluate e_0,...,e_layer on atoms 0,...,layer and the residual tail."""
    if layer < 0:
        raise ValueError("layer must be nonnegative")
    tails = np.array([equal_rate_gap_tail(rate, j) for j in range(layer + 2)])
    masses = tails[:-1] - tails[1:]
    partition_mass = np.concatenate((masses, tails[-1:]))
    basis = np.zeros((layer + 1, layer + 2))
    for index in range(layer + 1):
        basis[index, index] = math.sqrt(
            tails[index + 1] / (masses[index] * tails[index])
        )
        basis[index, index + 1 :] = -math.sqrt(
            masses[index] / (tails[index] * tails[index + 1])
        )
    return partition_mass, basis


def helmert_layer_diagnostics(rate: float, layer: int) -> tuple[float, float, float]:
    """Return Gram error, S_J-scaled tensor envelope, and scaled third moment."""
    partition_mass, basis = weighted_helmert_partition(rate, layer)
    gram = np.einsum("k,ak,bk->ab", partition_mass, basis, basis)
    tensor_envelope = 0.0
    for left in range(layer + 1):
        for right in range(layer + 1):
            if (left, right) != (0, 0):
                tensor_envelope = max(
                    tensor_envelope,
                    float(np.max(np.abs(np.outer(basis[left], basis[right])))),
                )

    christoffel = np.sum(basis * basis, axis=0)
    omitted = np.outer(basis[0] * basis[0], basis[0] * basis[0])
    vector_norm_squared = np.outer(christoffel, christoffel) - omitted
    vector_third_moment = float(
        np.einsum(
            "i,j,ij->",
            partition_mass,
            partition_mass,
            np.maximum(vector_norm_squared, 0.0) ** 1.5,
        )
    )
    tail = equal_rate_gap_tail(rate, layer)
    return (
        float(np.max(np.abs(gram - np.eye(layer + 1)))),
        tail * tensor_envelope,
        tail * vector_third_moment,
    )


def _helmert_interaction_values(rate: float, layer: int) -> tuple[FloatArray, FloatArray]:
    partition_mass, basis = weighted_helmert_partition(rate, layer)
    values = np.asarray(
        [
            np.outer(basis[:, left], basis[:, right]).reshape(-1)[1:]
            for left in range(partition_mass.size)
            for right in range(partition_mass.size)
        ]
    ).reshape(partition_mass.size, partition_mass.size, -1)
    return partition_mass, values


def helmert_overlap_diagnostics(rate: float, layer: int) -> tuple[float, float, float]:
    """Return covariance error, lag-one covariance error, and S_J-scaled third moment."""
    partition_mass, values = _helmert_interaction_values(rate, layer)
    dimension = (layer + 1) ** 2 - 1
    covariance = np.einsum(
        "i,j,ija,ijb->ab", partition_mass, partition_mass, values, values
    )
    lag_covariance = np.einsum(
        "i,j,k,ija,jkb->ab",
        partition_mass,
        partition_mass,
        partition_mass,
        values,
        values,
    )
    third_moment = float(
        np.einsum(
            "i,j,ij->",
            partition_mass,
            partition_mass,
            np.linalg.norm(values, axis=2) ** 3,
        )
    )
    return (
        float(np.max(np.abs(covariance - np.eye(dimension)))),
        float(np.max(np.abs(lag_covariance))),
        equal_rate_gap_tail(rate, layer) * third_moment,
    )


def helmert_exact_block_moment_ratio(rate: float, layer: int, length: int) -> float:
    """Enumerate a small overlap block and divide its third moment by its Rosenthal scale."""
    if length < 1:
        raise ValueError("length must be positive")
    partition_mass, values = _helmert_interaction_values(rate, layer)
    dimension = values.shape[2]
    third_moment = 0.0
    for states in itertools.product(range(partition_mass.size), repeat=length + 1):
        probability = math.prod(float(partition_mass[state]) for state in states)
        block_sum = np.zeros(dimension)
        for index in range(length):
            block_sum += values[states[index], states[index + 1]]
        third_moment += probability * float(np.linalg.norm(block_sum) ** 3)
    scale = (length * dimension) ** 1.5 + length / equal_rate_gap_tail(rate, layer)
    return third_moment / scale


def helmert_blocking_log_terms(
    rate: float, log_sample_size: float, layer: int
) -> tuple[float, float, float]:
    """Return deleted-edge and CMU dimension-adjusted log error bounds."""
    dimension = (layer + 1) ** 2 - 1
    log_block_length = math.log(dimension**2 + log_sample_size)
    log_dimension = math.log(dimension)
    log_tail = -rate * layer + math.log1p(rate * layer)
    deleted_mean_square = math.exp(log_dimension - log_block_length) + math.exp(
        log_block_length + log_dimension - log_sample_size
    )
    return (
        math.log(deleted_mean_square),
        0.5 * log_block_length + 2.5 * log_dimension - 0.5 * log_sample_size,
        log_dimension - 0.5 * log_sample_size - log_tail,
    )


def helmert_critical_log_mean(rate: float, layer: int, constant: float) -> float:
    """Return log(n*S_J^2) on 2*rate*J=log n+2*log log n-constant."""
    target = 2.0 * rate * layer + constant
    lower = 1.0
    upper = max(2.0, target)
    while upper + 2.0 * math.log(upper) < target:
        upper *= 2.0
    for _ in range(100):
        midpoint = 0.5 * (lower + upper)
        if midpoint + 2.0 * math.log(midpoint) < target:
            lower = midpoint
        else:
            upper = midpoint
    log_sample_size = 0.5 * (lower + upper)
    log_tail = -rate * layer + math.log1p(rate * layer)
    return log_sample_size + 2.0 * log_tail


def helmert_log_rate_terms(rate: float, log_sample_size: float, layer: int) -> tuple[float, float]:
    """Return logs of n*S_J^2 and d_J/(sqrt(n)*S_J)."""
    if not math.isfinite(log_sample_size):
        raise ValueError("log_sample_size must be finite")
    log_tail = -rate * layer + math.log1p(rate * layer)
    dimension = (layer + 1) ** 2 - 1
    return (
        log_sample_size + 2.0 * log_tail,
        math.log(dimension) - 0.5 * log_sample_size - log_tail,
    )


def weighted_omnibus_monte_carlo(
    weights: ArrayLike,
    direction: ArrayLike,
    alpha: float = 0.05,
    draws: int = 100_000,
    seed: int = 0,
) -> tuple[float, float]:
    """Numerically compare the weighted Gaussian score law at zero and a direction."""
    lam = np.asarray(weights, dtype=float)
    shift = np.asarray(direction, dtype=float)
    if lam.ndim != 1 or shift.shape != lam.shape or np.min(lam) <= 0.0:
        raise ValueError("weights and direction must be equal-length vectors with positive weights")
    if not 0.0 < alpha < 1.0 or draws < 2:
        raise ValueError("alpha and draws are outside their admissible ranges")
    rng = np.random.default_rng(seed)
    normals = rng.normal(size=(draws, lam.size))
    null_values = (normals * normals) @ lam
    critical = float(np.quantile(null_values, 1.0 - alpha))
    alternative_values = ((normals + shift) ** 2) @ lam
    return (
        float(np.mean(null_values > critical)),
        float(np.mean(alternative_values > critical)),
    )


def rademacher_mixture_second_moment(
    radius: float, mean_cycle: float, dimension: int
) -> float:
    """Return [cosh(r^2/(mu*d))]^d for the Gaussian-sequence mixture."""
    if radius <= 0.0 or mean_cycle <= 0.0 or dimension < 1:
        raise ValueError("radius, mean_cycle, and dimension must be positive")
    argument = radius * radius / (mean_cycle * dimension)
    return math.exp(dimension * math.log(math.cosh(argument)))


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

    image_formula_errors = []
    minimum_jacobian_singular_value = math.inf
    minimum_sigma_eigenvalue = math.inf
    minimum_omega_eigenvalue = math.inf
    covariance_points = (
        (0.1, 0.1),
        (0.2, 1.7),
        (1.0, 1.0),
        (2.0, 4.0),
        (5.0, 5.5),
    )
    for x, y in covariance_points:
        p = math.exp(-x)
        s = math.exp(-y)
        image_formula_errors.append(
            analytic_log_divided_difference(p + s, p * s)
            - symmetric_log_divided_difference(p, s)
        )
        coordinates, sigma_r = regenerative_inclusion_covariance(x, y)
        jacobian = constraint_jacobian(coordinates)
        omega = jacobian @ sigma_r @ jacobian.T
        minimum_jacobian_singular_value = min(
            minimum_jacobian_singular_value,
            np.linalg.svd(jacobian, compute_uv=False)[-1],
        )
        minimum_sigma_eigenvalue = min(
            minimum_sigma_eigenvalue, np.linalg.eigvalsh(sigma_r)[0]
        )
        minimum_omega_eigenvalue = min(
            minimum_omega_eigenvalue, np.linalg.eigvalsh(omega)[0]
        )

    trial_omega = np.array([[1.4, 0.3], [0.3, 1.1]])
    alpha = 0.05
    powers = np.array(
        [
            local_power(0.0, 0.0, trial_omega, alpha),
            local_power(0.0, 1.0, trial_omega, alpha),
            local_power(0.0, -1.0, trial_omega, alpha),
        ]
    )
    print("A8-r2 joint physical-image verification")
    print(f"analytic C formula maximum error={_maximum(image_formula_errors):.3e}")
    print(
        "tested minimum singular value Dpsi="
        f"{minimum_jacobian_singular_value:.6e}"
    )
    print(f"tested minimum eigenvalue Sigma_r={minimum_sigma_eigenvalue:.6e}")
    print(f"tested minimum eigenvalue Omega={minimum_omega_eigenvalue:.6e}")
    print(
        "boundary mixture 0.95 quantile="
        f"{boundary_critical_value(alpha):.10f}"
    )
    print(
        "local powers (origin, physical tau=1, nonreal tau=-1)="
        + np.array2string(powers, precision=10)
    )

    row_sum_errors = []
    stationary_errors = []
    inclusion_errors = []
    word_five_errors = []
    informations = []
    for diagonal_rate in (0.35, 1.0, 2.4, 5.0):
        g0, h0, q0, mu0 = markov_gap_alternative(diagonal_rate, 0.0)
        g1, h1, q1, mu1 = markov_gap_alternative(diagonal_rate, 0.005)
        row_sum_errors.append(np.max(np.abs(q1.sum(axis=1) - 1.0)))
        stationary_errors.append(np.max(np.abs(g1 @ q1 - g1)))
        inclusion_errors.append(
            np.max(
                np.abs(
                    markov_gap_inclusions(g1, q1, mu1)
                    - markov_gap_inclusions(g0, q0, mu0)
                )
            )
        )
        word_five_errors.append(
            abs(g1[1] * q1[1, 1] / mu1 - g1[1] ** 2 * 1.005 / mu1)
        )
        informations.append(markov_gap_information(g0, h0, mu0))

    score_powers = np.array(
        [markov_gap_local_power(1.35, t, alpha) for t in (0.0, 0.5, 1.0)]
    )
    print("A8-r3 complete visible-law score verification")
    print(f"Markov-gap maximum row-sum error={_maximum(row_sum_errors):.3e}")
    print(f"Markov-gap maximum stationary-marginal error={_maximum(stationary_errors):.3e}")
    print(f"three-inclusion maximum preservation error={_maximum(inclusion_errors):.3e}")
    print(f"length-five identity maximum error={_maximum(word_five_errors):.3e}")
    print(f"tested minimum calendar-time information={min(informations):.6e}")
    print(
        "finite-range score local powers (t=0,0.5,1)="
        + np.array2string(score_powers, precision=10)
    )

    tangent_row_errors = []
    tangent_column_errors = []
    tangent_atom_errors = []
    tangent_inclusion_errors = []
    tangent_information_errors = []
    rng = np.random.default_rng(20260807)
    for diagonal_rate in (0.35, 1.0, 2.4, 5.0):
        gap_mass = markov_gap_alternative(diagonal_rate, 0.0)[0][:12]
        gap_mass /= gap_mass.sum()
        raw = rng.normal(size=(gap_mass.size, gap_mass.size))
        score = markov_palm_tangent_projection(gap_mass, raw)
        tangent_row_errors.append(np.max(np.abs(score @ gap_mass)))
        tangent_column_errors.append(np.max(np.abs(gap_mass @ score)))
        tangent_atom_errors.append(abs(score[0, 0]))
        parameter = 0.02 / np.max(np.abs(score))
        transition = markov_palm_transition(gap_mass, score, parameter)
        null_transition = np.broadcast_to(gap_mass, transition.shape)
        mean_cycle = float((np.arange(gap_mass.size) + 1.0) @ gap_mass)
        tangent_inclusion_errors.append(
            np.max(
                np.abs(
                    markov_gap_inclusions(gap_mass, transition, mean_cycle)
                    - markov_gap_inclusions(gap_mass, null_transition, mean_cycle)
                )
            )
        )
        norm_squared = float(
            np.einsum("i,j,ij->", gap_mass, gap_mass, score * score)
        )
        tangent_information_errors.append(
            markov_palm_information(gap_mass, score) - norm_squared / mean_cycle
        )

    mixture_moments = np.array(
        [rademacher_mixture_second_moment(1.7, 1.9, d) for d in (16, 64, 256, 1024)]
    )
    tangent_g = markov_gap_alternative(1.35, 0.0)[0][:9]
    tangent_g /= tangent_g.sum()
    tangent_raw = np.arange(tangent_g.size**2, dtype=float).reshape(
        tangent_g.size, tangent_g.size
    )
    tangent_raw = np.sin(tangent_raw + 0.37)
    tangent_score = markov_palm_tangent_projection(tangent_g, tangent_raw)
    tangent_scale = 0.03 / np.max(np.abs(tangent_score))
    tangent_transition = markov_palm_transition(
        tangent_g, tangent_score, tangent_scale
    )
    tangent_mu = float((np.arange(tangent_g.size) + 1.0) @ tangent_g)
    tangent_null = np.broadcast_to(tangent_g, tangent_transition.shape)
    tangent_basis = finite_markov_tangent_basis(tangent_g)
    tangent_gram = np.einsum(
        "i,j,aij,bij->ab", tangent_g, tangent_g, tangent_basis, tangent_basis
    )
    tangent_norm = float(
        np.einsum("i,j,ij->", tangent_g, tangent_g, tangent_score**2)
    )
    tangent_information_error = abs(
        markov_palm_information(tangent_g, tangent_score)
        - tangent_norm / tangent_mu
    )
    null_power, direction_power = weighted_omnibus_monte_carlo(
        np.array([0.5, 0.2, 0.08, 0.03]),
        np.array([0.0, 0.0, 1.4, 0.0]),
        alpha=alpha,
        draws=300_000,
        seed=20260807,
    )
    print("A8-r4 complete Markov-Palm tangent verification")
    print(
        "tangent maximum row/column-centering error="
        f"{max(_maximum(tangent_row_errors), _maximum(tangent_column_errors), np.max(np.abs(tangent_score @ tangent_g)), np.max(np.abs(tangent_g @ tangent_score))):.3e}"
    )
    print(
        "tangent maximum |q(0,0)|="
        f"{max(_maximum(tangent_atom_errors), abs(tangent_score[0, 0])):.3e}"
    )
    print(
        "tangent three-inclusion maximum preservation error="
        f"{max(_maximum(tangent_inclusion_errors), np.max(np.abs(markov_gap_inclusions(tangent_g, tangent_transition, tangent_mu) - markov_gap_inclusions(tangent_g, tangent_null, tangent_mu)))):.3e}"
    )
    print(
        "finite tangent-basis maximum Gram error="
        f"{np.max(np.abs(tangent_gram - np.eye(tangent_basis.shape[0]))):.3e}"
    )
    print(
        "calendar-time information maximum scaling error="
        f"{max(_maximum(tangent_information_errors), tangent_information_error):.3e}"
    )
    print(
        "Rademacher mixture second moments (d=16,64,256,1024)="
        + np.array2string(mixture_moments, precision=10)
    )
    print(
        "weighted omnibus Monte Carlo (null, nonzero direction)="
        + np.array2string(np.array([null_power, direction_power]), precision=10)
    )

    helmert_gram_errors = []
    helmert_envelopes = []
    helmert_third_moments = []
    for diagonal_rate in (0.2, 0.7, 1.35, 3.0, 5.0):
        for layer in (2, 4, 8, 12, 20):
            gram_error, envelope, third_moment = helmert_layer_diagnostics(
                diagonal_rate, layer
            )
            helmert_gram_errors.append(gram_error)
            helmert_envelopes.append(envelope)
            helmert_third_moments.append(third_moment)

    log_n = 200.0
    rate = 1.35
    log_log_n = math.log(log_n)
    necessary_inside = math.floor(
        (log_n + 2.0 * log_log_n - 20.0) / (2.0 * rate)
    )
    necessary_outside = math.ceil(
        (log_n + 2.0 * log_log_n + 20.0) / (2.0 * rate)
    )
    sufficient_inside = math.floor(
        (log_n - 2.0 * log_log_n - 20.0) / (2.0 * rate)
    )
    log_necessary_inside = helmert_log_rate_terms(
        rate, log_n, necessary_inside
    )[0]
    log_necessary_outside = helmert_log_rate_terms(
        rate, log_n, necessary_outside
    )[0]
    log_sufficient_inside = helmert_log_rate_terms(
        rate, log_n, sufficient_inside
    )[1]
    print("A8-r5 canonical Helmert growing-layer verification")
    print(f"Helmert maximum Gram error={_maximum(helmert_gram_errors):.3e}")
    print(
        "tested range of S_J * max||phi_ab||_infinity="
        + np.array2string(
            np.array([min(helmert_envelopes), max(helmert_envelopes)]),
            precision=10,
        )
    )
    print(
        "tested range of S_J * E||Phi_J||_2^3="
        + np.array2string(
            np.array([min(helmert_third_moments), max(helmert_third_moments)]),
            precision=10,
        )
    )
    print(
        "log threshold diagnostics (necessary inside/outside, sufficient inside)="
        + np.array2string(
            np.array(
                [
                    log_necessary_inside,
                    log_necessary_outside,
                    log_sufficient_inside,
                ]
            ),
            precision=10,
        )
    )

    overlap_covariance_errors = []
    overlap_lag_errors = []
    overlap_third_moments = []
    exact_block_ratios = []
    critical_constant_errors = []
    critical_constant = 3.0
    critical_target = critical_constant - math.log(4.0)
    for diagonal_rate in (0.2, 0.7, 1.35, 3.0, 5.0):
        for layer in (1, 2, 4, 8):
            covariance_error, lag_error, third_moment = helmert_overlap_diagnostics(
                diagonal_rate, layer
            )
            overlap_covariance_errors.append(covariance_error)
            overlap_lag_errors.append(lag_error)
            overlap_third_moments.append(third_moment)
        if diagonal_rate < 5.0:
            for layer in (1, 2, 3):
                for length in (1, 2, 3, 4):
                    exact_block_ratios.append(
                        helmert_exact_block_moment_ratio(
                            diagonal_rate, layer, length
                        )
                    )
        critical_constant_errors.append(
            abs(
                helmert_critical_log_mean(
                    diagonal_rate, 10_000, critical_constant
                )
                - critical_target
            )
        )

    bracket_log_n = 12_800.0
    bracket_rate = 1.35
    sufficient_layer = math.floor(
        (
            bracket_log_n
            - 2.0 * math.log(bracket_log_n)
            - 10.0
            - math.sqrt(math.log(bracket_log_n))
        )
        / (2.0 * bracket_rate)
    )
    blocking_logs = helmert_blocking_log_terms(
        bracket_rate, bracket_log_n, sufficient_layer
    )
    print("A8-r7 exchange-point Helmert coupling-bracket verification")
    print(
        "overlap maximum covariance/lag-one error="
        f"{_maximum(overlap_covariance_errors):.3e}/"
        f"{_maximum(overlap_lag_errors):.3e}"
    )
    print(
        "tested range of S_J * E||Y_J||_2^3="
        + np.array2string(
            np.array([min(overlap_third_moments), max(overlap_third_moments)]),
            precision=10,
        )
    )
    print(f"small-block maximum Rosenthal ratio={max(exact_block_ratios):.10f}")
    print(
        "sufficient-region log error terms (deleted, CMU Gaussian, CMU rare)="
        + np.array2string(np.asarray(blocking_logs), precision=10)
    )
    print(
        "critical-window maximum |log(n*S_J^2)-(c-log 4)|="
        f"{max(critical_constant_errors):.3e}"
    )


if __name__ == "__main__":
    main()
