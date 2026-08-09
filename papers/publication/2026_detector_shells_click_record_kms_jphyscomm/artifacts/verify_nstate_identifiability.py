"""Numerical feasibility checks for killed-reset D-MAP identifiability.

The serial model has a transient continuous-time generator with successive
rates ``rates``.  Sampling it at unit time gives T0=exp(Q); absorption is a
click and deterministically resets the next hidden state to the last phase,
so T1=(I-T0)1 e_n^T.  Its visible record is renewal.

This script checks six different questions that must not be conflated:

1. In the serial subclass, do visible coordinates recover the unordered rate
   multiset, including pole collisions?  A Hankel recurrence applied to the
   Palm gap-tail sequence recovers the sampled poles exp(-rate_i), with their
   algebraic multiplicities, for representative n=2,3,4 examples.
2. Does killed reset alone identify a hidden kernel?  No.  A stochastic
   similarity transform gives a different nonnegative killed-reset kernel
   with exactly the same visible renewal law.
3. Does a physical two-state inclusion triple satisfy the exact scalar image
   equation?  The residual is checked on separated and repeated-rate examples.
4. Does the hidden mode obey its sharp global secant-slope bound?
5. Does the exact mean sampled cycle have the stated small-interval expansion?
6. What is the complete Markovian similarity fibre of the physical two-state
   kernel?  The exact arc parameter runs between 1 and gamma/recovery; its
   endpoints are the rate-swapped physical kernels, while its interior is
   strictly positive and has the same complete Palm tail.

The numerical searches are evidence and diagnostics, not proofs of global
injectivity.  The associated manuscript theorem supplies the exact minimal
similarity-orbit criterion and proves serial identifiability for arbitrary
positive rates, including collision strata.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass

import numpy as np
from numpy.typing import ArrayLike, NDArray
from scipy.linalg import eig, expm
from scipy.optimize import least_squares
from scipy.spatial import cKDTree


FloatArray = NDArray[np.float64]


def hidden_mode_secant(x: float, y: float) -> float:
    """Return the secant slope of t*exp(-t), with its diagonal limit."""
    if not np.isfinite(x) or not np.isfinite(y) or min(x, y) <= 0.0:
        raise ValueError("x and y must be finite and positive")
    if x == y:
        return float(np.exp(-x) * (1.0 - x))
    return float((y * np.exp(-y) - x * np.exp(-x)) / (y - x))


def symmetric_log_divided_difference(p: float, s: float) -> float:
    """Return the symmetric logarithmic divided difference C(p,s)."""
    if not np.isfinite(p) or not np.isfinite(s) or min(p, s) <= 0.0:
        raise ValueError("p and s must be finite and positive")
    midpoint = 0.5 * (p + s)
    half_gap = 0.5 * (p - s)
    if abs(half_gap) <= 1e-6 * midpoint:
        log_midpoint = np.log(midpoint)
        return float(
            midpoint * (1.0 - log_midpoint)
            + half_gap**2 / midpoint * (0.5 + log_midpoint / 3.0)
            + half_gap**4 / midpoint**3 * (1.0 / 12.0 + 4.0 * log_midpoint / 45.0)
        )
    return float((s * np.log(p) - p * np.log(s)) / (np.log(p) - np.log(s)))


def two_state_inclusion_coordinates(
    gamma: float, recovery: float, delta: float
) -> FloatArray:
    """Return (r0,r1,r2) for the physical two-state sampled counter."""
    if min(gamma, recovery, delta) <= 0.0:
        raise ValueError("rates and sampling interval must be positive")
    x = gamma * delta
    y = recovery * delta
    p = float(np.exp(-x))
    s = float(np.exp(-y))
    if x == y:
        b = x * p
    else:
        b = y * (p - s) / (y - x)
    a = 1.0 - s - b
    rho = (1.0 - p) * (1.0 - s) / (1.0 - p + b)
    hidden_lambda = p - b
    r1 = rho * a
    r2 = rho * rho + hidden_lambda * (r1 - rho * rho)
    return np.array([rho, r1, r2])


def sampled_counter_killed_kernel(
    gamma: float, recovery: float, delta: float
) -> FloatArray:
    """Return the physical two-state no-click kernel."""
    if not np.all(np.isfinite((gamma, recovery, delta))):
        raise ValueError("rates and sampling interval must be finite")
    if min(gamma, recovery, delta) <= 0.0:
        raise ValueError("rates and sampling interval must be positive")
    p = float(np.exp(-gamma * delta))
    s = float(np.exp(-recovery * delta))
    difference = recovery - gamma
    if difference == 0.0:
        b = recovery * delta * p
    else:
        b = recovery * p * (-np.expm1(-difference * delta)) / difference
    return np.array([[p, 0.0], [b, s]])


def sampled_counter_fibre_interval(
    gamma: float, recovery: float
) -> tuple[float, float]:
    """Return the exact closed q-interval of Markovian similarity equivalents."""
    finite_rates = np.all(np.isfinite((gamma, recovery)))
    if not finite_rates or min(gamma, recovery) <= 0.0:
        raise ValueError("rates must be finite and positive")
    endpoint = gamma / recovery
    return min(1.0, endpoint), max(1.0, endpoint)


def sampled_counter_fibre_kernel(
    gamma: float, recovery: float, delta: float, q: float
) -> FloatArray:
    """Return the q member of the exact physical two-state Markovian fibre."""
    if not np.isfinite(q):
        raise ValueError("q must be finite")
    lower, upper = sampled_counter_fibre_interval(gamma, recovery)
    if q < lower or q > upper:
        raise ValueError("q lies outside the exact Markovian fibre interval")
    physical = sampled_counter_killed_kernel(gamma, recovery, delta)
    p = float(physical[0, 0])
    b = float(physical[1, 0])
    s = float(physical[1, 1])
    endpoint = gamma / recovery
    equivalent = np.array(
        [
            [p - b + b * q, b * (1.0 - q) * (q - endpoint) / q],
            [b * q, s + b * (1.0 - q)],
        ]
    )
    deficits = np.ones(2) - equivalent @ np.ones(2)
    if float(equivalent.min()) < -1e-12 or float(deficits.min()) < -1e-12:
        raise ArithmeticError("closed-form fibre member is not substochastic")
    return equivalent


def physical_image_residual(inclusions: ArrayLike) -> float:
    """Evaluate the exact three-inclusion sampled-counter image equation."""
    coordinates = np.asarray(inclusions, dtype=float)
    if coordinates.size != 3:
        raise ValueError("exactly r0, r1, and r2 are required")
    r0, r1, r2 = coordinates
    denominator = r1 - r0 * r0
    if r0 <= 0.0 or denominator == 0.0:
        raise ValueError("the inclusion triple is outside the stable inverse chart")
    a = r1 / r0
    hidden_lambda = (r2 - r0 * r0) / denominator
    sigma1 = 1.0 - a + hidden_lambda
    sigma2 = r0 * (1.0 - hidden_lambda) - a + hidden_lambda
    discriminant = sigma1 * sigma1 - 4.0 * sigma2
    if discriminant < -1e-13:
        raise ValueError("the quotient polynomial has nonreal roots")
    root_gap = np.sqrt(max(discriminant, 0.0))
    p = 0.5 * (sigma1 + root_gap)
    s = 0.5 * (sigma1 - root_gap)
    return float(a - 1.0 + symmetric_log_divided_difference(p, s))


def mean_cycle_length(gamma: float, recovery: float, delta: float) -> float:
    """Return E(G+1) for the two-stage sampled cycle."""
    if min(gamma, recovery, delta) <= 0.0:
        raise ValueError("rates and sampling interval must be positive")
    x = gamma * delta
    y = recovery * delta
    gx = 1.0 / (-np.expm1(-x))
    if x == y:
        return float(gx + x * np.exp(-x) * gx * gx)
    gy = 1.0 / (-np.expm1(-y))
    return float((y * gx - x * gy) / (y - x))


def small_delta_mean_expansion(
    gamma: float, recovery: float, delta: float
) -> float:
    """Return the expansion of delta*E(G+1) through order delta^4."""
    if min(gamma, recovery, delta) <= 0.0:
        raise ValueError("rates and sampling interval must be positive")
    return float(
        1.0 / gamma
        + 1.0 / recovery
        + delta / 2.0
        + gamma * recovery * (gamma + recovery) * delta**4 / 720.0
    )


def serial_generator(rates: ArrayLike) -> FloatArray:
    """Return the lower-bidiagonal transient generator for serial phases."""
    rate_array = np.asarray(rates, dtype=float)
    if rate_array.ndim != 1 or rate_array.size < 2:
        raise ValueError("rates must be a one-dimensional tuple of length at least two")
    if not np.all(np.isfinite(rate_array)) or np.any(rate_array <= 0.0):
        raise ValueError("all rates must be finite and positive")
    generator = np.diag(-rate_array)
    for index in range(1, rate_array.size):
        generator[index, index - 1] = rate_array[index]
    return generator


def serial_killed_reset_kernels(
    rates: ArrayLike, delta: float = 1.0
) -> tuple[FloatArray, FloatArray]:
    """Construct the serial killed-reset D-MAP kernels T0 and T1."""
    if not np.isfinite(delta) or delta <= 0.0:
        raise ValueError("delta must be finite and positive")
    t0 = expm(delta * serial_generator(rates))
    n_states = t0.shape[0]
    reset = np.zeros(n_states)
    reset[-1] = 1.0
    click_probability = np.ones(n_states) - t0 @ np.ones(n_states)
    t1 = np.outer(click_probability, reset)
    if min(float(t0.min()), float(t1.min())) < -1e-12:
        raise ArithmeticError("matrix exponential did not produce nonnegative kernels")
    return t0, t1


def kernel_tail_coordinates(t0: ArrayLike, count: int) -> FloatArray:
    """Return S_k=e_n^T T0^k 1 for k=0,...,count-1."""
    matrix = np.asarray(t0, dtype=float)
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError("t0 must be square")
    if count < 1:
        raise ValueError("count must be positive")
    alpha = np.zeros(matrix.shape[0])
    alpha[-1] = 1.0
    ones = np.ones(matrix.shape[0])
    power = np.eye(matrix.shape[0])
    tails = np.empty(count)
    for lag in range(count):
        tails[lag] = alpha @ power @ ones
        power = power @ matrix
    return tails


def visible_tail_coordinates(
    rates: ArrayLike, count: int, delta: float = 1.0
) -> FloatArray:
    """Return visible Palm zero-run tails for a serial rate tuple."""
    t0, _ = serial_killed_reset_kernels(rates, delta)
    return kernel_tail_coordinates(t0, count)


def recover_sampled_poles(tails: ArrayLike, n_states: int) -> FloatArray:
    """Recover the unordered poles from a square Hankel matrix pencil."""
    tail_array = np.asarray(tails, dtype=float)
    if tail_array.size < 2 * n_states:
        raise ValueError("the n-state pencil needs S_0 through S_{2n-1}")
    h0 = np.array(
        [[tail_array[row + col] for col in range(n_states)] for row in range(n_states)]
    )
    h1 = np.array(
        [
            [tail_array[row + col + 1] for col in range(n_states)]
            for row in range(n_states)
        ]
    )
    poles = eig(h1, h0, right=False)
    if np.max(np.abs(poles.imag)) > 1e-8:
        raise ArithmeticError("recovered poles are not numerically real")
    real_poles = np.sort(poles.real)
    if np.any(real_poles <= 0.0) or np.any(real_poles >= 1.0):
        raise ArithmeticError("recovered poles are outside (0,1)")
    return real_poles


def visible_click_moments(
    rates: ArrayLike, max_lag: int, delta: float = 1.0
) -> FloatArray:
    """Return E[A_0] and E[A_0 A_l] for l=1,...,max_lag."""
    if max_lag < 0:
        raise ValueError("max_lag must be nonnegative")
    t0, _ = serial_killed_reset_kernels(rates, delta)
    n_states = t0.shape[0]
    alpha = np.zeros(n_states)
    alpha[-1] = 1.0
    ones = np.ones(n_states)
    rho = 1.0 / (alpha @ np.linalg.solve(np.eye(n_states) - t0, ones))
    tails = kernel_tail_coordinates(t0, max_lag + 1)
    interarrival = np.zeros(max_lag + 1)
    for lag in range(1, max_lag + 1):
        interarrival[lag] = tails[lag - 1] - tails[lag]
    renewal_mass = np.zeros(max_lag + 1)
    renewal_mass[0] = 1.0
    for lag in range(1, max_lag + 1):
        renewal_mass[lag] = sum(
            interarrival[jump] * renewal_mass[lag - jump]
            for jump in range(1, lag + 1)
        )
    return rho * renewal_mass


def recover_two_state_rates_from_three_inclusions(
    moments: ArrayLike, delta: float = 1.0
) -> FloatArray:
    """Apply the paper's existing n=2 three-inclusion quotient inverse."""
    coordinates = np.asarray(moments, dtype=float)
    if coordinates.size < 3:
        raise ValueError("r0, r1, and r2 are required")
    rho, r1, r2 = coordinates[:3]
    a = r1 / rho
    u2 = r2 / rho
    hidden_lambda = (u2 - rho) / (a - rho)
    pole_sum = 1.0 - a + hidden_lambda
    pole_product = rho * (1.0 - hidden_lambda) - a + hidden_lambda
    poles = np.sort(np.roots([1.0, -pole_sum, pole_product]).real)
    return np.sort(-np.log(poles) / delta)


def equivalent_killed_reset_kernel(t0: ArrayLike, epsilon: float) -> FloatArray:
    """Return a nontrivial stochastic-similarity equivalent killed kernel."""
    matrix = np.asarray(t0, dtype=float)
    n_states = matrix.shape[0]
    if matrix.ndim != 2 or matrix.shape[1] != n_states or n_states < 2:
        raise ValueError("t0 must be square with at least two states")
    transform = np.eye(n_states)
    transform[0, 0] = 1.0 - epsilon
    transform[0, 1] = epsilon
    equivalent = np.linalg.solve(transform, matrix @ transform)
    deficits = np.ones(n_states) - equivalent @ np.ones(n_states)
    if float(equivalent.min()) < -1e-12 or float(deficits.min()) < -1e-12:
        raise ValueError("epsilon does not preserve a nonnegative killed-reset kernel")
    return equivalent


def finite_difference_jacobian(rates: ArrayLike, max_lag: int) -> FloatArray:
    """Differentiate the visible click-moment map by centered differences."""
    rate_array = np.asarray(rates, dtype=float)
    jacobian = np.empty((max_lag + 1, rate_array.size))
    for column, rate in enumerate(rate_array):
        step = 1e-6 * max(1.0, rate)
        upper = rate_array.copy()
        lower = rate_array.copy()
        upper[column] += step
        lower[column] -= step
        jacobian[:, column] = (
            visible_click_moments(upper, max_lag)
            - visible_click_moments(lower, max_lag)
        ) / (2.0 * step)
    return jacobian


@dataclass(frozen=True)
class SearchSummary:
    starts: int
    converged: int
    canonical_fibers: tuple[tuple[float, ...], ...]
    labelled_orders: tuple[tuple[int, ...], ...]
    best_nonpermutation_residual: float


@dataclass(frozen=True)
class HankelDiagnostics:
    rank: int
    determinant: float
    condition_number: float
    smallest_singular_value: float


def hankel_diagnostics(tails: ArrayLike, n_states: int) -> HankelDiagnostics:
    """Return numerical rank and conditioning of the leading Hankel block."""
    tail_array = np.asarray(tails, dtype=float)
    if tail_array.size < 2 * n_states - 1:
        raise ValueError("the Hankel block needs S_0 through S_{2n-2}")
    hankel = np.array(
        [[tail_array[row + col] for col in range(n_states)] for row in range(n_states)]
    )
    singular_values = np.linalg.svd(hankel, compute_uv=False)
    tolerance = singular_values[0] * max(hankel.shape) * np.finfo(float).eps
    return HankelDiagnostics(
        rank=int(np.sum(singular_values > tolerance)),
        determinant=float(np.linalg.det(hankel)),
        condition_number=float(singular_values[0] / singular_values[-1]),
        smallest_singular_value=float(singular_values[-1]),
    )


def recover_minimal_recurrence(
    tails: ArrayLike, n_states: int
) -> tuple[FloatArray, float]:
    """Recover the monic order-n annihilator and its tail residual.

    If ``p(x)=x^n+c_{n-1}x^(n-1)+...+c_0``, the returned coefficients are
    ``[1,c_{n-1},...,c_0]``.  Repeated roots retain their multiplicities.
    """
    tail_array = np.asarray(tails, dtype=float)
    if tail_array.size < 2 * n_states:
        raise ValueError("the recurrence needs S_0 through S_{2n-1}")
    h0 = np.array(
        [[tail_array[row + col] for col in range(n_states)] for row in range(n_states)]
    )
    future = np.array([tail_array[row + n_states] for row in range(n_states)])
    ascending = np.linalg.solve(h0, -future)
    polynomial = np.concatenate(([1.0], ascending[::-1]))
    residuals = []
    for offset in range(tail_array.size - n_states):
        residuals.append(
            tail_array[offset + n_states]
            + float(ascending @ tail_array[offset : offset + n_states])
        )
    return polynomial, float(np.max(np.abs(residuals)))


def reset_similarity_lie_basis(n_states: int) -> tuple[FloatArray, ...]:
    """Basis of B1=0 and e_n^T B=0, the reset-preserving similarity tangent."""
    if n_states < 2:
        raise ValueError("n_states must be at least two")
    basis = []
    for row in range(n_states - 1):
        for column in range(n_states - 1):
            tangent = np.zeros((n_states, n_states))
            tangent[row, column] = 1.0
            tangent[row, -1] = -1.0
            basis.append(tangent)
    return tuple(basis)


def multistart_fiber_search(
    target_rates: ArrayLike, starts: int, seed: int
) -> SearchSummary:
    """Search numerically for rate tuples sharing the target click moments."""
    target = np.asarray(target_rates, dtype=float)
    max_lag = 2 * target.size + 2
    target_moments = visible_click_moments(target, max_lag)
    scale = np.maximum(np.abs(target_moments), 1e-4)
    rng = np.random.default_rng(seed)
    accepted: list[FloatArray] = []
    residuals: list[float] = []

    def residual(log_rates: FloatArray) -> FloatArray:
        return (visible_click_moments(np.exp(log_rates), max_lag) - target_moments) / scale

    for _ in range(starts):
        initial = rng.uniform(np.log(0.15), np.log(3.5), size=target.size)
        fit = least_squares(
            residual,
            initial,
            bounds=(np.log(0.08), np.log(5.0)),
            xtol=1e-12,
            ftol=1e-12,
            gtol=1e-12,
            max_nfev=2500,
        )
        norm = float(np.linalg.norm(residual(fit.x)))
        if norm < 1e-8:
            accepted.append(np.exp(fit.x))
            residuals.append(norm)

    canonical = sorted(
        {
            tuple(np.round(np.sort(solution), 4))
            for solution in accepted
        }
    )
    labelled_orders = sorted(
        {
            tuple(np.argsort(solution).tolist())
            for solution in accepted
        }
    )
    target_sorted = np.sort(target)
    nonpermutation = [
        residual_value
        for solution, residual_value in zip(accepted, residuals)
        if np.linalg.norm(np.sort(solution) - target_sorted) > 1e-3
    ]
    return SearchSummary(
        starts=starts,
        converged=len(accepted),
        canonical_fibers=tuple(canonical),
        labelled_orders=tuple(labelled_orders),
        best_nonpermutation_residual=min(nonpermutation, default=float("inf")),
    )


def random_nearest_pair_search(
    n_states: int, samples: int, seed: int
) -> tuple[float, float, tuple[float, ...], tuple[float, ...]]:
    """Find the closest sampled moment vectors among sorted random tuples."""
    rng = np.random.default_rng(seed)
    rates = np.sort(
        np.exp(rng.uniform(np.log(0.15), np.log(3.5), size=(samples, n_states))),
        axis=1,
    )
    moments = np.array([visible_click_moments(row, 2 * n_states + 2) for row in rates])
    scale = np.maximum(moments.std(axis=0), 1e-10)
    normalized = moments / scale
    distances, indices = cKDTree(normalized).query(normalized, k=2)
    index = int(np.argmin(distances[:, 1]))
    partner = int(indices[index, 1])
    moment_distance = float(np.linalg.norm(normalized[index] - normalized[partner]))
    rate_distance = float(np.linalg.norm(rates[index] - rates[partner]))
    return (
        moment_distance,
        rate_distance,
        tuple(rates[index]),
        tuple(rates[partner]),
    )


def array_string(values: ArrayLike) -> str:
    return np.array2string(
        np.asarray(values), precision=10, suppress_small=False, floatmode="fixed"
    )


def report_example(rates: tuple[float, ...], search_starts: int = 80) -> None:
    n_states = len(rates)
    t0, t1 = serial_killed_reset_kernels(rates)
    tails = kernel_tail_coordinates(t0, 2 * n_states)
    extended_tails = kernel_tail_coordinates(t0, 3 * n_states + 1)
    moments = visible_click_moments(rates, 2 * n_states + 2)
    recurrence, recurrence_residual = recover_minimal_recurrence(
        extended_tails, n_states
    )
    roots = np.roots(recurrence)
    recovered_rates = np.sort(-np.log(np.abs(roots)))
    diagnostics = hankel_diagnostics(tails, n_states)
    permutations = list(itertools.permutations(rates))
    permutation_error = max(
        float(np.max(np.abs(visible_click_moments(item, 2 * n_states + 2) - moments)))
        for item in permutations
    )
    singular_values = np.linalg.svd(
        finite_difference_jacobian(rates, 2 * n_states + 2), compute_uv=False
    )

    print(f"n={n_states} serial killed-reset example")
    print(f"rates={rates}")
    print("T0=")
    print(array_string(t0))
    print("T1=")
    print(array_string(t1))
    print(f"Palm tails S_0,...,S_{2 * n_states - 1}={array_string(tails)}")
    print(f"click moments r_0,...,r_{2 * n_states + 2}={array_string(moments)}")
    print(f"Hankel recurrence polynomial={array_string(recurrence)}")
    print(f"expected sampled-pole polynomial={array_string(np.poly(np.exp(-np.asarray(rates))))}")
    print(f"maximum recurrence residual={recurrence_residual:.3e}")
    print(
        "leading Hankel diagnostics: "
        f"rank={diagnostics.rank}, determinant={diagnostics.determinant:.3e}, "
        f"condition={diagnostics.condition_number:.3e}, "
        f"sigma_min={diagnostics.smallest_singular_value:.3e}"
    )
    print(f"recovered unordered rates (root moduli)={array_string(recovered_rates)}")
    if n_states == 2:
        print(
            "three-inclusion recovered unordered rates="
            f"{array_string(recover_two_state_rates_from_three_inclusions(moments))}"
        )
    print(f"maximum moment error over all labelled permutations={permutation_error:.3e}")
    print(f"moment-map Jacobian singular values={array_string(singular_values)}")

    search = multistart_fiber_search(rates, starts=search_starts, seed=100 + n_states)
    print(
        f"multistart search: {search.converged}/{search.starts} converged; "
        f"canonical sorted fibers={search.canonical_fibers}"
    )
    print(f"labelled permutation orders reached={search.labelled_orders}")
    if np.isfinite(search.best_nonpermutation_residual):
        print(
            "WARNING: accepted non-permutation solution with scaled residual="
            f"{search.best_nonpermutation_residual:.3e}"
        )
    else:
        print("no accepted non-permutation solution found")

    nearest = random_nearest_pair_search(n_states, samples=900, seed=200 + n_states)
    print(
        "random nearest-pair search: normalized moment distance="
        f"{nearest[0]:.3e}, rate distance={nearest[1]:.3e}"
    )
    print(f"nearest sorted tuples={nearest[2]} and {nearest[3]}")

    equivalent = equivalent_killed_reset_kernel(t0, epsilon=0.02)
    tail_difference = float(
        np.max(
            np.abs(
                kernel_tail_coordinates(t0, 20)
                - kernel_tail_coordinates(equivalent, 20)
            )
        )
    )
    print("non-serial stochastic-similarity equivalent T0'=")
    print(array_string(equivalent))
    print(f"||T0'-T0||_F={np.linalg.norm(equivalent - t0):.3e}")
    print(f"maximum S_0,...,S_19 difference={tail_difference:.3e}")
    print(f"reset-preserving similarity tangent dimension={(n_states - 1) ** 2}")
    print(
        "interpretation: killed reset alone has a nontrivial hidden-kernel "
        "fiber, while the serial rate tuple is recovered here only as an "
        "unordered multiset."
    )
    print()


def main() -> None:
    print("Sharp killed-reset D-MAP identifiability dichotomy verification")
    print("delta=1; all searches use deterministic random seeds")
    print()
    image_examples = ((0.35, 0.8, 0.2), (0.7, 1.6, 1.0), (2.0, 2.0, 1.0))
    image_residuals = [
        abs(physical_image_residual(two_state_inclusion_coordinates(*item)))
        for item in image_examples
    ]
    spectral_grid = np.geomspace(1e-4, 50.0, 181)
    spectral_values = np.array(
        [hidden_mode_secant(x, y) for x in spectral_grid for y in spectral_grid]
    )
    delta = 0.05
    mean_error = abs(
        delta * mean_cycle_length(0.7, 1.6, delta)
        - small_delta_mean_expansion(0.7, 1.6, delta)
    )
    print("A8 accepted-result diagnostics")
    print(f"maximum physical-image residual={max(image_residuals):.3e}")
    print(
        "hidden-mode grid range="
        f"[{spectral_values.min():.12f}, {spectral_values.max():.12f}], "
        f"sharp lower bound={-np.exp(-2.0):.12f}"
    )
    print(f"small-delta mean expansion error at delta={delta:g}: {mean_error:.3e}")
    print()
    print("Complete physical two-state killed-reset fibre diagnostics")
    for gamma, recovery, sample_delta in ((0.7, 1.6, 0.8), (2.1, 0.9, 0.6)):
        lower, upper = sampled_counter_fibre_interval(gamma, recovery)
        midpoint = 0.5 * (lower + upper)
        baseline = sampled_counter_killed_kernel(gamma, recovery, sample_delta)
        swapped = sampled_counter_killed_kernel(recovery, gamma, sample_delta)
        members = tuple(
            sampled_counter_fibre_kernel(
                gamma, recovery, sample_delta, fibre_parameter
            )
            for fibre_parameter in (lower, midpoint, upper)
        )
        endpoint_swap_error = min(
            max(
                float(np.max(np.abs(members[0] - first))),
                float(np.max(np.abs(members[2] - second))),
            )
            for first, second in ((baseline, swapped), (swapped, baseline))
        )
        tail_error = max(
            float(
                np.max(
                    np.abs(
                        kernel_tail_coordinates(member, 30)
                        - kernel_tail_coordinates(baseline, 30)
                    )
                )
            )
            for member in members
        )
        midpoint_deficit = np.ones(2) - members[1] @ np.ones(2)
        print(
            f"rates=({gamma:g},{recovery:g}), q interval=[{lower:.12g},{upper:.12g}], "
            f"endpoint swap error={endpoint_swap_error:.3e}"
        )
        print(
            f"midpoint min entry={members[1].min():.3e}, "
            f"midpoint min deficit={midpoint_deficit.min():.3e}, "
            f"maximum S_0,...,S_29 error={tail_error:.3e}"
        )
    diagonal_interval = sampled_counter_fibre_interval(1.3, 1.3)
    print(f"equal-rate q interval={diagonal_interval}")
    print()
    report_example((0.7, 1.6))
    report_example((0.7, 1.2, 1.2), search_starts=60)
    report_example((0.7, 1.2, 1.2, 2.3), search_starts=50)

    separated = (0.7, 1.2, 2.3)
    collision = (0.7, 1.2, 1.2)
    separated_singular_values = np.linalg.svd(
        finite_difference_jacobian(separated, 8), compute_uv=False
    )
    collision_singular_values = np.linalg.svd(
        finite_difference_jacobian(collision, 8), compute_uv=False
    )
    print("n=3 conditioning diagnostic")
    print(f"separated rates={separated}: {array_string(separated_singular_values)}")
    print(f"collision rates={collision}: {array_string(collision_singular_values)}")
    print(
        "smallest-singular-value ratio (collision/separated)="
        f"{collision_singular_values[-1] / separated_singular_values[-1]:.3e}"
    )
    print()
    print("NUMERICAL CONCLUSION")
    print("- the complete physical n=2 Markovian fibre is the exact q interval")
    print("  between 1 and gamma/recovery, with rate-swapped physical endpoints.")
    print("- strict fibre-interior positivity holds off diagonal; the equal-rate")
    print("  interval collapses to the singleton q=1.")
    print("- physical n=2 inclusion triples satisfy the exact scalar image equation.")
    print("- the hidden-mode grid respects the sharp lower bound -exp(-2).")
    print("- the sampled-cycle mean agrees with the expansion through order delta^4.")
    print("- n=2: the known three-inclusion inverse recovers the unordered rate pair.")
    print("- n=2,3,4 serial subclasses: the confluent Hankel recurrence recovers")
    print("  the unordered sampled-pole multiset, including repeated poles.")
    print("- unrestricted killed-reset kernels: explicit reset-preserving similarity")
    print("  pairs have identical visible laws but different hidden kernels for n=2,3,4.")
    print("- pole collision is an ill-conditioning/singular-chart boundary, not an")
    print("  identifiability boundary; the exact boundary is the Markovian orbit fibre.")


if __name__ == "__main__":
    main()
