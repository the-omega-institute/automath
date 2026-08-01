"""Numerical feasibility checks for killed-reset D-MAP identifiability.

The serial model has a transient continuous-time generator with successive
rates ``rates``.  Sampling it at unit time gives T0=exp(Q); absorption is a
click and deterministically resets the next hidden state to the last phase,
so T1=(I-T0)1 e_n^T.  Its visible record is renewal.

This script checks two different questions that must not be conflated:

1. In the serial subclass, do visible coordinates recover the unordered rate
   tuple?  A Hankel pencil applied to the Palm gap-tail sequence recovers the
   sampled poles exp(-rate_i) for the explicit n=2 and n=3 examples.
2. Does killed reset alone identify a hidden kernel?  No.  A stochastic
   similarity transform gives a different nonnegative killed-reset kernel
   with exactly the same visible renewal law.

The numerical searches are evidence and diagnostics, not proofs of global
injectivity.  The associated manuscript proposition supplies the n=3 proof
under pairwise-distinct serial rates.
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
            tuple(np.round(np.sort(solution), 7))
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
        if np.linalg.norm(np.sort(solution) - target_sorted) > 1e-5
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


def report_example(rates: tuple[float, ...]) -> None:
    n_states = len(rates)
    t0, t1 = serial_killed_reset_kernels(rates)
    tails = kernel_tail_coordinates(t0, 2 * n_states)
    moments = visible_click_moments(rates, 2 * n_states + 2)
    poles = recover_sampled_poles(tails, n_states)
    recovered_rates = np.sort(-np.log(poles))
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
    print(f"Hankel recovered poles={array_string(poles)}")
    print(f"Hankel recovered unordered rates={array_string(recovered_rates)}")
    if n_states == 2:
        print(
            "three-inclusion recovered unordered rates="
            f"{array_string(recover_two_state_rates_from_three_inclusions(moments))}"
        )
    print(f"maximum moment error over all labelled permutations={permutation_error:.3e}")
    print(f"moment-map Jacobian singular values={array_string(singular_values)}")

    search = multistart_fiber_search(rates, starts=80, seed=100 + n_states)
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
    print(
        "interpretation: killed reset alone has a nontrivial hidden-kernel "
        "fiber, while the serial rate tuple is recovered here only as an "
        "unordered multiset."
    )
    print()


def main() -> None:
    print("Killed-reset D-MAP identifiability feasibility check")
    print("delta=1; all searches use deterministic random seeds")
    print()
    report_example((0.7, 1.6))
    report_example((0.7, 1.2, 2.3))

    separated = (0.7, 1.2, 2.3)
    near_collision = (0.7, 1.2, 1.2001)
    separated_singular_values = np.linalg.svd(
        finite_difference_jacobian(separated, 8), compute_uv=False
    )
    collision_singular_values = np.linalg.svd(
        finite_difference_jacobian(near_collision, 8), compute_uv=False
    )
    print("n=3 conditioning diagnostic")
    print(f"separated rates={separated}: {array_string(separated_singular_values)}")
    print(f"near-collision rates={near_collision}: {array_string(collision_singular_values)}")
    print(
        "smallest-singular-value ratio (near/separated)="
        f"{collision_singular_values[-1] / separated_singular_values[-1]:.3e}"
    )
    print()
    print("NUMERICAL CONCLUSION")
    print("- n=2: the known three-inclusion inverse recovers the unordered rate pair.")
    print("- n=3 serial subclass: the Hankel pencil recovers the unordered rate triple;")
    print("  searches found no fiber beyond permutations for the tested moments.")
    print("- unrestricted killed-reset kernels: explicit stochastic-similarity pairs")
    print("  have identical visible laws, so hidden kernels are not identifiable.")
    print("- collision strata are substantially more ill-conditioned; the promoted")
    print("  n=3 proposition therefore assumes pairwise-distinct rates.")


if __name__ == "__main__":
    main()
