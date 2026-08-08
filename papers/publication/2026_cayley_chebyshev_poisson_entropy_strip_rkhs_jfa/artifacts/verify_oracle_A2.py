"""Independent certificate for the verified A2 additions.

The symbolic rows prove the rational identities used in the manuscript.  The
quadrature rows are deterministic stress tests, not substitutes for the
analytic proofs: they test the moment-matched KL constant, the two-node Gauss
specialization, and the logarithmic Pareto square boundary on nontrivial laws.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from typing import Callable, Iterable, Sequence

import mpmath as mp
import numpy as np
import sympy as sp
from numpy.polynomial.legendre import leggauss
from scipy.special import ndtri
from scipy.stats import qmc


@dataclass
class Check:
    name: str
    passed: bool
    evidence: str


def symbolic_checks() -> list[Check]:
    x, t = sp.symbols("x t", real=True, positive=True)
    a = sp.I * x / (2 * t - sp.I * x)
    checks: list[Check] = []

    p_density, q_density = sp.symbols("p_density q_density", positive=True)
    phi_delta = p_density * sp.log(p_density) - p_density + 1
    proxy_bregman = (
        p_density * (sp.log(p_density) - sp.log(q_density))
        - p_density
        + q_density
    )
    proxy_cross_entropy = p_density * sp.log(q_density)
    chain_residual = sp.simplify(
        phi_delta
        - proxy_bregman
        - proxy_cross_entropy
        + (q_density - 1)
    )
    checks.append(
        Check(
            "covariance-proxy KL chain identity",
            chain_residual == 0,
            "pointwise residual after restoring the zero-mass proxy mode "
            f"is {chain_residual}",
        )
    )

    recurrence_residuals = []
    for k in range(1, 9):
        residual = sp.simplify(a ** (k + 1) + a**k + t * sp.diff(a**k, t) / k)
        recurrence_residuals.append(residual)
    checks.append(
        Check(
            "pointwise Cayley-mode differential recurrence",
            all(value == 0 for value in recurrence_residuals),
            f"residuals={recurrence_residuals}",
        )
    )

    real_part = sp.simplify(-sp.re(a))
    checks.append(
        Check(
            "first-mode real part",
            sp.simplify(real_part - x**2 / (4 * t**2 + x**2)) == 0,
            f"-Re(a_t)={real_part}",
        )
    )

    resolvent = sp.simplify((1 + a) / (2 * t) - 1 / (2 * t - sp.I * x))
    checks.append(
        Check(
            "first-mode Laplace resolvent identity",
            resolvent == 0,
            f"residual={resolvent}",
        )
    )

    q = sp.symbols("q", nonnegative=True)
    moment_residuals = []
    for n in range(1, 9):
        finite_sum = sum((-1) ** (j - 1) * q**j for j in range(1, n))
        residual = sp.factor(q / (1 + q) - finite_sum - (-1) ** (n - 1) * q**n / (1 + q))
        moment_residuals.append(residual)
    checks.append(
        Check(
            "all-even-moment remainder identity",
            all(value == 0 for value in moment_residuals),
            f"orders=1..8, residuals={moment_residuals}",
        )
    )

    constant_rows = []
    constants_ok = True
    for r in range(1, 11):
        claimed = sp.Rational(1, 4) ** r * sp.binomial(2 * r - 2, r - 1)
        parseval = (
            sp.Rational(1, 2)
            * 2
            * sp.Rational(1, 4) ** r
            * sum(sp.binomial(r - 1, j) ** 2 for j in range(r))
        )
        constants_ok = constants_ok and sp.simplify(claimed - parseval) == 0
        constant_rows.append(f"C_{r}={claimed}")
    checks.append(
        Check(
            "moment-matched Parseval constants",
            constants_ok,
            ", ".join(constant_rows),
        )
    )

    norm_rows = []
    norm_ok = True
    for d in range(1, 11):
        exact = sp.simplify(
            sp.gamma(sp.Rational(d + 1, 2))
            * sp.gamma(sp.Rational(d, 2) + 1)
            / (sp.sqrt(sp.pi) * sp.gamma(d + 1))
        )
        norm_ok = norm_ok and sp.simplify(exact - sp.Rational(1, 2) ** d) == 0
        norm_rows.append(f"K_{d}={exact}")
    checks.append(
        Check(
            "large-translation L2 norm constant",
            norm_ok,
            ", ".join(norm_rows),
        )
    )

    spike_rows = []
    spike_ok = True
    for d in range(1, 9):
        exponent = sp.Rational(2 * (d - 3), d + 1)
        expected_sign = -1 if d < 3 else (0 if d == 3 else 1)
        actual_sign = int(sp.sign(exponent))
        spike_ok = spike_ok and actual_sign == expected_sign
        spike_rows.append(f"d={d}: exponent={exponent}")
    checks.append(
        Check(
            "finite-covariance spike dimension exponent",
            spike_ok,
            ", ".join(spike_rows),
        )
    )

    critical_rows = []
    critical_ok = True
    for d in range(4, 41):
        a_d = sp.Rational(d + 1, 2)
        p_d = sp.Rational(4 * (d + 1), d + 5)
        q_d = sp.Rational(d + 5, d + 1)
        # Radial beta integrals after translating u=y-z.  Since
        # a_d(q_d-1)=2, the numerator is exactly (1+|u+z|^2)^2.
        j0 = sp.gamma(a_d) * sp.gamma(sp.Rational(5, 2)) / (
            sp.sqrt(sp.pi) * sp.gamma(a_d + 2)
        )
        j1 = sp.gamma(a_d) * sp.gamma(sp.Rational(3, 2)) / (
            sp.sqrt(sp.pi) * sp.gamma(a_d + 1)
        )
        quadratic = sp.simplify(2 * j1 + sp.Rational(4, d) * (j1 - j0))
        quartic = sp.simplify(j0)
        expected_quadratic = sp.Rational(2 * (d + 5), (d + 1) * (d + 3))
        expected_quartic = sp.Rational(3, (d + 1) * (d + 3))
        m_d = int(sp.floor(p_d))
        row_ok = (
            sp.simplify(p_d * q_d - 4) == 0
            and sp.simplify(a_d * (q_d - 1) - 2) == 0
            and sp.simplify(quadratic - expected_quadratic) == 0
            and sp.simplify(quartic - expected_quartic) == 0
            and sp.Rational(m_d, 1) <= p_d < sp.Rational(m_d + 1, 1)
        )
        critical_ok = critical_ok and row_ok
        if d in (4, 10, 11, 12, 40):
            critical_rows.append(
                f"d={d}: p={p_d}, q={q_d}, m={m_d}, "
                f"norm^q=1+({quadratic})|z|^2+({quartic})|z|^4"
            )
    checks.append(
        Check(
            "critical Lq translation identity",
            critical_ok,
            "; ".join(critical_rows),
        )
    )

    cluster_ok = True
    cluster_rows = []
    integer_endpoints = []
    for d in range(4, 81):
        p_d = sp.Rational(4 * (d + 1), d + 5)
        q_d = sp.Rational(d + 5, d + 1)
        row_ok = (
            p_d > 2
            and p_d < 4
            and sp.simplify(q_d - (1 + sp.Rational(4, d + 1))) == 0
            and sp.simplify(p_d * q_d - 4) == 0
            and sp.simplify(1 - p_d / (d + 1)) > 0
        )
        cluster_ok = cluster_ok and row_ok
        if p_d.q == 1:
            integer_endpoints.append((d, int(p_d)))
        if d in (4, 11, 40, 80):
            cluster_rows.append(
                f"d={d}: p={p_d}, q={q_d}, "
                f"t-growth={sp.simplify(1-p_d/(d+1))}"
            )
    cluster_ok = cluster_ok and integer_endpoints == [(11, 3)]
    checks.append(
        Check(
            "critical vague-tail exponent algebra",
            cluster_ok,
            "; ".join(cluster_rows)
            + f"; integer endpoints={integer_endpoints}",
        )
    )

    proxy_rows = []
    proxy_ok = True
    for d in range(1, 41):
        radial_inverse = sp.Rational(1, d + 1)
        radial_quadratic = sp.Rational(d, (d + 1) * (d + 3))
        normalized_mean = sp.simplify(
            sp.Rational(d + 1, 2)
            * (
                -radial_inverse
                + sp.Rational(d + 3, d) * radial_quadratic
            )
        )
        proxy_ok = proxy_ok and normalized_mean == 0
        if d in (1, 4, 11, 40):
            proxy_rows.append(
                f"d={d}: integral(b_Sigma)/tr(Sigma)={normalized_mean}"
            )
    checks.append(
        Check(
            "covariance Poisson proxy normalization",
            proxy_ok,
            "; ".join(proxy_rows),
        )
    )

    delta_symbol, log_delta, log_u = sp.symbols(
        "delta log_delta log_u"
    )
    chain_residual = sp.expand(
        (1 + delta_symbol) * log_delta
        - (1 + delta_symbol) * (log_delta - log_u)
        - (1 + delta_symbol) * log_u
    )
    checks.append(
        Check(
            "covariance proxy exact KL chain identity",
            chain_residual == 0,
            f"pointwise residual={chain_residual}",
        )
    )
    return checks


def finite_covariance_proxy_check(quick: bool) -> Check:
    """Stress the proxy cross-entropy asymptotic on anisotropic atomic laws."""

    rows = []
    passed = True
    sample_power = 18
    times = (4.0, 7.0, 12.0) if quick else (4.0, 7.0, 12.0, 20.0)

    for d in (4, 7):
        sobol = qmc.Sobol(d=d + 1, scramble=True, seed=1729 + d)
        uniform = sobol.random_base2(sample_power)
        normal = ndtri(np.clip(uniform, 1.0e-14, 1.0 - 1.0e-14))
        y = normal[:, :d] / np.abs(normal[:, d, None])
        y_norm_sq = np.sum(y * y, axis=1)

        pair_masses = np.linspace(0.45 / d, 0.75 / d, d)
        pair_masses *= 0.72 / np.sum(pair_masses)
        radii = np.linspace(0.65, 2.15, d)
        covariance = np.diag(pair_masses * radii**2)
        trace = float(np.trace(covariance))
        covariance_zero = covariance - trace * np.eye(d) / d
        iso = 3 * (d + 1) * (7 * d + 9) / (
            4 * d * (d + 3) * (d + 5) * (d + 7)
        )
        traceless = 3 * (d + 1) * (d + 3) / (4 * (d + 5) * (d + 7))
        q_value = iso * trace**2 + traceless * float(
            np.sum(covariance_zero * covariance_zero)
        )

        quadratic = np.einsum("ni,ij,nj->n", y, covariance, y)
        b_mode = (d + 1) / 2 * (
            -trace / (1 + y_norm_sq)
            + (d + 3) * quadratic / (1 + y_norm_sq) ** 2
        )

        cross_ratios = []
        scaled_defects = []
        for time in times:
            quotient = np.full(y.shape[0], 1.0 - np.sum(pair_masses))
            for axis, (mass, radius) in enumerate(zip(pair_masses, radii)):
                shift = radius / time
                dot = y[:, axis]
                plus_denominator = 1 + y_norm_sq + shift**2 - 2 * shift * dot
                minus_denominator = 1 + y_norm_sq + shift**2 + 2 * shift * dot
                quotient += 0.5 * mass * (
                    ((1 + y_norm_sq) / plus_denominator) ** ((d + 1) / 2)
                    + ((1 + y_norm_sq) / minus_denominator) ** ((d + 1) / 2)
                )

            delta = quotient - 1
            u = b_mode / time**2
            remainder = delta - u
            proxy_entropy = np.mean(
                (1 + u) * np.log1p(u) - u
                + remainder * np.log1p(u)
            )
            proxy_divergence = np.mean(
                (1 + delta) * np.log((1 + delta) / (1 + u))
                - remainder
            )
            cross_ratios.append(time**4 * proxy_entropy / q_value)
            scaled_defects.append(time**4 * proxy_divergence)

        row_ok = (
            all(np.isfinite(cross_ratios))
            and all(np.isfinite(scaled_defects))
            and all(value >= -2.0e-10 for value in scaled_defects)
            and abs(cross_ratios[-1] - 1.0) < (0.03 if quick else 0.012)
            and abs(cross_ratios[-1] - 1.0) < abs(cross_ratios[0] - 1.0)
            and scaled_defects[-1] < scaled_defects[0]
        )
        passed = passed and row_ok
        rows.append(
            f"d={d}: t^4 cross/Q={cross_ratios}, "
            f"t^4 D(h||k)={scaled_defects}"
        )

    return Check(
        "finite-covariance proxy asymptotic stress",
        passed,
        "; ".join(rows),
    )


def raw_tail_poisson_energy_check(quick: bool) -> Check:
    """Stress the exact tail split and its finite-covariance asymptotic."""

    node_count = 400 if quick else 900
    nodes, weights = leggauss(node_count)
    y = np.tan((math.pi / 2) * nodes)
    omega_weights = weights / 2
    one_plus_y_squared = 1 + y * y

    # The listed masses are total antipodal-pair masses; the remaining mass
    # is placed at zero.  The active-tail check uses t=8, so two pairs remain
    # in V_t, while the asymptotic check starts beyond the support.
    pairs = ((1.0, 0.20), (4.0, 0.12), (12.0, 0.08), (40.0, 0.05))
    variance = sum(radius * radius * mass for radius, mass in pairs)
    b_mode = variance * (
        -1 / one_plus_y_squared
        + 4 * y * y / one_plus_y_squared**2
    )
    q_value = 0.5 * float(np.sum(omega_weights * b_mode**2))

    def phi(values: np.ndarray) -> np.ndarray:
        return (1 + values) * np.log1p(values) - values

    def pair_quotient(radius: float, time: float) -> np.ndarray:
        epsilon = radius / time
        return 0.5 * (
            one_plus_y_squared / (1 + (y - epsilon) ** 2)
            + one_plus_y_squared / (1 + (y + epsilon) ** 2)
        )

    active_time = 8.0
    quotient = np.full(y.shape, 1 - sum(mass for _, mass in pairs))
    tail_potential = np.zeros_like(y)
    tail_mass = 0.0
    interior_remainder = np.zeros_like(y)
    omitted_tail_polynomial = np.zeros_like(y)
    for radius, mass in pairs:
        pair_value = pair_quotient(radius, active_time)
        quotient += mass * pair_value
        epsilon = radius / active_time
        quadratic_pair = 1 + epsilon**2 * (
            -1 / one_plus_y_squared
            + 4 * y * y / one_plus_y_squared**2
        )
        if radius <= active_time:
            interior_remainder += mass * (pair_value - quadratic_pair)
        else:
            tail_potential += mass * pair_value
            tail_mass += mass
            omitted_tail_polynomial += mass * (quadratic_pair - 1)

    delta = quotient - 1
    u_mode = b_mode / active_time**2
    reconstructed_remainder = interior_remainder - omitted_tail_polynomial
    split_error = float(
        np.max(
            np.abs(
                delta
                - u_mode
                - tail_potential
                + tail_mass
                - reconstructed_remainder
            )
        )
    )
    tail_mass_error = abs(
        float(np.sum(omega_weights * tail_potential)) - tail_mass
    )

    times = (80.0, 160.0, 320.0, 640.0) if quick else (
        80.0,
        120.0,
        200.0,
        320.0,
        500.0,
        800.0,
    )
    coefficient_ratios = []
    for time in times:
        quotient = np.full(y.shape, 1 - sum(mass for _, mass in pairs))
        for radius, mass in pairs:
            quotient += mass * pair_quotient(radius, time)
        entropy = float(np.sum(omega_weights * phi(quotient - 1)))
        coefficient_ratios.append(time**4 * entropy / q_value)

    passed = (
        split_error < 2.0e-12
        and tail_mass_error < 2.0e-12
        and all(
            coefficient_ratios[index] < coefficient_ratios[index + 1]
            for index in range(len(coefficient_ratios) - 1)
        )
        and abs(coefficient_ratios[-1] - 1) < (0.006 if quick else 0.003)
    )
    return Check(
        "raw-tail Poisson energy decomposition stress",
        passed,
        f"active-tail split residual={split_error:.3e}, "
        f"tail normalization residual={tail_mass_error:.3e}, "
        f"post-support t^4 H/Q ratios={coefficient_ratios}",
    )


def moving_annulus_comparability_check() -> Check:
    """Check the dyadic moving-annulus kernel against the Poisson kernel."""

    rows = []
    passed = True
    for d in (1, 4, 11, 40):
        exponent = (d + 1) / 2
        ratios = []
        for k in range(0, 10):
            if k == 0:
                radii = (0.0, 0.37, 0.999999)
                dyadic_weight = 1.0
            else:
                lower = 2.0 ** (k - 1)
                upper = 2.0**k
                radii = (lower, math.sqrt(lower * upper), upper * (1 - 1e-12))
                dyadic_weight = 2.0 ** (-k * (d + 1))
            ratios.extend(
                (1 + radius * radius) ** (-exponent) / dyadic_weight
                for radius in radii
            )
        row_ok = min(ratios) >= 2.0 ** (-(d + 1) / 2) - 1e-12 and max(ratios) <= 2.0 ** (d + 1) + 1e-8
        passed = passed and row_ok
        rows.append(f"d={d}: kernel-ratio range=[{min(ratios):.6g}, {max(ratios):.6g}]")

    def scalar_phi(value: float) -> float:
        return (1 + value) * math.log1p(value) - value

    multiplier_ratios = []
    for constant in (0.05, 0.3, 2.0, 10.0):
        for value in np.geomspace(1.0e-10, 1.0e10, 300):
            multiplier_ratios.append(scalar_phi(constant * value) / scalar_phi(value))
    passed = passed and min(multiplier_ratios) > 0 and math.isfinite(max(multiplier_ratios))
    rows.append(
        "Phi fixed-multiplier ratio range="
        f"[{min(multiplier_ratios):.6g}, {max(multiplier_ratios):.6g}]"
    )
    return Check("moving-annulus potential comparability", passed, "; ".join(rows))


def pre_phi_thin_shell_aggregation_check() -> Check:
    """Stress the critical scaling behind aggregation before applying Phi."""

    rows = []
    passed = True
    for d in (4, 11, 40):
        q_value = (d + 5) / (d + 1)
        b_values = np.array((2.0, 4.0, 8.0, 16.0, 32.0))
        # K=B^{3q/(q-1)} is more than sufficient for
        # B^q K^{1-q}->0, while the aggregate energy is B^q.
        log_k = 3 * q_value / (q_value - 1) * np.log(b_values)
        isolated_log_energy = q_value * np.log(b_values) + (1 - q_value) * log_k
        aggregate_log_energy = q_value * np.log(b_values)
        isolated = np.exp(isolated_log_energy)
        aggregate = np.exp(aggregate_log_energy)
        row_ok = all(np.diff(isolated) < 0) and all(np.diff(aggregate) > 0)
        passed = passed and row_ok
        rows.append(
            f"d={d}, q={q_value:.6g}: isolated={isolated.tolist()}, "
            f"aggregate={aggregate.tolist()}"
        )
    return Check("pre-Phi thin-shell aggregation scaling", passed, "; ".join(rows))


def critical_bregman_check() -> Check:
    """Stress the uniform Phi-Bregman bound at zero density and large spikes."""

    def phi(value: float) -> float:
        if value == -1.0:
            return 1.0
        return (1.0 + value) * math.log1p(value) - value

    rows = []
    passed = True
    for d in (4, 5, 10, 11, 12, 20, 40):
        q_d = (d + 5) / (d + 1)
        minimum = math.inf
        maximum_ratio = 0.0
        for u in np.linspace(-0.25, 0.25, 21):
            negative_and_local = np.linspace(-1.0 - u, 0.5001, 500)
            positive_spikes = np.geomspace(0.5001, 1.0e12, 500)
            for v in np.concatenate((negative_and_local, positive_spikes)):
                if abs(v) < 1.0e-13:
                    continue
                remainder = phi(u + v) - phi(u) - math.log1p(u) * v
                minimum = min(minimum, remainder)
                maximum_ratio = max(maximum_ratio, remainder / abs(v) ** q_d)
        row_ok = minimum >= -2.0e-10 and math.isfinite(maximum_ratio)
        passed = passed and row_ok
        rows.append(
            f"d={d}: min Bregman={minimum:.3e}, "
            f"max Bregman/|v|^q={maximum_ratio:.6g}"
        )
    return Check("critical Bregman perturbation bound", passed, "; ".join(rows))


def covariance_proxy_quadrature_check(quick: bool) -> Check:
    """Test the proxy chain identity and cross-entropy coefficient in d>=4."""

    node_count = 70 if quick else 130
    nodes, weights = leggauss(node_count)
    theta = (math.pi / 4) * (nodes + 1)
    theta_weights = (math.pi / 4) * weights
    phi = (math.pi / 2) * (nodes + 1)
    phi_weights = (math.pi / 2) * weights
    radius_nodes = np.tan(theta)

    rows = []
    passed = True
    times = (7.0, 10.0, 14.0, 20.0) if quick else (7.0, 10.0, 14.0, 20.0, 30.0)
    for d, sphere_radius in ((4, 0.8), (7, 1.3), (11, 1.7)):
        radial_weights = theta_weights * np.sin(theta) ** (d - 1)
        radial_weights /= np.sum(radial_weights)
        angular_weights = phi_weights * np.sin(phi) ** (d - 2)
        angular_weights /= np.sum(angular_weights)
        cosines = np.cos(phi)
        exponent = (d + 1) / 2
        variance = sphere_radius**2 / d
        radius_squared = radius_nodes**2
        b_sigma = exponent * (
            -sphere_radius**2 / (1 + radius_squared)
            + (d + 3)
            * variance
            * radius_squared
            / (1 + radius_squared) ** 2
        )
        q_sigma = 0.5 * float(np.sum(radial_weights * b_sigma**2))

        ratios = []
        identity_errors = []
        minimum_defect = math.inf
        rejected_times = []
        valid_times = []
        for time in times:
            epsilon = sphere_radius / time
            denominator = (
                1
                + radius_squared[:, None]
                + epsilon**2
                - 2 * radius_nodes[:, None] * epsilon * cosines[None, :]
            )
            quotient_values = np.sum(
                angular_weights[None, :]
                * ((1 + radius_squared[:, None]) / denominator) ** exponent,
                axis=1,
            )
            proxy_values = 1 + b_sigma / time**2
            if np.min(proxy_values) <= 0:
                rejected_times.append(time)
                continue
            valid_times.append(time)
            entropy = float(
                np.sum(
                    radial_weights
                    * quotient_values
                    * np.log(quotient_values)
                )
            )
            defect = float(
                np.sum(
                    radial_weights
                    * quotient_values
                    * np.log(quotient_values / proxy_values)
                )
            )
            cross_entropy = float(
                np.sum(
                    radial_weights
                    * quotient_values
                    * np.log(proxy_values)
                )
            )
            identity_errors.append(abs(entropy - defect - cross_entropy))
            minimum_defect = min(minimum_defect, defect)
            ratios.append(time**4 * cross_entropy / q_sigma)

        row_ok = (
            max(identity_errors) < 2.0e-13
            and minimum_defect > -2.0e-13
            and abs(ratios[-1] - 1) < (0.012 if quick else 0.005)
            and abs(ratios[-1] - 1) < abs(ratios[0] - 1)
        )
        passed = passed and row_ok
        rows.append(
            f"d={d}, sphere radius={sphere_radius}: "
            f"valid t={valid_times}, positivity-gate rejections={rejected_times}, "
            f"t^4 cross/Q ratios={ratios}, "
            f"max chain residual={max(identity_errors):.3e}, "
            f"min proxy KL={minimum_defect:.3e}"
        )
    return Check(
        "covariance proxy multidimensional quadrature",
        passed,
        "; ".join(rows),
    )


def quotient(y: mp.mpf, t: mp.mpf, law: Sequence[tuple[mp.mpf, mp.mpf]]) -> mp.mpf:
    return sum(weight * (1 + y * y) / (1 + (y - location / t) ** 2) for weight, location in law)


def discrete_kl(
    t: mp.mpf,
    first: Sequence[tuple[mp.mpf, mp.mpf]],
    second: Sequence[tuple[mp.mpf, mp.mpf]],
) -> mp.mpf:
    def integrand(theta: mp.mpf) -> mp.mpf:
        y = mp.tan(theta)
        p = quotient(y, t, first)
        q = quotient(y, t, second)
        return p * mp.log(p / q) / mp.pi

    return mp.quad(integrand, [-mp.pi / 2, 0, mp.pi / 2])


def numerical_moment_matching_checks(quick: bool) -> list[Check]:
    mp.mp.dps = 55
    checks: list[Check] = []

    # A four-point standardized symmetric law and its two-node Gauss rule.
    radius = mp.sqrt(mp.mpf("1.75"))
    nu = [
        (mp.mpf("0.25"), -radius),
        (mp.mpf("0.25"), -mp.mpf("0.5")),
        (mp.mpf("0.25"), mp.mpf("0.5")),
        (mp.mpf("0.25"), radius),
    ]
    gauss = [(mp.mpf("0.5"), -1), (mp.mpf("0.5"), 1)]
    kappa = mp.mpf("0.5625")
    expected = mp.mpf(5) * kappa**2 / 64
    times = (mp.mpf(5), mp.mpf(8), mp.mpf(12)) if quick else (mp.mpf(5), mp.mpf(8), mp.mpf(12), mp.mpf(20), mp.mpf(30))
    scaled = [time**8 * discrete_kl(time, nu, gauss) for time in times]
    ratios = [value / expected for value in scaled]
    checks.append(
        Check(
            "two-node Gauss fourth-moment KL constant",
            all(ratios[j] < ratios[j + 1] for j in range(len(ratios) - 1))
            and abs(ratios[-1] - 1) < (mp.mpf("0.04") if quick else mp.mpf("0.01")),
            f"expected={mp.nstr(expected, 16)}, ratios={[mp.nstr(v, 12) for v in ratios]}",
        )
    )

    # Opposite finite-difference perturbations preserve moments 0,1,2 and
    # differ first at order three by Delta_3=0.12.
    locations = [mp.mpf(j) for j in range(4)]
    signed = [mp.mpf(-1), mp.mpf(3), mp.mpf(-3), mp.mpf(1)]
    epsilon = mp.mpf("0.01")
    first = [(mp.mpf("0.25") + epsilon * signed[j], locations[j]) for j in range(4)]
    second = [(mp.mpf("0.25") - epsilon * signed[j], locations[j]) for j in range(4)]
    delta_three = sum(w * z**3 for w, z in first) - sum(w * z**3 for w, z in second)
    expected_three = mp.mpf(3) * delta_three**2 / 32
    times_three = (mp.mpf(5), mp.mpf(8), mp.mpf(12)) if quick else (mp.mpf(5), mp.mpf(8), mp.mpf(12), mp.mpf(20), mp.mpf(30))
    scaled_three = [time**6 * discrete_kl(time, first, second) for time in times_three]
    ratios_three = [value / expected_three for value in scaled_three]
    checks.append(
        Check(
            "third-moment-matched KL constant",
            all(ratios_three[j] < ratios_three[j + 1] for j in range(len(ratios_three) - 1))
            and abs(ratios_three[-1] - 1) < (mp.mpf("0.03") if quick else mp.mpf("0.01")),
            f"Delta_3={delta_three}, C_3=3/32, ratios={[mp.nstr(v, 12) for v in ratios_three]}",
        )
    )
    return checks


def pareto_square_boundary_check(quick: bool) -> Check:
    # Symmetric Pareto with P(|X|>x)=x^-4 has M_4(t)=4 log t.  Its two-node
    # Gauss law is (delta_{-sqrt(2)}+delta_{sqrt(2)})/2.
    magnitude_count = 700 if quick else 1200
    angle_count = 1100 if quick else 1800
    xu, wu = leggauss(magnitude_count)
    uniform = (xu + 1) / 2
    uniform_weights = wu / 2
    magnitudes = uniform ** (-0.25)
    xt, wt = leggauss(angle_count)
    theta = (math.pi / 2) * xt
    omega_weights = wt / 2
    y = np.tan(theta)

    def pareto_quotient(time: float) -> np.ndarray:
        answer = np.zeros_like(y)
        for start in range(0, magnitude_count, 70):
            eps = magnitudes[start : start + 70, None] / time
            yy = y[None, :]
            pair = 0.5 * (
                (1 + yy * yy) / (1 + (yy - eps) ** 2)
                + (1 + yy * yy) / (1 + (yy + eps) ** 2)
            )
            answer += np.sum(uniform_weights[start : start + 70, None] * pair, axis=0)
        return answer

    def gauss_quotient(time: float) -> np.ndarray:
        eps = math.sqrt(2) / time
        return 0.5 * (
            (1 + y * y) / (1 + (y - eps) ** 2)
            + (1 + y * y) / (1 + (y + eps) ** 2)
        )

    times = (5.0, 8.0, 12.0) if quick else (5.0, 8.0, 12.0, 20.0)
    ratios = []
    for time in times:
        q_nu = pareto_quotient(time)
        q_gauss = gauss_quotient(time)
        divergence = float(np.sum(omega_weights * q_nu * np.log(q_nu / q_gauss)))
        scaled = time**8 * divergence
        predicted = (5 / 64) * (4 * math.log(time)) ** 2
        ratios.append(scaled / predicted)
    passed = all(ratios[j] < ratios[j + 1] for j in range(len(ratios) - 1)) and ratios[-1] > (0.40 if quick else 0.47)
    return Check(
        "regular-variation Gauss square boundary",
        passed,
        f"M_4(t)=4 log(t), normalized ratios={ratios}",
    )


def critical_vague_tail_checks() -> list[Check]:
    """Stress the diffuse and clustered mechanisms in the new boundary theorem."""

    checks: list[Check] = []

    def test_function(value: float) -> float:
        if abs(value) >= 1.0:
            return 0.0
        return (1.0 - value * value) ** 2

    radial_rows = []
    radial_ok = True
    for d in (4, 11, 40):
        p_d = 4.0 * (d + 1) / (d + 5)
        target = float(
            mp.quad(
                lambda value: p_d
                * mp.exp(-p_d * value)
                * (1 - value * value) ** 2,
                [-1, 1],
            )
        )
        scales = (80.0, 800.0, 8000.0)
        errors = []
        s_values = [12.0]
        while s_values[-1] <= scales[-1] + 1.1:
            s_values.append(s_values[-1] + s_values[-1] ** (-0.5))
        for scale in scales:
            value = 0.0
            for left, right in zip(s_values[:-1], s_values[1:]):
                offset = left - scale
                if abs(offset) >= 1.1:
                    continue
                # exp(p*scale)/scale times the exact shell mass
                # integral_left^right p*u*exp(-p*u) du.
                scaled_mass = (
                    ((left + 1.0 / p_d) / scale)
                    * math.exp(-p_d * (left - scale))
                    - ((right + 1.0 / p_d) / scale)
                    * math.exp(-p_d * (right - scale))
                )
                value += scaled_mass * test_function(offset)
            errors.append(abs(value / target - 1.0))
        row_ok = errors[-1] < errors[0] and errors[-1] < 0.025
        radial_ok = radial_ok and row_ok
        radial_rows.append(f"d={d}: relative errors={errors}")
    checks.append(
        Check(
            "critical clustered-shell vague Riemann sums",
            radial_ok,
            "; ".join(radial_rows),
        )
    )

    rate_rows = []
    rate_ok = True
    log_times = (8.0, 16.0, 32.0, 64.0)
    for d in (4, 10, 11, 12, 40):
        p_d = 4.0 * (d + 1) / (d + 5)
        if d == 11:
            ratios = [math.exp(-value) * value**2 for value in log_times]
        else:
            ratios = [
                math.exp((2.0 - p_d) * value) * value
                for value in log_times
            ]
        row_ok = all(
            ratios[index + 1] < ratios[index]
            for index in range(len(ratios) - 1)
        ) and ratios[-1] < 1.0e-3
        rate_ok = rate_ok and row_ok
        rate_rows.append(f"d={d}: normalized remainder rates={ratios}")
    checks.append(
        Check(
            "critical diffuse remainder decay including d=11",
            rate_ok,
            "; ".join(rate_rows),
        )
    )

    bernoulli_rows = []
    bernoulli_ok = True
    for atom_mass in np.geomspace(1.0e-9, 1.0e-2, 16):
        convolved_mass = 0.4 * atom_mass
        reference_mass = 0.02 * atom_mass
        divergence = (
            convolved_mass * math.log(convolved_mass / reference_mass)
            + (1.0 - convolved_mass)
            * math.log(
                (1.0 - convolved_mass) / (1.0 - reference_mass)
            )
        )
        ratio = divergence / atom_mass
        bernoulli_rows.append(ratio)
        bernoulli_ok = bernoulli_ok and ratio > 0.75
    checks.append(
        Check(
            "critical cluster Bernoulli entropy lower bound",
            bernoulli_ok,
            f"D(Ber(0.4a)||Ber(0.02a))/a range="
            f"[{min(bernoulli_rows)}, {max(bernoulli_rows)}]",
        )
    )
    return checks


def run(quick: bool) -> list[Check]:
    return (
        symbolic_checks()
        + [critical_bregman_check(), covariance_proxy_quadrature_check(quick)]
        + [finite_covariance_proxy_check(quick)]
        + [
            raw_tail_poisson_energy_check(quick),
            moving_annulus_comparability_check(),
            pre_phi_thin_shell_aggregation_check(),
        ]
        + numerical_moment_matching_checks(quick)
        + [pareto_square_boundary_check(quick)]
        + critical_vague_tail_checks()
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    checks = run(args.quick)
    print("ORACLE A2 INDEPENDENT VERIFICATION")
    for check in checks:
        print(f"[{check.name}] {'PASS' if check.passed else 'FAIL'}")
        print(f"  {check.evidence}")
    failures = [check.name for check in checks if not check.passed]
    print(f"failures={failures}")
    print("RESULT: PASS" if not failures else "RESULT: FAIL")
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
