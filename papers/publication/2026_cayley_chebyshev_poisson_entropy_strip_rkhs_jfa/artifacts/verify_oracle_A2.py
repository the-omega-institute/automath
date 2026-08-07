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


@dataclass
class Check:
    name: str
    passed: bool
    evidence: str


def symbolic_checks() -> list[Check]:
    x, t = sp.symbols("x t", real=True, positive=True)
    a = sp.I * x / (2 * t - sp.I * x)
    checks: list[Check] = []

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
    return checks


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
        + [critical_bregman_check()]
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
