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
    return checks


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


def run(quick: bool) -> list[Check]:
    return symbolic_checks() + numerical_moment_matching_checks(quick) + [pareto_square_boundary_check(quick)]


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
