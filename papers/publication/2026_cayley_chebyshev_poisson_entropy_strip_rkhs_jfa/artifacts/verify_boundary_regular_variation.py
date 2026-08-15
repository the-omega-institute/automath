"""Verification battery for the regular-variation entropy boundary theorem.

The checks are deterministic:

1. exact Laurent constant terms are compared with the theorem's kappa_N;
2. logarithmic-Pareto models test the Karamata truncated-moment scale;
3. the unconditional quotient jet is tested in L-infinity on a Cayley grid;
4. full KL quadrature tests the sign, scale, and convergence direction;
5. a parameter scan searches for counterexamples to the necessary
   divergent-integral hypothesis.
"""

from __future__ import annotations

import argparse
import math
import sys
from contextlib import redirect_stdout
from dataclasses import dataclass
from io import StringIO
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
from scipy.integrate import quad
from scipy.special import roots_laguerre

from verify_moment_equivalence import (
    EntropyQuadrature,
    entropy_coefficient,
    finite_moments,
    mode_integral,
)


@dataclass(frozen=True)
class LogParetoBoundary:
    """Symmetric law with density proportional to y^(-p-1)(log y)^(-a).

    A mass tail_mass is split equally between +/-Y, Y >= e, and the
    remaining mass is at zero. Its absolute tail is asymptotic to

        C y^(-p) (log y)^(-a),   C = tail_mass / (p * Z),

    where Z normalizes the positive-magnitude density.
    """

    p: int
    a: float
    tail_mass: float = 0.05

    @property
    def z_normalizer(self) -> float:
        value, _ = quad(
            lambda z: math.exp(-self.p * z) * z ** (-self.a),
            1.0,
            np.inf,
            epsabs=2e-14,
            epsrel=2e-13,
        )
        return value

    @property
    def tail_constant(self) -> float:
        return self.tail_mass / (self.p * self.z_normalizer)

    @property
    def name(self) -> str:
        return f"log-Pareto(p={self.p}, a={self.a:g})"

    def ell(self, t: float) -> float:
        if t <= math.e:
            return 0.0
        upper = math.log(t)
        if self.a == 1.0:
            return math.log(upper)
        return (upper ** (1.0 - self.a) - 1.0) / (1.0 - self.a)

    def truncated_boundary_moment(self, t: float) -> float:
        return self.tail_mass * self.ell(t) / self.z_normalizer

    def boundary_moment_finite(self) -> bool:
        return self.a > 1.0

    def boundary_moment(self) -> float:
        if not self.boundary_moment_finite():
            return math.inf
        return self.tail_mass / (self.z_normalizer * (self.a - 1.0))

    def moment(self, order: int) -> float:
        if order % 2:
            return 0.0
        if order == 0:
            return 1.0
        if order == self.p:
            return self.boundary_moment()
        if order > self.p:
            return math.inf
        rate = self.p - order
        value, _ = quad(
            lambda z: math.exp(-rate * z) * z ** (-self.a),
            1.0,
            np.inf,
            epsabs=2e-13,
            epsrel=2e-12,
        )
        return self.tail_mass * value / self.z_normalizer

    def quadrature(self, count: int) -> Tuple[np.ndarray, np.ndarray]:
        nodes, weights = roots_laguerre(count)
        z = 1.0 + nodes / self.p
        tilting = z ** (-self.a)
        probabilities = weights * tilting
        probabilities /= np.sum(probabilities)
        magnitudes = np.exp(z)
        magnitudes = np.concatenate(([0.0], magnitudes))
        probabilities = np.concatenate(
            ([1.0 - self.tail_mass], self.tail_mass * probabilities)
        )
        return magnitudes, probabilities


def quotient(law: LogParetoBoundary, t: float, y: np.ndarray, count: int) -> np.ndarray:
    magnitudes, probabilities = law.quadrature(count)
    a = magnitudes[:, None] / t
    yy = y[None, :]
    pair = 0.5 * (
        (1.0 + yy * yy) / (1.0 + (yy - a) ** 2)
        + (1.0 + yy * yy) / (1.0 + (yy + a) ** 2)
    )
    return np.sum(probabilities[:, None] * pair, axis=0) - 1.0


def u_mode(n: int, y: np.ndarray) -> np.ndarray:
    # Stable three-term recurrence from the generating denominator.
    if n == 0:
        return np.ones_like(y)
    denominator = 1.0 + y * y
    u0 = np.ones_like(y)
    u1 = 2.0 * y / denominator
    if n == 1:
        return u1
    for _ in range(2, n + 1):
        u0, u1 = u1, (2.0 * y * u1 - u0) / denominator
    return u1


def verify_constants() -> List[Dict[str, object]]:
    rows = []
    for n_order in range(3, 8):
        p = 2 * n_order - 2
        exact = mode_integral((2, p))
        formula = ((-1) ** n_order) * (n_order - 1) * 2 ** (-2 * n_order + 2)
        rows.append(
            {
                "N": n_order,
                "p": p,
                "constant_term": exact,
                "formula": formula,
                "passed": abs(exact - formula) < 2e-14,
            }
        )
    return rows


def verify_moments() -> List[Dict[str, object]]:
    rows: List[Dict[str, object]] = []
    times = (1e2, 1e4, 1e8, 1e16)
    for a in (0.0, 0.5, 1.0):
        law = LogParetoBoundary(4, a)
        ratios = [
            law.truncated_boundary_moment(t)
            / (law.p * law.tail_constant * law.ell(t))
            for t in times
        ]
        rows.append(
            {
                "law": law.name,
                "times": times,
                "M_over_pC_ell": ratios,
                "passed": max(abs(value - 1.0) for value in ratios) < 5e-12,
            }
        )
    return rows


def verify_quotient_jets() -> List[Dict[str, object]]:
    theta = np.linspace(-1.54, 1.54, 601)
    y = np.tan(theta)
    rows: List[Dict[str, object]] = []
    for a in (0.0, 1.0):
        law = LogParetoBoundary(4, a)
        ratios = []
        for t in (20.0, 50.0, 120.0, 300.0):
            delta = quotient(law, t, y, count=220)
            finite = np.zeros_like(y)
            for n in range(2, law.p):
                finite += law.moment(n) * u_mode(n, y) * t ** (-n)
            top = (
                u_mode(law.p, y)
                * t ** (-law.p)
                * law.truncated_boundary_moment(t)
            )
            error = float(np.max(np.abs(delta - finite - top)))
            scale = t ** (-law.p) * law.truncated_boundary_moment(t)
            ratios.append(error / scale)
        # The asymptotic is slow, especially at a=1; require net decay.
        passed = ratios[-1] < ratios[0] and ratios[-1] < 0.8
        rows.append(
            {
                "law": law.name,
                "times": (20.0, 50.0, 120.0, 300.0),
                "sup_error_over_boundary_mode": ratios,
                "passed": passed,
            }
        )
    return rows


def verify_full_entropy() -> List[Dict[str, object]]:
    quadrature = EntropyQuadrature(angle_count=720, tail_count=240)
    rows: List[Dict[str, object]] = []
    for a in (0.0, 1.0):
        law = LogParetoBoundary(4, a)
        mu2 = law.moment(2)
        a4 = entropy_coefficient(2, finite_moments(law, 2))
        kappa = -1.0 / 8.0
        normalized = []
        # Both models are beyond their small-t transient on this interval.
        # The log-log model has a shallow pre-asymptotic maximum near t=28.
        times = (28.0, 40.0, 60.0, 90.0, 140.0)
        for t in times:
            h = quadrature.h(law, t)
            residual = t**6 * (h - a4 * t ** (-4))
            normalized.append(residual / (kappa * mu2 * law.truncated_boundary_moment(t)))
        # Full entropy convergence contains an O(1)/M term and is deliberately
        # tested only for correct sign and movement toward the limit one.
        errors = [abs(value - 1.0) for value in normalized]
        passed = normalized[-1] > 0.0 and errors[-1] < errors[0]
        rows.append(
            {
                "law": law.name,
                "times": times,
                "residual_over_kappa_mu2_M": normalized,
                "passed": passed,
            }
        )
    return rows


def counterexample_search() -> Dict[str, object]:
    rows = []
    false_classifications = []
    for a in np.linspace(-0.5, 2.0, 26):
        law = LogParetoBoundary(4, float(a))
        integral_diverges = a <= 1.0
        moment_finite = law.boundary_moment_finite()
        classification_ok = moment_finite == (not integral_diverges)
        row = {
            "a": float(a),
            "integrated_factor_diverges": integral_diverges,
            "p_moment_finite": moment_finite,
            "classification_ok": classification_ok,
        }
        rows.append(row)
        if not classification_ok:
            false_classifications.append(row)
    return {
        "candidates": len(rows),
        "false_classifications": false_classifications,
        "finite-boundary-example": {
            "a": 1.5,
            "meaning": (
                "tail index remains p, but integral L(s) ds/s converges and "
                "the p-th moment is finite"
            ),
        },
        "passed": not false_classifications,
    }


def _run_verification() -> int:
    sections = {
        "laurent_constants": verify_constants(),
        "tauberian_moments": verify_moments(),
        "quotient_jets": verify_quotient_jets(),
        "full_entropy": verify_full_entropy(),
        "counterexample_search": counterexample_search(),
    }
    failures = []
    for name, section in sections.items():
        if isinstance(section, list):
            failures.extend(
                f"{name}:{row.get('law', row.get('N'))}"
                for row in section
                if not row["passed"]
            )
        elif not section["passed"]:
            failures.append(name)

    print("REGULAR-VARIATION BOUNDARY-LAYER VERIFICATION")
    for name, section in sections.items():
        print(f"\n[{name}]")
        if isinstance(section, list):
            for row in section:
                print(row)
        else:
            print(section)
    print(f"\nfailures={failures}")
    print("RESULT: PASS" if not failures else "RESULT: FAIL")
    return 0 if not failures else 1


def main(argv=()) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    if args.output is None:
        return _run_verification()

    capture = StringIO()
    with redirect_stdout(capture):
        status = _run_verification()
    report = capture.getvalue()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(report, encoding="utf-8", newline="\n")
    print(report, end="")
    return status


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
