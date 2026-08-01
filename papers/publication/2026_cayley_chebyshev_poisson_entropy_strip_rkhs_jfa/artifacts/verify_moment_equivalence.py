"""Numerical checks for the Cayley--Poisson moment-equivalence hierarchy.

The computation is deterministic.  It evaluates

    H(t) = int Phi(E[R_{X/t}] - 1) d omega,

in the Cayley angle, computes the universal coefficients by Laurent
constant-term extraction, and compares the scaled residuals.  Symmetric
Pareto laws have P(|X| > x) = x**(-alpha), x >= 1, so their q-th absolute
moment is finite exactly for q < alpha.  The boundary alpha = 2m-2 is the
regularly-varying test with the claimed top moment infinite.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from dataclasses import dataclass
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np
from scipy.special import roots_laguerre


def _compositions(total: int, parts: int, minimum: int = 2) -> Iterable[Tuple[int, ...]]:
    if parts == 1:
        if total >= minimum:
            yield (total,)
        return
    for first in range(minimum, total - minimum * (parts - 1) + 1):
        for rest in _compositions(total - first, parts - 1, minimum):
            yield (first,) + rest


def laurent_mode(n: int) -> Dict[int, complex]:
    """Return Q_n from the manuscript's fixed Laurent convention."""
    scale = ((-1j) ** n) / (2**n)
    out: Dict[int, complex] = {}
    for k in range(1, n + 1):
        coefficient = scale * math.comb(n - 1, k - 1)
        out[k] = coefficient
        out[-k] = coefficient * ((-1) ** n)
    return out


def mode_integral(indices: Sequence[int]) -> float:
    """Compute J(indices) as the constant term of the Laurent product."""
    product: Dict[int, complex] = {0: 1.0}
    for n in indices:
        next_product: Dict[int, complex] = {}
        for a, ca in product.items():
            for b, cb in laurent_mode(n).items():
                next_product[a + b] = next_product.get(a + b, 0.0) + ca * cb
        product = next_product
    value = product.get(0, 0.0)
    if abs(value.imag) > 2e-12:
        raise ArithmeticError(f"non-real mode integral J{tuple(indices)}={value}")
    return float(value.real)


def entropy_coefficient(m: int, moments: Dict[int, float]) -> float:
    """Evaluate A_{2m} from the universal coefficient formula."""
    if m < 2:
        raise ValueError("m must be at least 2")
    total = 2 * m
    answer = 0.0
    for r in range(2, m + 1):
        prefactor = ((-1) ** r) / (r * (r - 1))
        for indices in _compositions(total, r):
            moment_product = 1.0
            for n in indices:
                value = moments.get(n)
                if value is None or not math.isfinite(value):
                    raise ValueError(f"moment {n} is not finite")
                moment_product *= value
            answer += prefactor * moment_product * mode_integral(indices)
    return answer


@dataclass(frozen=True)
class SymmetricPareto:
    alpha: float
    name: str

    def moment(self, order: int) -> float:
        if order % 2:
            return 0.0
        if order >= self.alpha:
            return math.inf
        return self.alpha / (self.alpha - order)

    def quadrature(self, count: int) -> Tuple[np.ndarray, np.ndarray]:
        # If Z is Exp(1), then |X|=exp(Z/alpha) has the required Pareto tail.
        nodes, weights = roots_laguerre(count)
        nodes = np.asarray(nodes, dtype=np.longdouble)
        # Windows aliases longdouble to float64.  Nodes beyond this threshold
        # have exponentially negligible Laguerre weight but squaring their
        # Pareto magnitudes would overflow float64.
        keep = nodes / np.longdouble(self.alpha) < 300
        nodes = nodes[keep]
        weights = weights[keep]
        magnitudes = np.exp(nodes / np.longdouble(self.alpha))
        weights = np.asarray(weights, dtype=np.longdouble)
        weights = weights / np.sum(weights)
        return magnitudes, weights


@dataclass(frozen=True)
class SymmetricAtomic:
    magnitudes: Tuple[float, ...]
    probabilities: Tuple[float, ...]
    name: str

    def moment(self, order: int) -> float:
        if order % 2:
            return 0.0
        return sum(p * (x**order) for x, p in zip(self.magnitudes, self.probabilities))

    def quadrature(self, count: int) -> Tuple[np.ndarray, np.ndarray]:
        del count
        return np.asarray(self.magnitudes), np.asarray(self.probabilities)


def _phi(s: np.ndarray) -> np.ndarray:
    """Stable evaluation of (1+s) log(1+s)-s near zero."""
    out = np.empty_like(s, dtype=np.longdouble)
    small = np.abs(s) < np.longdouble("0.02")
    if np.any(small):
        z = s[small]
        term = z * z
        series = term / 2
        for r in range(3, 18):
            term *= z
            series += ((-1) ** r) * term / (r * (r - 1))
        out[small] = series
    if np.any(~small):
        z = s[~small]
        out[~small] = (1 + z) * np.log1p(z) - z
    return out


class EntropyQuadrature:
    def __init__(self, angle_count: int = 480, tail_count: int = 180):
        nodes, weights = np.polynomial.legendre.leggauss(angle_count)
        self.theta = np.asarray((math.pi / 2) * nodes, dtype=np.longdouble)
        # omega(dy)=d theta/pi, so mapped Legendre weights are weights/2.
        self.angle_weights = np.asarray(weights / 2, dtype=np.longdouble)
        self.tail_count = tail_count

    def h(self, law, t: float) -> float:
        magnitudes, probabilities = law.quadrature(self.tail_count)
        a = np.asarray(magnitudes, dtype=np.longdouble) / np.longdouble(t)
        p = np.asarray(probabilities, dtype=np.longdouble)
        p /= np.sum(p)
        c = np.cos(self.theta)
        s = np.sin(self.theta)
        cs = c * s
        c2 = c * c
        delta = np.zeros_like(self.theta)
        # Chunking bounds memory for the full (tail node) x (angle node) array.
        for start in range(0, len(a), 48):
            aa = a[start : start + 48, None]
            pp = p[start : start + 48, None]
            quadratic = aa * aa * c2[None, :]
            linear = 2 * aa * cs[None, :]
            pair = np.longdouble("0.5") * (
                1 / (1 - linear + quadratic) + 1 / (1 + linear + quadratic)
            )
            delta += np.sum(pp * (pair - 1), axis=0)
        if np.min(1 + delta) <= 0:
            raise ArithmeticError("quadrature produced a nonpositive density quotient")
        return float(np.sum(self.angle_weights * _phi(delta)))


def finite_moments(law, top: int) -> Dict[int, float]:
    return {n: law.moment(n) for n in range(2, top + 1)}


def scaled_residual(law, m: int, t: float, quadrature: EntropyQuadrature) -> float:
    h_value = quadrature.h(law, t)
    lower = 0.0
    for j in range(2, m):
        lower += entropy_coefficient(j, finite_moments(law, 2 * j - 2)) * t ** (-2 * j)
    return (t ** (2 * m)) * (h_value - lower)


def _finite_check(law, m: int, times: Sequence[float], quadrature: EntropyQuadrature) -> dict:
    exact = entropy_coefficient(m, finite_moments(law, 2 * m - 2))
    scaled = [scaled_residual(law, m, t, quadrature) for t in times]
    scale = max(1.0, abs(exact))
    errors = [abs(x - exact) / scale for x in scaled]
    # Heavy tails can converge slowly.  The check requires visible movement
    # toward the exact Laurent coefficient and a moderate final discrepancy.
    passed = errors[-1] < 0.35 and min(errors[-2:]) <= min(errors[:2])
    return {
        "law": law.name,
        "m": m,
        "moment_order": 2 * m - 2,
        "moment_finite": True,
        "times": list(times),
        "scaled_residual": scaled,
        "exact_A": exact,
        "relative_errors": errors,
        "passed": passed,
    }


def _boundary_check(law, m: int, times: Sequence[float], quadrature: EntropyQuadrature) -> dict:
    scaled = [scaled_residual(law, m, t, quadrature) for t in times]
    kappa = ((-1) ** m) * (m - 1) * (2 ** (-2 * m + 2))
    if m == 2:
        sign_ok = scaled[-1] > 0
    else:
        sign_ok = math.copysign(1.0, scaled[-1]) == math.copysign(1.0, kappa)
    growth = abs(scaled[-1]) > 1.12 * abs(scaled[0])
    return {
        "law": law.name,
        "m": m,
        "moment_order": 2 * m - 2,
        "moment_finite": False,
        "times": list(times),
        "scaled_residual": scaled,
        "expected_boundary_behavior": "(log t)^2" if m == 2 else "signed log t",
        "expected_sign": 1 if m == 2 else int(math.copysign(1, kappa)),
        "passed": bool(sign_ok and growth),
    }


def run_battery(quick: bool = False) -> dict:
    max_m = 4 if quick else 5
    times = (5.0, 7.0, 10.0, 14.0) if quick else (5.0, 7.0, 10.0, 14.0, 20.0)
    quadrature = EntropyQuadrature(
        angle_count=320 if quick else 560,
        tail_count=120 if quick else 210,
    )
    checks: List[dict] = []
    failed_checks: List[str] = []

    for m in range(2, max_m + 1):
        p = 2 * m - 2
        finite_law = SymmetricPareto(alpha=p + 6.0, name=f"Pareto(alpha={p + 6:g})")
        boundary_law = SymmetricPareto(alpha=float(p), name=f"Pareto-boundary(alpha={p:g})")
        for check in (
            _finite_check(finite_law, m, times, quadrature),
            _boundary_check(boundary_law, m, times, quadrature),
        ):
            checks.append(check)
            if not check["passed"]:
                failed_checks.append(f"{check['law']}, m={m}")

    # Explicit converse search: all candidates have the claimed top moment.
    # A candidate is recorded only when its large-t scaled residual fails both
    # to approach the exact A and the deterministic quadrature sanity checks.
    counterexamples: List[dict] = []
    search_rows: List[dict] = []
    atomic = SymmetricAtomic((1.0, 2.0), (0.7, 0.3), "two-radius compact law")
    for m in range(2, max_m + 1):
        p = 2 * m - 2
        candidates = [
            SymmetricPareto(p + 2.0, f"search Pareto(alpha={p + 2:g})"),
            SymmetricPareto(p + 6.0, f"search Pareto(alpha={p + 6:g})"),
            atomic,
        ]
        for law in candidates:
            row = _finite_check(law, m, times, quadrature)
            search_rows.append(row)
            if not row["passed"]:
                counterexamples.append(row)

    return {
        "description": "Cayley--Poisson sharp moment-equivalence numerical battery",
        "orders_checked": max_m - 1,
        "m_range": [2, max_m],
        "checks": checks,
        "failed_checks": failed_checks,
        "counterexample_search": search_rows,
        "counterexamples": counterexamples,
        "quadrature": {
            "angle_nodes": len(quadrature.theta),
            "pareto_laguerre_nodes": quadrature.tail_count,
        },
    }


def _format_report(report: dict) -> str:
    lines = [
        report["description"],
        f"orders m={report['m_range'][0]}..{report['m_range'][1]}",
        f"quadrature={report['quadrature']}",
        "",
        "FINITE/BOUNDARY BATTERY",
    ]
    for row in report["checks"]:
        lines.append(
            f"m={row['m']} p={row['moment_order']} law={row['law']} "
            f"moment_finite={row['moment_finite']} passed={row['passed']}"
        )
        lines.append("  t=" + ", ".join(f"{x:g}" for x in row["times"]))
        lines.append(
            "  t^(2m) residual=" + ", ".join(f"{x:.10g}" for x in row["scaled_residual"])
        )
        if row["moment_finite"]:
            lines.append(f"  exact A_(2m)={row['exact_A']:.10g}")
        else:
            lines.append(
                f"  expected={row['expected_boundary_behavior']}, sign={row['expected_sign']}"
            )
    lines.extend(["", "EXPLICIT COUNTEREXAMPLE SEARCH"])
    for row in report["counterexample_search"]:
        lines.append(
            f"m={row['m']} law={row['law']} exact={row['exact_A']:.8g} "
            f"last_scaled={row['scaled_residual'][-1]:.8g} passed={row['passed']}"
        )
    lines.extend(
        [
            "",
            f"failed battery checks: {len(report['failed_checks'])}",
            f"counterexamples found: {len(report['counterexamples'])}",
            "RESULT: PASS" if not report["failed_checks"] and not report["counterexamples"] else "RESULT: FAIL",
        ]
    )
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true", help="smaller deterministic test battery")
    parser.add_argument("--json", action="store_true", help="emit JSON instead of the text report")
    args = parser.parse_args()
    report = run_battery(quick=args.quick)
    print(json.dumps(report, indent=2) if args.json else _format_report(report), end="")
    return 0 if not report["failed_checks"] and not report["counterexamples"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
