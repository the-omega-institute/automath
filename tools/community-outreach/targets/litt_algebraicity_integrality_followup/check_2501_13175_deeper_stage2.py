#!/usr/bin/env python3
"""Stage-2 deeper checker for Lam-Litt arXiv:2501.13175.

This script extends the Stage-1 local Taylor check at the specialization
a=2, b_0=1, b_1=0.  The local coordinate is x=t-a, matching the Stage-1
recurrence derivation.  The requested denominator scan is for b_0,...,b_50;
the residual check computes one extra lookahead coefficient b_51 because the
coefficient of x^49 in the second-order ODE depends on b_51.
"""

from __future__ import annotations

import datetime as _datetime
import json
import math
import os
import signal
import time
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import sympy as sp


PAPER = "arXiv:2501.13175"
STAGE = "2 deeper Taylor + denominator + algebraicity probe"
OUTPUT_NAME = "check_2501_13175_deeper_stage2_output.json"
PROGRESS_INTERVAL_SECONDS = 20.0
TASK_3_TIMEOUT_SECONDS = 5 * 60

A_VALUE = sp.Rational(2)
B0_VALUE = sp.Rational(1)
B1_VALUE = sp.Rational(0)
MAX_N_REPORTED = 50
RESIDUAL_MAX_POWER = 49
ALGEBRAICITY_SERIES_ORDER = 30

_LAST_PROGRESS = 0.0


class Task3Timeout(RuntimeError):
    """Raised when the algebraicity probe exceeds its task-local time budget."""


def utc_now_iso() -> str:
    return _datetime.datetime.now(_datetime.timezone.utc).isoformat().replace("+00:00", "Z")


def progress(message: str, force: bool = False) -> None:
    """Print timestamped progress, throttled for long exact-arithmetic runs."""
    global _LAST_PROGRESS
    now = time.monotonic()
    if force or _LAST_PROGRESS == 0.0 or now - _LAST_PROGRESS >= PROGRESS_INTERVAL_SECONDS:
        print(f"[{utc_now_iso()}] {message}", flush=True)
        _LAST_PROGRESS = now


def _task3_alarm_handler(signum: int, frame: Any) -> None:
    raise Task3Timeout(
        f"algebraicity probe exceeded {TASK_3_TIMEOUT_SECONDS} seconds"
    )


def rational_string(value: Any) -> str:
    return str(sp.Rational(value))


def recurrence_terms_for_specialization(max_n: int) -> List[sp.Rational]:
    """Generate b_0,...,b_max_n from the anchored Taylor recurrence."""
    if max_n < 1:
        raise ValueError("max_n must be at least 1 for this specialization")

    terms: List[sp.Rational] = [B0_VALUE, B1_VALUE]
    for n in range(max_n - 1):
        denom = A_VALUE * (A_VALUE**2 - 11 * A_VALUE - 1) * (n + 2) * (n + 1)
        numerator = (
            (3 * A_VALUE**2 - 22 * A_VALUE - 1) * (n + 1) ** 2 * terms[n + 1]
            + (((3 * A_VALUE - 11) * (n + 1) * n) + A_VALUE - 3) * terms[n]
            + (n**2 * terms[n - 1] if n > 0 else sp.Rational(0))
        )
        terms.append(sp.cancel(-numerator / denom))
    return terms


def finite_series_residual_coefficients(
    terms: Sequence[sp.Rational], max_power: int
) -> List[sp.Rational]:
    """Return coefficients of x^0,...,x^max_power in the shifted ODE residual."""
    x = sp.symbols("x")
    t = A_VALUE + x
    series = sum(term * x**idx for idx, term in enumerate(terms))
    residual = sp.expand(
        t * (t**2 - 11 * t - 1) * sp.diff(series, x, 2)
        + (3 * t**2 - 22 * t - 1) * sp.diff(series, x)
        + (t - 3) * series
    )
    return [sp.Rational(sp.simplify(residual.coeff(x, i))) for i in range(max_power + 1)]


def task_1_extended_taylor(terms_for_residual: Sequence[sp.Rational]) -> Dict[str, Any]:
    progress("TASK 1: checking residual coefficients x^0 through x^49", force=True)
    residuals = finite_series_residual_coefficients(terms_for_residual, RESIDUAL_MAX_POWER)
    all_zero = all(coeff == 0 for coeff in residuals)

    return {
        "max_n": MAX_N_REPORTED,
        "all_residuals_zero": bool(all_zero),
        "first_few_b_n": [rational_string(term) for term in terms_for_residual[:10]],
    }


def prime_factors_of_denominator(value: sp.Rational) -> List[int]:
    denominator = int(abs(sp.Rational(value).q))
    if denominator <= 1:
        return []
    return sorted(int(prime) for prime in sp.factorint(denominator).keys())


def union_prime_factors(values: Iterable[sp.Rational]) -> List[int]:
    primes = set()
    for value in values:
        primes.update(prime_factors_of_denominator(value))
    return sorted(primes)


def task_2_denominator_scan(terms_b0_to_b50: Sequence[sp.Rational]) -> Dict[str, Any]:
    progress("TASK 2: scanning denominator prime support for b_0 through b_50", force=True)
    primes_all = union_prime_factors(terms_b0_to_b50)
    primes_20_50 = set(union_prime_factors(terms_b0_to_b50[20:51]))
    primes_20_30 = set(union_prime_factors(terms_b0_to_b50[20:31]))
    stabilization_observed = primes_20_50 == primes_20_30
    max_prime: Optional[int] = max(primes_all) if primes_all else None

    if primes_all:
        summary = (
            f"Denominators of b_0..b_50 involve {len(primes_all)} distinct primes; "
            f"max prime {max_prime}; stabilization on [20,50] versus [20,30]: "
            f"{stabilization_observed}."
        )
    else:
        summary = (
            "Denominators of b_0..b_50 are all 1; stabilization on [20,50] "
            f"versus [20,30]: {stabilization_observed}."
        )

    return {
        "summary": summary,
        "primes_appearing": primes_all,
        "max_prime": max_prime,
        "stabilization_observed": bool(stabilization_observed),
    }


def truncate_product(
    left: Sequence[sp.Rational], right: Sequence[sp.Rational], order: int
) -> List[sp.Rational]:
    out = [sp.Rational(0) for _ in range(order)]
    for i, left_coeff in enumerate(left[:order]):
        if left_coeff == 0:
            continue
        max_j = order - i
        for j, right_coeff in enumerate(right[:max_j]):
            if right_coeff != 0:
                out[i + j] += left_coeff * right_coeff
    return [sp.cancel(coeff) for coeff in out]


def shift_power_series_for_t(power: int, order: int) -> List[sp.Rational]:
    """Coefficients of (2+x)^power through x^(order-1)."""
    if power == 0:
        return [sp.Rational(1)] + [sp.Rational(0) for _ in range(order - 1)]
    return [
        sp.Rational(math.comb(power, k)) * A_VALUE ** (power - k) if k <= power else sp.Rational(0)
        for k in range(order)
    ]


def f_power_series(
    terms: Sequence[sp.Rational], max_power: int, order: int
) -> List[List[sp.Rational]]:
    powers: List[List[sp.Rational]] = [
        [sp.Rational(1)] + [sp.Rational(0) for _ in range(order - 1)]
    ]
    f_series = [sp.Rational(term) for term in terms[:order]]
    for _ in range(max_power):
        powers.append(truncate_product(powers[-1], f_series, order))
    return powers


def normalize_null_vector(vector: Sequence[Any]) -> List[int]:
    rationals = [sp.Rational(entry) for entry in vector]
    lcm_den = 1
    for entry in rationals:
        lcm_den = math.lcm(lcm_den, int(entry.q))

    integers = [int(entry * lcm_den) for entry in rationals]
    gcd_all = 0
    for entry in integers:
        gcd_all = math.gcd(gcd_all, abs(entry))
    if gcd_all:
        integers = [entry // gcd_all for entry in integers]

    first_nonzero = next((entry for entry in integers if entry != 0), 0)
    if first_nonzero < 0:
        integers = [-entry for entry in integers]
    return integers


def format_polynomial(coefficients: Sequence[int], monomials: Sequence[Tuple[int, int]]) -> str:
    pieces: List[Tuple[int, str]] = []
    for coeff, (i, j) in zip(coefficients, monomials):
        if coeff == 0:
            continue

        factors: List[str] = []
        if i == 1:
            factors.append("t")
        elif i > 1:
            factors.append(f"t^{i}")

        if j == 1:
            factors.append("f")
        elif j > 1:
            factors.append(f"f^{j}")

        monomial = "*".join(factors)
        pieces.append((coeff, monomial))

    if not pieces:
        return "0 = 0"

    rendered = ""
    for idx, (coeff, monomial) in enumerate(pieces):
        abs_coeff = abs(coeff)
        if monomial:
            coeff_text = "" if abs_coeff == 1 else str(abs_coeff) + "*"
            term_text = coeff_text + monomial
        else:
            term_text = str(abs_coeff)

        if idx == 0:
            rendered += ("-" if coeff < 0 else "") + term_text
        else:
            rendered += f" {'-' if coeff < 0 else '+'} {term_text}"

    return rendered + " = 0"


def fit_bidegree_relation(
    terms: Sequence[sp.Rational], t_degree: int, f_degree: int
) -> Optional[str]:
    order = ALGEBRAICITY_SERIES_ORDER
    monomials = [(i, j) for j in range(f_degree + 1) for i in range(t_degree + 1)]
    t_powers = [shift_power_series_for_t(i, order) for i in range(t_degree + 1)]
    f_powers = f_power_series(terms, f_degree, order)

    columns: List[List[sp.Rational]] = []
    for i, j in monomials:
        columns.append(truncate_product(t_powers[i], f_powers[j], order))

    rows = [[columns[col_idx][row_idx] for col_idx in range(len(columns))] for row_idx in range(order)]
    matrix = sp.Matrix(rows)
    nullspace = matrix.nullspace()
    if not nullspace:
        return None

    normalized = normalize_null_vector(list(nullspace[0]))
    return format_polynomial(normalized, monomials)


def task_3_algebraicity_probe(terms: Sequence[sp.Rational]) -> Dict[str, Any]:
    progress("TASK 3: starting algebraicity probe with 5-minute timeout", force=True)
    tested: List[List[int]] = []
    previous_handler = signal.getsignal(signal.SIGALRM)
    previous_timer = signal.setitimer(signal.ITIMER_REAL, 0)
    signal.signal(signal.SIGALRM, _task3_alarm_handler)
    signal.setitimer(signal.ITIMER_REAL, TASK_3_TIMEOUT_SECONDS)

    try:
        for t_degree, f_degree in [(3, 3), (5, 3)]:
            progress(f"TASK 3: fitting bidegree ({t_degree},{f_degree})", force=True)
            tested.append([t_degree, f_degree])
            polynomial_form = fit_bidegree_relation(terms, t_degree, f_degree)
            if polynomial_form is not None:
                return {
                    "bidegree_tested": tested,
                    "polynomial_found": True,
                    "polynomial_form": polynomial_form,
                }

        return {
            "bidegree_tested": tested,
            "polynomial_found": False,
            "polynomial_form": None,
        }
    except Task3Timeout as exc:
        progress(f"TASK 3: skipped after timeout: {exc}", force=True)
        return {
            "status": "skipped_timeout",
            "bidegree_tested": tested,
            "polynomial_found": False,
            "polynomial_form": None,
        }
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous_handler)
        if previous_timer and previous_timer[0] > 0:
            signal.setitimer(signal.ITIMER_REAL, previous_timer[0], previous_timer[1])


def verdict_for(
    task_1: Dict[str, Any],
    task_2: Dict[str, Any],
    task_3: Dict[str, Any],
) -> str:
    task_1_ok = task_1.get("all_residuals_zero") is True
    task_2_ok = (
        isinstance(task_2.get("primes_appearing"), list)
        and isinstance(task_2.get("stabilization_observed"), bool)
        and (task_2.get("max_prime") is None or isinstance(task_2.get("max_prime"), int))
    )
    task_3_ok = (
        task_3.get("polynomial_found") is True
        or bool(task_3.get("bidegree_tested"))
        or task_3.get("status") == "skipped_timeout"
    )

    if task_1_ok and task_2_ok and task_3_ok:
        return "PASS_DEEPER_TAYLOR_INTEGRALITY"
    if not task_1_ok:
        return "FAIL_EXTENDED_TAYLOR_RESIDUAL"
    if not task_2_ok:
        return "PARTIAL_DENOMINATOR_SCAN_INCOMPLETE"
    return "PARTIAL_ALGEBRAICITY_PROBE_INCOMPLETE"


def build_output(
    task_1: Dict[str, Any],
    task_2: Dict[str, Any],
    task_3: Dict[str, Any],
    verdict: str,
) -> Dict[str, Any]:
    return {
        "paper": PAPER,
        "stage": STAGE,
        "task_1_extended_taylor": task_1,
        "task_2_denominator_scan": task_2,
        "task_3_algebraicity_probe": task_3,
        "verdict": verdict,
    }


def main() -> int:
    output_path = os.path.abspath(os.path.join(os.path.dirname(__file__), OUTPUT_NAME))

    progress("Lam-Litt arXiv:2501.13175 Stage-2 checker starting", force=True)
    terms_b0_to_b51 = recurrence_terms_for_specialization(MAX_N_REPORTED + 1)
    terms_b0_to_b50 = terms_b0_to_b51[: MAX_N_REPORTED + 1]

    task_1 = task_1_extended_taylor(terms_b0_to_b51)
    task_2 = task_2_denominator_scan(terms_b0_to_b50)
    task_3 = task_3_algebraicity_probe(terms_b0_to_b51[:ALGEBRAICITY_SERIES_ORDER])

    verdict = verdict_for(task_1, task_2, task_3)
    output = build_output(task_1, task_2, task_3, verdict)

    progress("Writing Stage-2 JSON output", force=True)
    with open(output_path, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2)
        handle.write("\n")

    print(f"JSON output: {output_path}", flush=True)
    print(f"VERDICT: {verdict}", flush=True)
    return 0 if verdict == "PASS_DEEPER_TAYLOR_INTEGRALITY" else 1


if __name__ == "__main__":
    raise SystemExit(main())
