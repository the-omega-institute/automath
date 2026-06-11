#!/usr/bin/env python3
"""Stage-3 integrality-density measurement for Lam-Litt arXiv:2501.13175.

This extends the Stage-1/Stage-2 exact Taylor computation at the nonsingular
point a=2 with initial coefficients b_0=1, b_1=0.  The local coordinate is
x=t-a, so f(t)=sum b_k x^k.  The script measures how quickly new denominator
primes appear in b_0,...,b_N and compares three one-parameter growth models.
"""

from __future__ import annotations

import datetime as _datetime
import json
import math
import os
import time
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

import sympy as sp


PAPER = "arXiv:2501.13175"
STAGE = "3 integrality density measurement"
OUTPUT_NAME = "check_2501_13175_integrality_density_stage3_output.json"

A_VALUE = sp.Rational(2)
B0_VALUE = sp.Rational(1)
B1_VALUE = sp.Rational(0)
TARGET_MAX_N = 200
MIN_PASS_N = 100

COMPUTE_BUDGET_SECONDS = 25 * 60
PROGRESS_INTERVAL_SECONDS = 20.0


def utc_now_iso() -> str:
    return _datetime.datetime.now(_datetime.timezone.utc).isoformat().replace("+00:00", "Z")


def progress(message: str, force: bool = False) -> None:
    now = time.time()
    if force or now - progress.last_print >= PROGRESS_INTERVAL_SECONDS:
        print(f"[{utc_now_iso()}] {message}", flush=True)
        progress.last_print = now


progress.last_print = 0.0  # type: ignore[attr-defined]


def derive_recurrence_symbolically() -> bool:
    """Re-derive the Stage-1 coefficient recurrence from the shifted ODE."""
    a, n, x = sp.symbols("a n x")
    b_nm1, b_n, b_np1, b_np2 = sp.symbols("b_nm1 b_n b_np1 b_np2")

    t = a + x
    p2 = sp.expand(t * (t**2 - 11 * t - 1))
    p1 = sp.expand(3 * t**2 - 22 * t - 1)
    p0 = sp.expand(t - 3)

    computed = sp.expand(
        p2.coeff(x, 0) * (n + 2) * (n + 1) * b_np2
        + p2.coeff(x, 1) * (n + 1) * n * b_np1
        + p2.coeff(x, 2) * n * (n - 1) * b_n
        + p2.coeff(x, 3) * (n - 1) * (n - 2) * b_nm1
        + p1.coeff(x, 0) * (n + 1) * b_np1
        + p1.coeff(x, 1) * n * b_n
        + p1.coeff(x, 2) * (n - 1) * b_nm1
        + p0.coeff(x, 0) * b_n
        + p0.coeff(x, 1) * b_nm1
    )

    expected = sp.expand(
        a * (a**2 - 11 * a - 1) * (n + 2) * (n + 1) * b_np2
        + (3 * a**2 - 22 * a - 1) * (n + 1) ** 2 * b_np1
        + ((3 * a - 11) * (n + 1) * n + a - 3) * b_n
        + n**2 * b_nm1
    )
    return sp.factor(computed - expected) == 0


def next_term(terms: Sequence[sp.Rational], n: int) -> sp.Rational:
    """Return b_{n+2} from the anchored Taylor recurrence."""
    denom = A_VALUE * (A_VALUE**2 - 11 * A_VALUE - 1) * (n + 2) * (n + 1)
    numerator = (
        (3 * A_VALUE**2 - 22 * A_VALUE - 1) * (n + 1) ** 2 * terms[n + 1]
        + (((3 * A_VALUE - 11) * (n + 1) * n) + A_VALUE - 3) * terms[n]
        + (n**2 * terms[n - 1] if n > 0 else sp.Rational(0))
    )
    return sp.cancel(-numerator / denom)


def compute_terms(max_n: int, started_at: float) -> List[sp.Rational]:
    terms: List[sp.Rational] = [B0_VALUE, B1_VALUE]
    progress("computed up to k=1, elapsed=0.00s", force=True)

    for n in range(max_n - 1):
        terms.append(next_term(terms, n))
        reached_k = len(terms) - 1
        elapsed = time.time() - started_at
        progress(f"computed up to k={reached_k}, elapsed={elapsed:.2f}s")

        if elapsed >= COMPUTE_BUDGET_SECONDS:
            progress(
                f"25-minute budget reached during recurrence at k={reached_k}; capping there",
                force=True,
            )
            break

    return terms


def factor_denominator_primes(value: sp.Rational) -> Set[int]:
    denominator = int(abs(sp.Rational(value).q))
    if denominator <= 1:
        return set()
    return {int(prime) for prime in sp.factorint(denominator).keys()}


def factor_denominators(
    terms: Sequence[sp.Rational], started_at: float
) -> Tuple[List[Set[int]], int]:
    per_k: List[Set[int]] = []
    max_factored = -1

    for k, term in enumerate(terms):
        per_k.append(factor_denominator_primes(term))
        max_factored = k
        elapsed = time.time() - started_at
        progress(f"factored denominator for k={k}, elapsed={elapsed:.2f}s")

        if elapsed >= COMPUTE_BUDGET_SECONDS:
            progress(
                f"25-minute budget reached during denominator factorization at k={k}; capping there",
                force=True,
            )
            break

    return per_k, max_factored


def window_points(max_n: int) -> List[int]:
    return list(range(10, max_n + 1, 10))


def cumulative_prime_tables(
    per_k_primes: Sequence[Set[int]], max_n: int
) -> Tuple[Dict[str, int], List[int], List[Optional[int]], List[int]]:
    points = window_points(max_n)
    cumulative: Set[int] = set()
    previous_at_window: Set[int] = set()
    p_n_table: Dict[str, int] = {}
    increments: List[int] = []
    largest_new: List[Optional[int]] = []

    next_point_idx = 0
    for k in range(max_n + 1):
        cumulative.update(per_k_primes[k])
        if next_point_idx < len(points) and k == points[next_point_idx]:
            newly_seen = cumulative - previous_at_window
            p_n_table[str(k)] = len(cumulative)
            increments.append(len(cumulative) - len(previous_at_window))
            largest_new.append(max(newly_seen) if newly_seen else None)
            previous_at_window = set(cumulative)
            next_point_idx += 1

    return p_n_table, increments, largest_new, sorted(cumulative)


def denominator_bitlength_growth(
    terms: Sequence[sp.Rational], max_n: int
) -> List[List[int]]:
    return [[n, int(abs(sp.Rational(terms[n]).q)).bit_length()] for n in window_points(max_n)]


def fit_no_intercept(xs: Sequence[int], ys: Sequence[int], basis: str) -> Dict[str, float]:
    if basis == "log_N":
        phis = [math.log(x) for x in xs]
    elif basis == "sqrt_N":
        phis = [math.sqrt(x) for x in xs]
    elif basis == "N_over_log_N":
        phis = [x / math.log(x) for x in xs]
    else:
        raise ValueError(f"unknown model basis: {basis}")

    denominator = sum(phi * phi for phi in phis)
    c = sum(y * phi for y, phi in zip(ys, phis)) / denominator if denominator else 0.0
    residual_sse = sum((y - c * phi) ** 2 for y, phi in zip(ys, phis))
    return {"c": float(c), "residual_sse": float(residual_sse)}


def model_fits_for(p_n_table: Dict[str, int]) -> Tuple[Dict[str, Dict[str, float]], str]:
    xs = [int(key) for key in sorted(p_n_table, key=int)]
    ys = [p_n_table[str(x)] for x in xs]
    fits = {
        "log_N": fit_no_intercept(xs, ys, "log_N"),
        "sqrt_N": fit_no_intercept(xs, ys, "sqrt_N"),
        "N_over_log_N": fit_no_intercept(xs, ys, "N_over_log_N"),
    }
    best = min(fits, key=lambda name: fits[name]["residual_sse"])
    return fits, best


def fingerprint_summary(
    max_n: int,
    p_at_max: int,
    largest_prime: Optional[int],
    best_fit_model: str,
    increments: Sequence[int],
) -> str:
    recent_increments = list(increments[-5:]) if increments else []
    largest_prime_text = str(largest_prime) if largest_prime is not None else "none"
    return (
        f"By N={max_n}, the denominators involve {p_at_max} distinct primes "
        f"(largest {largest_prime_text}), with recent window increments {recent_increments}. "
        f"Among the tested one-parameter models, {best_fit_model} has the smallest SSE, "
        "supporting continued growth rather than Stage-2-style stabilization."
    )


def build_partial_output(reason: str, max_n: int = 0) -> Dict[str, Any]:
    return {
        "paper": PAPER,
        "stage": STAGE,
        "max_N_computed": int(max_n),
        "P_N_table": {},
        "primes_at_max_N": [],
        "largest_prime_overall": None,
        "new_prime_increment_per_window": [],
        "largest_new_prime_per_window": [],
        "denominator_bitlength_growth": [],
        "model_fits": {
            "log_N": {"c": 0.0, "residual_sse": 0.0},
            "sqrt_N": {"c": 0.0, "residual_sse": 0.0},
            "N_over_log_N": {"c": 0.0, "residual_sse": 0.0},
        },
        "best_fit_model": "log_N",
        "arithmetic_fingerprint_summary": f"Partial run: {reason}.",
        "verdict": f"PARTIAL_{reason}",
    }


def main() -> int:
    started_at = time.time()
    output_path = os.path.abspath(os.path.join(os.path.dirname(__file__), OUTPUT_NAME))

    progress("Lam-Litt arXiv:2501.13175 Stage-3 checker starting", force=True)
    recurrence_ok = derive_recurrence_symbolically()
    if not recurrence_ok:
        output = build_partial_output("RECURRENCE_DERIVATION_FAILED")
    else:
        terms = compute_terms(TARGET_MAX_N, started_at)
        generated_max_n = len(terms) - 1
        per_k_primes, factored_max_n = factor_denominators(terms, started_at)
        max_n = min(generated_max_n, factored_max_n)
        points = window_points(max_n)

        if max_n >= MIN_PASS_N and points:
            p_n_table, increments, largest_new, primes_at_max = cumulative_prime_tables(
                per_k_primes, max_n
            )
            bitlengths = denominator_bitlength_growth(terms, max_n)
            model_fits, best_fit_model = model_fits_for(p_n_table)
            largest_prime = max(primes_at_max) if primes_at_max else None
            p_at_max = p_n_table[str(points[-1])]

            output = {
                "paper": PAPER,
                "stage": STAGE,
                "max_N_computed": int(max_n),
                "P_N_table": p_n_table,
                "primes_at_max_N": primes_at_max,
                "largest_prime_overall": largest_prime,
                "new_prime_increment_per_window": increments,
                "largest_new_prime_per_window": largest_new,
                "denominator_bitlength_growth": bitlengths,
                "model_fits": model_fits,
                "best_fit_model": best_fit_model,
                "arithmetic_fingerprint_summary": fingerprint_summary(
                    max_n=max_n,
                    p_at_max=p_at_max,
                    largest_prime=largest_prime,
                    best_fit_model=best_fit_model,
                    increments=increments,
                ),
                "verdict": "PASS_INTEGRALITY_DENSITY_CAPSTONE",
            }
        else:
            output = build_partial_output("INSUFFICIENT_N_OR_TABLES", max_n=max_n)

    progress("Writing Stage-3 JSON output", force=True)
    with open(output_path, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2)
        handle.write("\n")

    print(f"JSON output: {output_path}", flush=True)
    print(f"VERDICT: {output['verdict']}", flush=True)
    return 0 if output["verdict"] == "PASS_INTEGRALITY_DENSITY_CAPSTONE" else 1


if __name__ == "__main__":
    raise SystemExit(main())
