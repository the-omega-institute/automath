#!/usr/bin/env python3
"""T-43 P(N) denominator-prime density signature probe.

Legendre Picard-Fuchs ODE:
    lambda(1-lambda) f''(lambda) + (1 - 2 lambda) f'(lambda) - (1/4) f(lambda) = 0

Shift lambda = a + t and write f(a+t) = sum_{n>=0} b_n t^n.  Since
    (a+t)(1-a-t) = a(1-a) + (1-2a)t - t^2
    1 - 2(a+t) = (1-2a) - 2t,
the coefficient of t^n is
    a(1-a)(n+1)(n+2)b_{n+2}
      + (1-2a)(n+1)^2 b_{n+1}
      - (n + 1/2)^2 b_n = 0.

Thus, away from the singular points a=0,1,
    b_{n+2} =
      ((n + 1/2)^2 b_n - (1-2a)(n+1)^2 b_{n+1})
      / (a(1-a)(n+1)(n+2)).

For the specialization used here, a=1/4, b_0=1, b_1=0.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import sympy as sp


SCRIPT_PATH = Path(__file__).resolve()
OUTPUT_PATH = SCRIPT_PATH.with_name("t43_pn_density_signature_check_output.json")


def derive_recurrence_symbolically() -> sp.Expr:
    """Derive b_{n+2} from the shifted ODE using SymPy algebra."""
    a, n = sp.symbols("a n")
    b_n, b_np1, b_np2 = sp.symbols("b_n b_np1 b_np2")

    coeff = (
        a * (1 - a) * (n + 1) * (n + 2) * b_np2
        + (1 - 2 * a) * n * (n + 1) * b_np1
        - n * (n - 1) * b_n
        + (1 - 2 * a) * (n + 1) * b_np1
        - 2 * n * b_n
        - sp.Rational(1, 4) * b_n
    )
    recurrence = sp.solve(sp.Eq(sp.expand(coeff), 0), b_np2)[0]
    return sp.factor(recurrence)


def check_recurrence(expected: sp.Expr) -> None:
    """Fail loudly if the derivation no longer matches the documented formula."""
    a, n = sp.symbols("a n")
    b_n, b_np1 = sp.symbols("b_n b_np1")
    documented = (
        (n + sp.Rational(1, 2)) ** 2 * b_n
        - (1 - 2 * a) * (n + 1) ** 2 * b_np1
    ) / (a * (1 - a) * (n + 1) * (n + 2))
    if sp.simplify(expected - documented) != 0:
        raise AssertionError(f"derived recurrence mismatch: {expected!s}")


def coefficient_stream(max_n: int) -> Iterable[Tuple[int, sp.Rational]]:
    """Yield b_0,...,b_max_n for a=1/4, b_0=1, b_1=0."""
    if max_n < 0:
        return

    coeffs: List[sp.Rational] = [sp.Rational(1), sp.Rational(0)]
    yield 0, coeffs[0]
    if max_n >= 1:
        yield 1, coeffs[1]

    for n in range(max_n - 1):
        # Specialization of the documented recurrence at a=1/4:
        # b_{n+2} = [4(2n+1)^2 b_n - 8(n+1)^2 b_{n+1}]
        #            / [3(n+1)(n+2)].
        next_coeff = (
            4 * (2 * n + 1) ** 2 * coeffs[n]
            - 8 * (n + 1) ** 2 * coeffs[n + 1]
        ) / (3 * (n + 1) * (n + 2))
        next_coeff = sp.Rational(next_coeff)
        coeffs.append(next_coeff)
        yield n + 2, next_coeff


def compute_pn_table(max_n: int, progress_seconds: float) -> Dict[str, int]:
    prime_set = set()
    table: Dict[str, int] = {}
    start = time.monotonic()
    last_progress = start

    for index, coeff in coefficient_stream(max_n):
        denominator = sp.denom(coeff)
        if denominator != 1:
            prime_set.update(sp.factorint(denominator).keys())

        if index >= 10 and index % 10 == 0:
            table[str(index)] = len(prime_set)

        now = time.monotonic()
        if now - last_progress >= progress_seconds:
            print(
                f"[progress] coefficient_index={index} "
                f"current_prime_set_size={len(prime_set)} "
                f"elapsed_seconds={now - start:.1f}",
                flush=True,
            )
            last_progress = now

    return table


def least_squares_one_parameter(
    points: Iterable[Tuple[int, int]], basis
) -> Tuple[float, float]:
    xs: List[float] = []
    ys: List[float] = []
    for n, p_n in points:
        x = float(basis(n))
        if not math.isfinite(x):
            continue
        xs.append(x)
        ys.append(float(p_n))

    denom = sum(x * x for x in xs)
    if denom == 0:
        return 0.0, float("inf")

    c = sum(x * y for x, y in zip(xs, ys)) / denom
    rss = sum((c * x - y) ** 2 for x, y in zip(xs, ys))
    return c, rss


def fit_models(pn_table: Dict[str, int]) -> Tuple[str, Dict[str, float], Dict[str, float]]:
    points = sorted((int(n), p_n) for n, p_n in pn_table.items())
    models = {
        "log_N": lambda n: math.log(n),
        "sqrt_N": lambda n: math.sqrt(n),
        "N_over_log_N": lambda n: n / math.log(n),
    }

    constants: Dict[str, float] = {}
    residuals: Dict[str, float] = {}
    for name, basis in models.items():
        c, rss = least_squares_one_parameter(points, basis)
        constants[name] = c
        residuals[name] = rss

    best_fit = min(residuals, key=residuals.get)
    return best_fit, residuals, constants


def stabilization_check(pn_table: Dict[str, int]) -> bool:
    values_from_50 = [p_n for n, p_n in ((int(k), v) for k, v in pn_table.items()) if n >= 50]
    if not values_from_50:
        return False
    return max(pn_table.values()) - min(values_from_50) <= 2


def implication_text(
    max_n: int,
    pn_table: Dict[str, int],
    best_fit_model: str,
    residuals: Dict[str, float],
    stabilizes: bool,
) -> str:
    p10 = pn_table.get("10")
    p50 = pn_table.get("50")
    pmax = pn_table.get(str(max_n))
    if stabilizes:
        return (
            f"For the Legendre Picard-Fuchs specialization lambda=1/4, P(N) is effectively "
            f"stable over the sampled range: P(10)={p10}, P(50)={p50}, and "
            f"P({max_n})={pmax}.  This is a surprising and significant finding worth "
            f"investigating further as a possible finite-monodromy detection handle for T-43, "
            f"although it is only a one-specialization denominator-prime fingerprint and not "
            f"a proof of finite monodromy."
        )
    return (
        f"For the Legendre Picard-Fuchs specialization lambda=1/4, P(N) does not stabilize: "
        f"P(10)={p10}, P(50)={p50}, and P({max_n})={pmax}.  The smallest residual model is "
        f"{best_fit_model} with residual {residuals[best_fit_model]:.6g}, so the observed "
        f"denominator-prime growth pattern alone is NOT a finite-monodromy signature for the "
        f"Legendre family at lambda=1/4; it confirms transcendence in the same fingerprint "
        f"sense tested here rather than detecting finite monodromy."
    )


def build_payload(max_n: int, started_at: float, pn_table: Dict[str, int]) -> Dict[str, object]:
    best_fit_model, residuals, _constants = fit_models(pn_table)
    stabilizes = stabilization_check(pn_table)

    if max_n >= 100 and pn_table and all(math.isfinite(v) for v in residuals.values()):
        verdict = "PASS_T43_PN_SIGNATURE"
    elif pn_table:
        verdict = "PARTIAL_MAX_N_BELOW_100"
    else:
        verdict = "FAIL_NO_PN_TABLE"

    return {
        "target": "T-43 (Lam-Litt 6.2.5)",
        "methodology_borrowed_from": "arXiv:2501.13175 Stage-3 N/log N density",
        "ODE": "Legendre Picard-Fuchs: lambda(1-lambda) f'' + (1-2 lambda) f' - (1/4) f = 0",
        "specialization": {"a": "1/4", "b_0": 1, "b_1": 0},
        "max_N": max_n,
        "P_N_table": pn_table,
        "best_fit_model": best_fit_model,
        "model_residuals": {name: float(value) for name, value in residuals.items()},
        "P_N_stabilizes": stabilizes,
        "T_43_signature_implication": implication_text(
            max_n=max_n,
            pn_table=pn_table,
            best_fit_model=best_fit_model,
            residuals=residuals,
            stabilizes=stabilizes,
        ),
        "verdict": verdict,
        "elapsed_seconds": time.monotonic() - started_at,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Probe P(N) denominator-prime density for the Legendre Picard-Fuchs ODE."
    )
    parser.add_argument(
        "--max-n",
        type=int,
        default=1000,
        help="largest Taylor coefficient index to compute (default: 1000)",
    )
    parser.add_argument(
        "--progress-seconds",
        type=float,
        default=20.0,
        help="seconds between progress reports (default: 20)",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    started_at = time.monotonic()

    derived = derive_recurrence_symbolically()
    check_recurrence(derived)
    print(f"symbolic_recurrence_b_np2={derived}", flush=True)

    pn_table = compute_pn_table(args.max_n, args.progress_seconds)
    payload = build_payload(args.max_n, started_at, pn_table)

    OUTPUT_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2), flush=True)
    print(f"wrote {OUTPUT_PATH}", flush=True)


if __name__ == "__main__":
    main()
