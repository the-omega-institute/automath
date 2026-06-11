#!/usr/bin/env python3
"""Stage-1 anchor for Lam-Litt arXiv:2501.13175, Proposition 4.0.1.

The paper displays a Picard-Fuchs ODE and the induced Taylor-coefficient
recurrence at a nonsingular point t=a. This checker independently re-derives
that recurrence from the ODE by exact symbolic coefficient extraction.
"""

from __future__ import annotations

import datetime as _datetime
from fractions import Fraction
import json
import os
import signal
import time
from typing import Any, Dict, List

import sympy as sp


TIME_BUDGET_SECONDS = 20 * 60
PROGRESS_INTERVAL_SECONDS = 20
OUTPUT_NAME = "check_2501_13175_stage1_output.json"
PAPER = "arXiv:2501.13175"
CLAIM_LOCATOR = "Proposition 4.0.1, Section 4, equation (4.2)"
EXPLICIT_CLAIM = (
    "For the ODE t(t^2 - 11t - 1) f''(t) + (3t^2 - 22t - 1) f'(t) + "
    "(t - 3) f(t) = 0, the Taylor coefficients f(t)=sum b_n (t-a)^n at "
    "a point with a(a^2 - 11a - 1) != 0 satisfy "
    "a(a^2 - 11a - 1)(n+2)(n+1)b_{n+2} + "
    "(3a^2 - 22a - 1)(n+1)^2 b_{n+1} + "
    "([(3a - 11)(n+1)n + a - 3])b_n + n^2 b_{n-1} = 0."
)

_START_MONOTONIC = time.monotonic()
_LAST_PROGRESS = 0.0


class VerificationAbort(RuntimeError):
    """Raised when the Stage-1 checker exceeds its runtime budget."""


def utc_now_iso() -> str:
    return _datetime.datetime.now(_datetime.timezone.utc).isoformat().replace("+00:00", "Z")


def progress(message: str, force: bool = False) -> None:
    """Print timestamped progress, throttled so long runs stay visibly alive."""
    global _LAST_PROGRESS
    now = time.monotonic()
    if force or _LAST_PROGRESS == 0.0 or now - _LAST_PROGRESS >= PROGRESS_INTERVAL_SECONDS:
        print(f"[{utc_now_iso()}] {message}", flush=True)
        _LAST_PROGRESS = now


def check_time_budget(context: str) -> None:
    elapsed = time.monotonic() - _START_MONOTONIC
    if elapsed > TIME_BUDGET_SECONDS:
        raise VerificationAbort(
            f"time budget exceeded during {context}; elapsed_seconds={elapsed:.3f}"
        )


def _alarm_handler(signum: int, frame: Any) -> None:
    raise VerificationAbort("global 20-minute alarm fired before Stage-1 completed")


def rational_string(value: Any) -> str:
    return str(sp.Rational(value))


def derive_recurrence_symbolically() -> Dict[str, Any]:
    progress("STEP 1: deriving the coefficient recurrence from the ODE", force=True)
    a, n, x = sp.symbols("a n x")
    b_nm1, b_n, b_np1, b_np2 = sp.symbols("b_nm1 b_n b_np1 b_np2")

    t = a + x
    p2 = sp.expand(t * (t**2 - 11 * t - 1))
    p1 = sp.expand(3 * t**2 - 22 * t - 1)
    p0 = sp.expand(t - 3)

    # Coefficient of x^n in p2 f'' + p1 f' + p0 f. Since p2 is cubic,
    # p1 quadratic, and p0 linear in x, only b_{n-1},...,b_{n+2} can appear.
    coeff_from_p2 = (
        p2.coeff(x, 0) * (n + 2) * (n + 1) * b_np2
        + p2.coeff(x, 1) * (n + 1) * n * b_np1
        + p2.coeff(x, 2) * n * (n - 1) * b_n
        + p2.coeff(x, 3) * (n - 1) * (n - 2) * b_nm1
    )
    coeff_from_p1 = (
        p1.coeff(x, 0) * (n + 1) * b_np1
        + p1.coeff(x, 1) * n * b_n
        + p1.coeff(x, 2) * (n - 1) * b_nm1
    )
    coeff_from_p0 = p0.coeff(x, 0) * b_n + p0.coeff(x, 1) * b_nm1
    computed = sp.expand(coeff_from_p2 + coeff_from_p1 + coeff_from_p0)

    expected = sp.expand(
        a * (a**2 - 11 * a - 1) * (n + 2) * (n + 1) * b_np2
        + (3 * a**2 - 22 * a - 1) * (n + 1) ** 2 * b_np1
        + ((3 * a - 11) * (n + 1) * n + a - 3) * b_n
        + n**2 * b_nm1
    )
    difference = sp.factor(computed - expected)
    match = difference == 0

    return {
        "computed": str(sp.factor(computed)),
        "expected": str(sp.factor(expected)),
        "difference": str(difference),
        "match": bool(match),
        "p2_shifted": str(p2),
        "p1_shifted": str(p1),
        "p0_shifted": str(p0),
    }


def recurrence_terms_for_specialization(
    a_value: Fraction,
    b0_value: Fraction,
    b1_value: Fraction,
    count: int,
) -> List[Fraction]:
    """Generate b_0,...,b_{count-1} from the anchored recurrence."""
    terms = [b0_value, b1_value]
    for n in range(count - 2):
        denom = a_value * (a_value**2 - 11 * a_value - 1) * (n + 2) * (n + 1)
        numerator = (
            (3 * a_value**2 - 22 * a_value - 1) * (n + 1) ** 2 * terms[n + 1]
            + (((3 * a_value - 11) * (n + 1) * n) + a_value - 3) * terms[n]
            + (n**2 * terms[n - 1] if n > 0 else Fraction(0))
        )
        terms.append(-numerator / denom)
    return terms


def finite_series_residual_check() -> Dict[str, Any]:
    progress("STEP 2: checking a concrete rational Taylor specialization", force=True)
    x = sp.symbols("x")
    a_value = Fraction(2, 1)
    b0_value = Fraction(1, 1)
    b1_value = Fraction(0, 1)
    term_count = 12
    terms = recurrence_terms_for_specialization(a_value, b0_value, b1_value, term_count)

    series = sum(
        sp.Rational(term.numerator, term.denominator) * x**idx
        for idx, term in enumerate(terms)
    )
    t = sp.Rational(a_value.numerator, a_value.denominator) + x
    residual = sp.expand(
        t * (t**2 - 11 * t - 1) * sp.diff(series, x, 2)
        + (3 * t**2 - 22 * t - 1) * sp.diff(series, x)
        + (t - 3) * series
    )

    # A truncated series through b_11 can only force coefficients through x^9.
    checked_coefficients = [sp.simplify(residual.coeff(x, i)) for i in range(term_count - 2)]
    matches = [coeff == 0 for coeff in checked_coefficients]
    denominators = sorted({abs(term.denominator) for term in terms})

    return {
        "specialization": {"a": str(a_value), "b0": str(b0_value), "b1": str(b1_value)},
        "terms_b0_through_b11": [str(term) for term in terms],
        "distinct_denominators": [str(denom) for denom in denominators],
        "checked_residual_coefficients_x0_through_x9": [str(coeff) for coeff in checked_coefficients],
        "match": all(matches),
        "note": (
            "Finite sanity check only; this does not prove the paper's infinite-prime "
            "denominator conclusion."
        ),
    }


def build_output(verifications: List[Dict[str, Any]], verdict: str) -> Dict[str, Any]:
    return {
        "paper": PAPER,
        "stage": 1,
        "explicit_claim": EXPLICIT_CLAIM,
        "claim_locator": CLAIM_LOCATOR,
        "verifications": verifications,
        "verdict": verdict,
    }


def main() -> int:
    signal.signal(signal.SIGALRM, _alarm_handler)
    signal.alarm(TIME_BUDGET_SECONDS)
    output_path = os.path.abspath(os.path.join(os.path.dirname(__file__), OUTPUT_NAME))

    try:
        progress("Lam-Litt arXiv:2501.13175 Stage-1 checker starting", force=True)
        symbolic = derive_recurrence_symbolically()
        check_time_budget("symbolic recurrence derivation")
        concrete = finite_series_residual_check()
        check_time_budget("finite residual check")

        verifications: List[Dict[str, Any]] = [
            {
                "name": "derive_equation_4_2_from_picard_fuchs_ode",
                "expected": symbolic["expected"],
                "computed": symbolic["computed"],
                "match": symbolic["match"],
                "details": {
                    "difference": symbolic["difference"],
                    "shifted_ode_coefficients": {
                        "t(t^2-11t-1)": symbolic["p2_shifted"],
                        "3t^2-22t-1": symbolic["p1_shifted"],
                        "t-3": symbolic["p0_shifted"],
                    },
                },
            },
            {
                "name": "finite_specialization_residual_a_2_b0_1_b1_0",
                "expected": "residual coefficients x^0 through x^9 vanish",
                "computed": concrete["checked_residual_coefficients_x0_through_x9"],
                "match": concrete["match"],
                "details": concrete,
            },
        ]

        verdict = (
            "PASS_PROP_4_0_1_RECURRENCE"
            if all(bool(item["match"]) for item in verifications)
            else "FAIL_PROP_4_0_1_RECURRENCE"
        )
        output = build_output(verifications, verdict)
    except VerificationAbort as exc:
        verdict = "PARTIAL_TIME_BUDGET"
        output = build_output(
            [
                {
                    "name": "runtime_budget",
                    "expected": "complete within 20 minutes",
                    "computed": str(exc),
                    "match": False,
                }
            ],
            verdict,
        )
    finally:
        signal.alarm(0)

    progress("STEP 3: writing JSON output", force=True)
    with open(output_path, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2, sort_keys=True)
        handle.write("\n")

    print(f"JSON output: {output_path}", flush=True)
    print(f"VERDICT: {output['verdict']}", flush=True)
    return 0 if output["verdict"].startswith("PASS_") else 1


if __name__ == "__main__":
    raise SystemExit(main())
