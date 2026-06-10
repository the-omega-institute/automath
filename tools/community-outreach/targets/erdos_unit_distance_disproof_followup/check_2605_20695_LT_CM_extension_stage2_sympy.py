#!/usr/bin/env python3
"""Stage-2 SymPy check for the CM extensions attached to arXiv:2605.20695.

This is a finite, constructive sanity check.  It does not verify the
asymptotic unit-distance result in the paper.  It checks the multiquadratic
degree data for

    L_T = Q(sqrt(5), sqrt(13), sqrt(17), sqrt(21), sqrt(33))

and for the CM extensions K_d = L_T(sqrt(-d)), then builds a small exact set
of norm-one points in K_3 under the embedding sqrt(-3) -> +i sqrt(3).
"""

from __future__ import annotations

import datetime as _datetime
import json
import math
import os
import signal
import time
from typing import Dict, List, Sequence, Tuple

import mpmath as mp
import sympy as sp
from sympy.polys.numberfields import minimal_polynomial


PAPER = "arXiv:2605.20695"
STAGE = "stage2_CM_extension_sympy"
GENERATORS = [5, 13, 17, 21, 33]
CM_D_VALUES = [3, 5, 7, 11, 13, 17]
CANONICAL_D = 3
VECTOR_PRIMES = [-1, 3, 5, 7, 11, 13, 17]
TIME_BUDGET_SECONDS = 22 * 60
PROGRESS_INTERVAL_SECONDS = 20
OUTPUT_NAME = "check_2605_20695_LT_CM_extension_stage2_sympy_output.json"


class Stage2Abort(RuntimeError):
    """Raised when the script cannot finish within the declared time budget."""


_START_MONOTONIC = time.monotonic()
_LAST_PROGRESS = 0.0


def utc_now_iso() -> str:
    return _datetime.datetime.now(_datetime.timezone.utc).isoformat().replace("+00:00", "Z")


def elapsed_seconds() -> float:
    return time.monotonic() - _START_MONOTONIC


def progress(message: str, force: bool = False) -> None:
    """Print progress with elapsed seconds, throttled to at most 20-second gaps."""
    global _LAST_PROGRESS
    now = time.monotonic()
    if force or _LAST_PROGRESS == 0.0 or now - _LAST_PROGRESS >= PROGRESS_INTERVAL_SECONDS:
        print(f"[t={now - _START_MONOTONIC:.1f}s] {message}", flush=True)
        _LAST_PROGRESS = now


def check_time_budget(context: str) -> None:
    elapsed = elapsed_seconds()
    if elapsed > TIME_BUDGET_SECONDS:
        raise Stage2Abort(
            f"time budget exceeded during {context}: "
            f"elapsed_seconds={elapsed:.3f}, budget_seconds={TIME_BUDGET_SECONDS}"
        )


def _alarm_handler(signum, frame) -> None:  # type: ignore[no-untyped-def]
    raise Stage2Abort("global 22-minute alarm fired before Stage-2 completed")


def prime_factorization(n: int) -> Dict[int, int]:
    if n == 0:
        raise ValueError("0 has no square class in Q*/(Q*)^2")

    factors: Dict[int, int] = {}
    if n < 0:
        factors[-1] = 1

    n_abs = abs(n)
    divisor = 2
    while divisor * divisor <= n_abs:
        while n_abs % divisor == 0:
            factors[divisor] = factors.get(divisor, 0) + 1
            n_abs //= divisor
        divisor += 1 if divisor == 2 else 2

    if n_abs > 1:
        factors[n_abs] = factors.get(n_abs, 0) + 1

    return factors


def squareclass_vector(n: int, primes: Sequence[int]) -> List[int]:
    factors = prime_factorization(n)
    return [factors.get(prime, 0) % 2 for prime in primes]


def f2_rank_and_basis(rows: Sequence[Sequence[int]]) -> Tuple[int, List[List[int]], List[int]]:
    matrix = [list(row) for row in rows]
    if not matrix:
        return 0, [], []

    row_count = len(matrix)
    col_count = len(matrix[0])
    pivot_row = 0
    pivots: List[int] = []

    for col in range(col_count):
        pivot = None
        for row in range(pivot_row, row_count):
            if matrix[row][col] % 2:
                pivot = row
                break
        if pivot is None:
            continue

        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        for row in range(row_count):
            if row != pivot_row and matrix[row][col] % 2:
                matrix[row] = [(a ^ b) for a, b in zip(matrix[row], matrix[pivot_row])]
        pivots.append(col)
        pivot_row += 1
        if pivot_row == row_count:
            break

    return pivot_row, [matrix[row] for row in range(pivot_row)], pivots


def multiquadratic_degree(squareclasses: Sequence[int]) -> Tuple[int, Dict[str, object]]:
    vectors = [squareclass_vector(n, VECTOR_PRIMES) for n in squareclasses]
    rank, basis, pivots = f2_rank_and_basis(vectors)
    records = [
        {
            "generator": n,
            "prime_order": VECTOR_PRIMES,
            "vector_mod_2": vector,
        }
        for n, vector in zip(squareclasses, vectors)
    ]
    return 2**rank, {
        "rank_over_F2": rank,
        "degree": 2**rank,
        "generator_vectors": records,
        "basis": basis,
        "pivot_columns": pivots,
    }


def construct_lt_with_sympy() -> Dict[str, object]:
    progress("step 1: constructing L_T generators in SymPy and certifying degree", force=True)
    check_time_budget("L_T construction")

    sqrt_generators = [sp.sqrt(n) for n in GENERATORS]
    primitive_expression = sum(sqrt_generators)
    lt_field = sp.QQ.algebraic_field(*sqrt_generators)
    degree, certificate = multiquadratic_degree(GENERATORS)

    # Direct minimal_polynomial on the full primitive element is expensive in
    # SymPy 1.14 on this field.  SymPy can nevertheless construct the
    # AlgebraicField representation quickly; its defining modulus has degree
    # 32, agreeing with the exact square-class rank computation.
    x = sp.Symbol("x")
    prefix_checks = []
    for length in range(1, 4):
        prefix_expr = sum(sqrt_generators[:length])
        minpoly = minimal_polynomial(prefix_expr, x)
        prefix_checks.append(
            {
                "prefix_generators": GENERATORS[:length],
                "primitive": str(prefix_expr),
                "minimal_polynomial_degree": int(sp.degree(minpoly, x)),
                "minimal_polynomial": str(minpoly),
            }
        )

    progress(f"step 1 complete: [L_T:Q]={degree}", force=True)
    return {
        "sympy_generators": [str(expr) for expr in sqrt_generators],
        "sympy_primitive_expression": str(primitive_expression),
        "sympy_algebraic_field": str(lt_field),
        "sympy_algebraic_field_modulus_degree": int(lt_field.mod.degree()),
        "sympy_algebraic_field_modulus": str(lt_field.mod),
        "degree": degree,
        "degree_certificate": certificate,
        "sympy_prefix_minpoly_checks": prefix_checks,
    }


def compute_cm_degrees() -> Tuple[Dict[str, int], Dict[str, object]]:
    progress("step 2: certifying CM extension degrees [K_d:Q]", force=True)
    check_time_budget("CM degree computation")

    degrees: Dict[str, int] = {}
    details: Dict[str, object] = {}
    for d in CM_D_VALUES:
        degree, certificate = multiquadratic_degree([*GENERATORS, -d])
        degrees[f"d={d}"] = degree
        details[f"d={d}"] = {
            "degree": degree,
            "degree_certificate": certificate,
            "sympy_generator": str(sp.sqrt(-d)),
            "intersection_reason": (
                "L_T is generated by positive square roots, hence is totally real. "
                f"Q(sqrt(-{d})) is imaginary quadratic for d>0.  Any subfield of a "
                "totally real field is totally real, so the intersection is Q."
            ),
        }

    progress(f"step 2 complete: CM degrees={degrees}", force=True)
    return degrees, details


def sixth_roots_of_unity(tau: sp.Expr) -> List[sp.Expr]:
    zeta6 = (1 + tau) / 2
    return [sp.simplify(zeta6**j) for j in range(6)]


def norm_one_cm_points(tau: sp.Expr, max_points: int = 36) -> List[sp.Expr]:
    """Return exact norm-one elements (a+b*tau)/(a-b*tau) in Q(sqrt(-3)).

    These points lie in Q(sqrt(-3)) subset K_3.  They are more varied than the
    sixth roots of unity, but they still do not use genuinely L_T-dependent
    algebraic integers; the JSON notes this boundary explicitly.
    """
    points: List[sp.Expr] = []
    for a in range(1, 8):
        for b in range(1, 8):
            if math.gcd(a, b) != 1:
                continue
            alpha = sp.simplify((sp.Integer(a) + sp.Integer(b) * tau) / (sp.Integer(a) - sp.Integer(b) * tau))
            points.append(alpha)
            if len(points) >= max_points:
                return points
    return points


def canonical_key(expr: sp.Expr) -> str:
    return sp.srepr(sp.together(sp.simplify(expr)))


def build_unit_circle_set() -> List[sp.Expr]:
    progress("step 3: constructing exact unit-circle set S in K_3", force=True)
    check_time_budget("unit-circle construction")

    tau = sp.sqrt(-3)
    candidates = [*sixth_roots_of_unity(tau), *norm_one_cm_points(tau)]
    seen = set()
    points: List[sp.Expr] = []
    for candidate in candidates:
        simplified = sp.simplify(candidate)
        key = canonical_key(simplified)
        if key in seen:
            continue
        seen.add(key)
        points.append(simplified)
        if len(points) >= 100:
            break

    progress(f"step 3 complete: S_size={len(points)}", force=True)
    return points


def numeric_point_record(alpha: sp.Expr) -> Dict[str, str]:
    check_time_budget("numeric point evaluation")

    alpha_eval = sp.N(alpha, 80)
    re_part = sp.N(sp.re(alpha_eval), 50)
    im_part = sp.N(sp.im(alpha_eval), 50)
    abs_part = sp.N(sp.sqrt(sp.re(alpha_eval) ** 2 + sp.im(alpha_eval) ** 2), 50)

    # mpmath conversion is used to exercise the requested high-precision
    # numeric float path before JSON string serialization.
    mp.mp.dps = 50
    re_mpf = mp.mpf(str(re_part))
    im_mpf = mp.mpf(str(im_part))
    abs_mpf = mp.sqrt(re_mpf * re_mpf + im_mpf * im_mpf)

    return {
        "alpha_symbolic": str(alpha),
        "re": mp.nstr(re_mpf, 45),
        "im": mp.nstr(im_mpf, 45),
        "abs": mp.nstr(abs_mpf, 45),
    }


def point_coordinates(alpha: sp.Expr) -> Tuple[sp.Expr, sp.Expr]:
    expanded = sp.expand_complex(alpha)
    return sp.simplify(sp.re(expanded)), sp.simplify(sp.im(expanded))


def is_unit_distance(coords_i: Tuple[sp.Expr, sp.Expr], coords_j: Tuple[sp.Expr, sp.Expr]) -> Tuple[bool, str]:
    re_i, im_i = coords_i
    re_j, im_j = coords_j
    dist2 = sp.simplify((re_i - re_j) ** 2 + (im_i - im_j) ** 2)
    exact_delta = sp.simplify(dist2 - 1)
    if exact_delta == 0:
        return True, "exact"

    numeric_delta = abs(sp.N(sp.sqrt(dist2), 80) - 1)
    if numeric_delta < sp.Float("1e-30"):
        return True, "numeric_1e-30"
    return False, "not_unit"


def count_unit_distance_pairs(points: Sequence[sp.Expr]) -> Tuple[int, List[Dict[str, object]], Dict[str, int]]:
    progress("step 4: counting exact/high-precision unit-distance pairs", force=True)
    check_time_budget("unit-distance counting")

    coords = [point_coordinates(alpha) for alpha in points]
    count = 0
    method_counts = {"exact": 0, "numeric_1e-30": 0}
    pairs: List[Dict[str, object]] = []

    for i in range(len(points)):
        for j in range(i + 1, len(points)):
            is_unit, method = is_unit_distance(coords[i], coords[j])
            if not is_unit:
                continue
            count += 1
            method_counts[method] += 1
            pairs.append(
                {
                    "i": i,
                    "j": j,
                    "method": method,
                    "alpha_i": str(points[i]),
                    "alpha_j": str(points[j]),
                }
            )

    progress(f"step 4 complete: unit_distance_pairs={count}", force=True)
    return count, pairs, method_counts


def write_json(output: Dict[str, object]) -> str:
    output_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), OUTPUT_NAME)
    progress(f"step 5: writing JSON output to {output_path}", force=True)
    with open(output_path, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return output_path


def build_output(status: str = "PASS", honest_notes_extra: str | None = None) -> Dict[str, object]:
    lt_result = construct_lt_with_sympy()
    cm_degrees, cm_details = compute_cm_degrees()
    points = build_unit_circle_set()
    point_records = [numeric_point_record(alpha) for alpha in points]
    unit_pairs, pair_details, method_counts = count_unit_distance_pairs(points)

    n = len(points)
    pass_conditions = (
        lt_result["degree"] == 32
        and all(cm_degrees.get(f"d={d}") == 64 for d in CM_D_VALUES)
        and n >= 6
        and unit_pairs >= 1
    )
    final_status = status if status != "PASS" else ("PASS" if pass_conditions else "HONEST_PARTIAL")

    honest_notes = (
        "S is an exact finite subset of K_3 on the canonical unit circle.  It contains "
        "the six sixth roots of unity and additional rationally parametrized norm-one "
        "elements (a+b*sqrt(-3))/(a-b*sqrt(-3)) in the CM subfield Q(sqrt(-3)).  "
        "This is deliberately a first finite slice: it does not construct "
        "L_T-dependent ring-of-integers norm-one elements, and n is far too small "
        "to test the asymptotic exponent in the paper."
    )
    if honest_notes_extra:
        honest_notes = f"{honest_notes} {honest_notes_extra}"

    return {
        "paper": PAPER,
        "paper_citation": (
            "Alon, Bloom, Gowers, Litt, Sawin, Shankar, Tsimerman, Wang, Wood. "
            "Remarks on the disproof of the unit distance conjecture. arXiv:2605.20695, May 2026."
        ),
        "stage": STAGE,
        "status": final_status,
        "timestamp_utc": utc_now_iso(),
        "sympy_version": sp.__version__,
        "L_T_generators": GENERATORS,
        "L_T_degree": lt_result["degree"],
        "L_T_construction": lt_result,
        "CM_extensions": cm_degrees,
        "CM_extension_details": cm_details,
        "canonical_d": CANONICAL_D,
        "canonical_embedding": {
            "sqrt(-3)": "+i*sqrt(3)",
            "sqrt(k) for k in {5,13,17,21,33}": "+sqrt(k)",
        },
        "S_size": n,
        "S_construction": (
            "sixth roots of unity plus exact norm-one elements "
            "(a+b*sqrt(-3))/(a-b*sqrt(-3)) for small coprime positive integers a,b"
        ),
        "S_points": point_records,
        "unit_distance_pairs": unit_pairs,
        "unit_distance_pair_details": pair_details,
        "unit_distance_pair_methods": method_counts,
        "pair_ratio": unit_pairs / n if n else None,
        "asymptotic_comparison": {
            "n": n,
            "erdos_classical_bound_exponent_extra": (
                "c/log log n with c approximately constant; n is not in the asymptotic regime"
            ),
            "disproof_claim_extra_eps": 6.24e-38,
            "note": (
                "n too small to distinguish; this is a constructive sanity check, "
                "not an asymptotic verification"
            ),
        },
        "honest_notes": honest_notes,
        "runtime_seconds": round(elapsed_seconds(), 6),
        "verdict": final_status,
    }


def insufficient_output(reason: str) -> Dict[str, object]:
    return {
        "paper": PAPER,
        "stage": STAGE,
        "status": "INSUFFICIENT_INFRASTRUCTURE",
        "timestamp_utc": utc_now_iso(),
        "sympy_version": sp.__version__,
        "L_T_degree": None,
        "CM_extensions": {},
        "canonical_d": CANONICAL_D,
        "S_size": 0,
        "S_points": [],
        "unit_distance_pairs": 0,
        "pair_ratio": None,
        "asymptotic_comparison": {
            "n": 0,
            "erdos_classical_bound_exponent_extra": (
                "c/log log n with c approximately constant; no finite set was completed"
            ),
            "disproof_claim_extra_eps": 6.24e-38,
            "note": "Stage-2 did not complete, so no asymptotic verification is claimed.",
        },
        "honest_notes": reason,
        "runtime_seconds": round(elapsed_seconds(), 6),
        "verdict": "INSUFFICIENT_INFRASTRUCTURE",
    }


def main() -> int:
    signal.signal(signal.SIGALRM, _alarm_handler)
    signal.alarm(TIME_BUDGET_SECONDS)

    output_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), OUTPUT_NAME)
    verdict = "INSUFFICIENT_INFRASTRUCTURE"
    try:
        progress("starting Stage-2 CM extension SymPy check", force=True)
        output = build_output()
        verdict = str(output["verdict"])
        output_path = write_json(output)
        progress(f"complete: verdict={verdict}", force=True)
    except Stage2Abort as exc:
        output = insufficient_output(str(exc))
        output_path = write_json(output)
        verdict = "INSUFFICIENT_INFRASTRUCTURE"
    except Exception as exc:  # Keep the honesty contract: write JSON even on failure.
        output = insufficient_output(f"unexpected exception: {type(exc).__name__}: {exc}")
        output_path = write_json(output)
        verdict = "INSUFFICIENT_INFRASTRUCTURE"
    finally:
        signal.alarm(0)

    print(f"VERDICT: {verdict}")
    print(f"JSON: {output_path}")
    print('COMMIT: not committed')
    return 0 if verdict in {"PASS", "HONEST_PARTIAL"} else 2


if __name__ == "__main__":
    raise SystemExit(main())
