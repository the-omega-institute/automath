#!/usr/bin/env python3
"""Stage-3 finite check for genuinely L_T-dependent unit-circle elements.

This script builds

    beta_{a,b,k} = (a + b*i*sqrt(k)) / (a - b*i*sqrt(k))

for k in {5, 13, 17, 21, 33}.  These elements lie in
F = L_T(i) = Q(sqrt(5), sqrt(13), sqrt(17), sqrt(21), sqrt(33), i), and
under the principal embedding i -> +i, sqrt(k) -> +sqrt(k), they have
complex absolute value 1.

The check is intentionally finite and conservative: it deduplicates by exact
SymPy simplification, uses high-precision floating point only as a prefilter
for unit-distance candidates, and then asks SymPy to confirm |beta1-beta2|^2=1
symbolically.
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import mpmath as mp
import sympy as sp


TARGET_DIR = Path(__file__).resolve().parent
OUTPUT_PATH = TARGET_DIR / "check_2605_20695_LT_genuine_layer_stage3_output.json"

T_VALUES = (5, 13, 17, 21, 33)
M_CANDIDATES = (8, 10, 12)
MIN_N = 50
NUMERIC_PRECISION = 60
MPMATH_DPS = 80
NUMERIC_PREFILTER_TOL = sp.Float("1e-30", NUMERIC_PRECISION)
NUMERIC_FALLBACK_TOL = sp.Float("1e-50", NUMERIC_PRECISION)
PROGRESS_INTERVAL_SECONDS = 20.0


@dataclass(frozen=True)
class BetaPoint:
    k: int
    a: int
    b: int
    expr: sp.Expr
    z: mp.mpc


class Progress:
    def __init__(self) -> None:
        self.start = time.monotonic()
        self.last = self.start

    def maybe(self, message: str) -> None:
        now = time.monotonic()
        if now - self.last >= PROGRESS_INTERVAL_SECONDS:
            print(f"[t={int(now - self.start)}s] {message}", flush=True)
            self.last = now

    def final(self, message: str) -> None:
        now = time.monotonic()
        print(f"[t={now - self.start:.3f}s] {message}", flush=True)


def beta_expr(a: int, b: int, k: int) -> sp.Expr:
    # Rationalized exact form in Q(i, sqrt(k)).
    denominator = sp.Integer(a * a + b * b * k)
    numerator = sp.Integer(a * a - b * b * k) + sp.Integer(2 * a * b) * sp.I * sp.sqrt(k)
    return sp.cancel(numerator / denominator)


def canonical_key(expr: sp.Expr) -> str:
    return sp.srepr(sp.cancel(sp.together(expr)))


def original_beta_expr(a: int, b: int, k: int) -> sp.Expr:
    root = sp.sqrt(k)
    return sp.cancel((sp.Integer(a) + sp.Integer(b) * sp.I * root) / (sp.Integer(a) - sp.Integer(b) * sp.I * root))


def expr_to_complex(expr: sp.Expr) -> mp.mpc:
    evaluated = sp.N(expr, NUMERIC_PRECISION)
    return mp.mpc(mp.mpf(str(sp.re(evaluated))), mp.mpf(str(sp.im(evaluated))))


def symbolic_equal(lhs: sp.Expr, rhs: sp.Expr) -> bool:
    return sp.simplify(lhs - rhs) == 0


def symbolic_distance_squared(lhs: sp.Expr, rhs: sp.Expr) -> sp.Expr:
    delta = sp.cancel(lhs - rhs)
    return sp.simplify(sp.expand(delta * sp.conjugate(delta)))


def serialise_expr(expr: sp.Expr) -> str:
    return str(sp.sstr(expr))


def build_points(M: int, progress: Progress) -> tuple[list[BetaPoint], dict[str, Any]]:
    total_candidates = sum(
        1
        for _k in T_VALUES
        for a in range(1, M + 1)
        for b in range(1, M + 1 - a)
        if math.gcd(a, b) == 1
    )
    points: list[BetaPoint] = []
    points_by_key: dict[str, BetaPoint] = {}
    duplicate_records: list[dict[str, Any]] = []
    raw_count_by_k = {str(k): 0 for k in T_VALUES}
    built = 0

    for k in T_VALUES:
        for a in range(1, M + 1):
            for b in range(1, M + 1 - a):
                if math.gcd(a, b) != 1:
                    continue
                raw_count_by_k[str(k)] += 1
                expr = beta_expr(a, b, k)
                key = canonical_key(expr)
                keyed_match = points_by_key.get(key)
                duplicate_of = keyed_match if keyed_match is not None and symbolic_equal(expr, keyed_match.expr) else None
                if duplicate_of is None:
                    for existing in points:
                        if existing is keyed_match:
                            continue
                        if symbolic_equal(expr, existing.expr):
                            duplicate_of = existing
                            break

                if duplicate_of is None:
                    point = BetaPoint(k=k, a=a, b=b, expr=expr, z=expr_to_complex(expr))
                    points.append(point)
                    points_by_key[key] = point
                else:
                    duplicate_records.append(
                        {
                            "k": k,
                            "a": a,
                            "b": b,
                            "duplicate_of": {
                                "k": duplicate_of.k,
                                "a": duplicate_of.a,
                                "b": duplicate_of.b,
                            },
                        }
                    )

                built += 1
                progress.maybe(f"built {built}/{total_candidates} beta's")

    duplicate_summary = {
        "raw_candidates": total_candidates,
        "unique_after_symbolic_deduplication": len(points),
        "duplicate_count": len(duplicate_records),
        "deduplication_method": "exact symbolic equality by sympy.simplify(lhs-rhs)==0 against prior S-members; canonical keys are only a fast path",
        "raw_count_by_k": raw_count_by_k,
        "duplicate_examples": duplicate_records[:10],
    }
    return points, duplicate_summary


def count_unit_distance_pairs(points: list[BetaPoint], progress: Progress) -> dict[str, Any]:
    total_pairs = len(points) * (len(points) - 1) // 2
    checked = 0
    numeric_shortlist = 0
    symbolic_confirmed = 0
    numeric_fallback_confirmed = 0
    pair_examples: list[dict[str, Any]] = []
    symbolic_failures: list[dict[str, Any]] = []
    used_numeric_fallback = False

    for i, left in enumerate(points):
        for right in points[i + 1 :]:
            checked += 1
            dz = left.z - right.z
            numeric_d2_mpf = dz.real * dz.real + dz.imag * dz.imag
            numeric_d2 = sp.Float(str(numeric_d2_mpf), NUMERIC_PRECISION)
            if abs(numeric_d2 - 1) <= NUMERIC_PREFILTER_TOL:
                numeric_shortlist += 1
                d2_expr = symbolic_distance_squared(left.expr, right.expr)
                exact_is_one = sp.simplify(d2_expr - 1) == 0

                if exact_is_one:
                    symbolic_confirmed += 1
                    if len(pair_examples) < 10:
                        pair_examples.append(
                            {
                                "k1": left.k,
                                "a1": left.a,
                                "b1": left.b,
                                "k2": right.k,
                                "a2": right.a,
                                "b2": right.b,
                                "distance_squared_symbolic": serialise_expr(d2_expr),
                                "verification": "symbolic",
                            }
                        )
                elif abs(numeric_d2 - 1) <= NUMERIC_FALLBACK_TOL:
                    used_numeric_fallback = True
                    numeric_fallback_confirmed += 1
                    if len(pair_examples) < 10:
                        pair_examples.append(
                            {
                                "k1": left.k,
                                "a1": left.a,
                                "b1": left.b,
                                "k2": right.k,
                                "a2": right.a,
                                "b2": right.b,
                                "distance_squared_symbolic": serialise_expr(d2_expr),
                                "verification": "numerically verified, |d^2-1| < 1e-50",
                            }
                        )
                elif len(symbolic_failures) < 10:
                    symbolic_failures.append(
                        {
                            "k1": left.k,
                            "a1": left.a,
                            "b1": left.b,
                            "k2": right.k,
                            "a2": right.a,
                            "b2": right.b,
                            "numeric_distance_squared": str(numeric_d2),
                            "distance_squared_symbolic": serialise_expr(d2_expr),
                        }
                    )

            progress.maybe(f"checked {checked}/{total_pairs} pairs")

    return {
        "total_pairs_checked": total_pairs,
        "numeric_shortlist": numeric_shortlist,
        "symbolically_confirmed_pairs": symbolic_confirmed,
        "numeric_fallback_confirmed_pairs": numeric_fallback_confirmed,
        "unit_distance_pairs": symbolic_confirmed + numeric_fallback_confirmed,
        "pair_examples": pair_examples,
        "symbolic_failures_after_numeric_prefilter": symbolic_failures,
        "used_numeric_fallback": used_numeric_fallback,
    }


def contribution_counts(points: list[BetaPoint]) -> dict[str, int]:
    counts = {str(k): 0 for k in T_VALUES}
    for point in points:
        counts[str(point.k)] += 1
    return counts


def roots_of_unity_caveat(points: list[BetaPoint]) -> str | None:
    roots = {
        "1": sp.Integer(1),
        "-1": -sp.Integer(1),
        "i": sp.I,
        "-i": -sp.I,
        "zeta6": sp.Rational(1, 2) + sp.I * sp.sqrt(3) / 2,
        "zeta6_conj": sp.Rational(1, 2) - sp.I * sp.sqrt(3) / 2,
        "-zeta6": -sp.Rational(1, 2) - sp.I * sp.sqrt(3) / 2,
        "-zeta6_conj": -sp.Rational(1, 2) + sp.I * sp.sqrt(3) / 2,
    }
    hits: list[dict[str, Any]] = []
    for point in points:
        for name, root in roots.items():
            if symbolic_equal(point.expr, root):
                hits.append({"k": point.k, "a": point.a, "b": point.b, "root": name})
                break
    if hits:
        return f"{len(hits)} generated beta values are small roots of unity: {hits[:10]}"
    return None


def main() -> int:
    progress = Progress()
    attempted_M: list[int] = []
    selected_M: int | None = None
    points: list[BetaPoint] = []
    duplicate_summary: dict[str, Any] = {}

    for M in M_CANDIDATES:
        attempted_M.append(M)
        points, duplicate_summary = build_points(M, progress)
        if len(points) >= MIN_N:
            selected_M = M
            break

    if selected_M is None:
        selected_M = attempted_M[-1]

    progress.final(f"selected M={selected_M}; unique n={len(points)}")
    pair_data = count_unit_distance_pairs(points, progress)
    progress.final(
        "checked "
        f"{pair_data['total_pairs_checked']} pairs; "
        f"unit-distance pairs={pair_data['unit_distance_pairs']}"
    )

    k_contributions = contribution_counts(points)
    layer_exercised = all(k_contributions[str(k)] > 0 for k in T_VALUES)
    nontrivial_pair_exists = pair_data["unit_distance_pairs"] > 0

    honest_caveats: list[str] = [
        "This is a finite search over beta_{a,b,k} with positive coprime a,b and a+b<=M; it is not an exhaustive construction in F.",
        "The generated beta values each lie in a quadratic CM subfield Q(i*sqrt(k)) of F; the Stage-3 layer condition here is exercised by using every requested k from L_T.",
    ]
    if duplicate_summary["duplicate_count"]:
        honest_caveats.append(
            f"{duplicate_summary['duplicate_count']} beta candidates coincided under exact symbolic deduplication."
        )
    else:
        honest_caveats.append("No beta candidates coincided under exact symbolic deduplication.")

    roots_caveat = roots_of_unity_caveat(points)
    if roots_caveat:
        honest_caveats.append(roots_caveat)
    else:
        honest_caveats.append("No generated beta value is one of +/-1, +/-i, or a primitive sixth-root variant checked symbolically.")

    if pair_data["used_numeric_fallback"]:
        honest_caveats.append("At least one recorded pair used the permitted high-precision numeric fallback instead of symbolic confirmation.")
    else:
        honest_caveats.append("All recorded unit-distance pairs, if any, are symbolically confirmed after high-precision numeric prefiltering.")

    if not nontrivial_pair_exists:
        honest_caveats.append(
            "No nontrivial unit-distance pair was found in this finite beta family for the selected M, so the Stage-3 PASS criterion fails."
        )

    verdict = "PASS" if len(points) >= MIN_N and layer_exercised and nontrivial_pair_exists else "FAIL"
    pair_ratio = (
        float(pair_data["unit_distance_pairs"] / pair_data["total_pairs_checked"])
        if pair_data["total_pairs_checked"]
        else 0.0
    )

    output: dict[str, Any] = {
        "paper": "arXiv:2605.20695",
        "stage": "Stage-3 L_T-genuine layer follow-up",
        "field": "F = L_T(i) = Q(sqrt(5), sqrt(13), sqrt(17), sqrt(21), sqrt(33), i)",
        "F_degree_over_Q": 64,
        "CM_over": "L_T",
        "sympy_version": sp.__version__,
        "M_range": attempted_M,
        "M_selected": selected_M,
        "T_values": list(T_VALUES),
        "n": len(points),
        "k_contributions": k_contributions,
        "duplicate_summary": duplicate_summary,
        "unit_distance_pairs": pair_data["unit_distance_pairs"],
        "pair_examples": pair_data["pair_examples"],
        "pair_ratio": pair_ratio,
        "pair_count_details": pair_data,
        "L_T_layer_exercised": layer_exercised,
        "pass_criteria": {
            "n_at_least_50": len(points) >= MIN_N,
            "L_T_layer_exercised": layer_exercised,
            "nontrivial_unit_distance_pair_exists": nontrivial_pair_exists,
        },
        "verdict": verdict,
        "honest_caveats": honest_caveats,
        "runtime_seconds": round(time.monotonic() - progress.start, 6),
    }

    OUTPUT_PATH.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {OUTPUT_PATH}", flush=True)
    print(f"verdict={verdict}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
