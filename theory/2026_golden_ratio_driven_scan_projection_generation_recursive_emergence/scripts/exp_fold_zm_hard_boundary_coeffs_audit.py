#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit hard-boundary coefficient closed forms for the Fold fiber-weight partition Z_m(y).

This script is English-only by repository convention.

We use the (m,k) coefficient table a_{m,k} = [y^k] Z_m(y), defined by
  Z_m(y) = sum_{x in X_m} y^{|x|_1} d_m(x) = sum_k a_{m,k} y^k,
where d_m(x) = |Fold_m^{-1}(x)|.

We generate a_{m,k} for moderately large m using the local 2D recurrence stated in the paper:
  a_{m,k} = a_{m-1,k} + a_{m-2,k} + 2 a_{m-2,k-1}
            - a_{m-3,k} - a_{m-4,k-1} - a_{m-4,k-2},   (m>=4)
with boundary conditions a_{m,k}=0 for k<0 or k>ceil(m/2).

From this table we extract hard-boundary layers:
  A_j(k) = [y^{k-j}] Z_{2k}(y)   (even length)
  B_j(k) = [y^{k+1-j}] Z_{2k+1}(y) (odd length)

Checks performed:
  - The 2D recurrence matches exact Fold enumeration for m<=m_enum_max.
  - For each fixed j<=j_max, A_j(k) is an exact polynomial in k of degree 4j+2,
    and B_j(k) is an exact polynomial of degree 4j (forward differences).
  - The binomial-basis (Newton series) coefficients match the closed forms for
    A_1,A_2,A_3 and B_1,B_2.
  - The ordinary generating function of A_1 equals the stated pure-pole rational function.

Outputs (default):
  - artifacts/export/fold_zm_hard_boundary_coeffs_audit.json
  - sections/generated/eq_fold_zm_hard_boundary_coeffs_audit.tex
"""

from __future__ import annotations

import argparse
import json
import time
from itertools import product
from math import comb
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import fold_m


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _kmax(m: int) -> int:
    # max number of 1s in a golden-mean word of length m
    return (m + 1) // 2  # ceil(m/2)


def _binom(n: int, r: int) -> int:
    if r < 0 or n < 0 or r > n:
        return 0
    return comb(n, r)


def enumerate_a_mk(m: int) -> List[int]:
    # a_{m,k} = # {a in Omega_m : |Fold_m(a)|_1 = k}
    counts = [0] * (m + 1)
    for bits in product([0, 1], repeat=m):
        x = fold_m(bits)
        counts[sum(x)] += 1
    return counts


def build_a_table(m_max: int) -> List[List[int]]:
    """Build a[m][k] for 0<=m<=m_max and 0<=k<=ceil(m/2) using the 2D recurrence."""
    if m_max < 0:
        raise ValueError("m_max must be non-negative")

    a: List[List[int]] = [[0] * (_kmax(m) + 1) for m in range(m_max + 1)]

    # Base cases from exact enumeration (m=0..min(3,m_max)).
    for m in range(0, min(3, m_max) + 1):
        counts = enumerate_a_mk(m)
        for k in range(_kmax(m) + 1):
            a[m][k] = counts[k]

    def get(mm: int, kk: int) -> int:
        if mm < 0 or kk < 0 or mm > m_max:
            return 0
        row = a[mm]
        if kk >= len(row):
            return 0
        return row[kk]

    for m in range(4, m_max + 1):
        for k in range(0, _kmax(m) + 1):
            a[m][k] = (
                get(m - 1, k)
                + get(m - 2, k)
                + 2 * get(m - 2, k - 1)
                - get(m - 3, k)
                - get(m - 4, k - 1)
                - get(m - 4, k - 2)
            )
            if a[m][k] < 0:
                raise AssertionError(f"negative a[{m},{k}]={a[m][k]} (should never happen)")

    return a


def forward_differences(values: List[int]) -> List[List[int]]:
    diffs: List[List[int]] = [values[:]]
    while len(diffs[-1]) >= 2:
        prev = diffs[-1]
        diffs.append([prev[i + 1] - prev[i] for i in range(len(prev) - 1)])
    return diffs


def _seq_A(a: List[List[int]], j: int, k_max: int) -> List[int]:
    out: List[int] = []
    for k in range(k_max + 1):
        if k < j:
            out.append(0)
            continue
        m = 2 * k
        idx = k - j
        out.append(a[m][idx])
    return out


def _seq_B(a: List[List[int]], j: int, k_max: int) -> List[int]:
    out: List[int] = []
    for k in range(k_max + 1):
        if k < j - 1:
            out.append(0)
            continue
        m = 2 * k + 1
        idx = k + 1 - j
        out.append(a[m][idx])
    return out


def _check_polynomial_by_differences(values: List[int], degree: int) -> Tuple[bool, List[int]]:
    """Return (ok, c_r) where c_r = Delta^r f(0) for r=0..degree (Newton/binomial basis)."""
    if degree < 0:
        raise ValueError("degree must be non-negative")
    diffs = forward_differences(values)
    # Need at least degree+2 points to check (degree+1)-th differences on at least one entry.
    if len(values) < degree + 2:
        return False, []
    # (degree+1)-th differences must be identically zero if polynomial degree <= degree.
    level = degree + 1
    ok = True
    if level < len(diffs):
        if any(x != 0 for x in diffs[level]):
            ok = False
    else:
        ok = False
    c = [diffs[r][0] for r in range(min(degree, len(diffs) - 1) + 1)]
    return ok, c


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Z_m(y) hard-boundary coefficient closed forms")
    parser.add_argument("--k-max", type=int, default=80, help="Max k for A_j(k), B_j(k) checks (default: 80)")
    parser.add_argument("--m-enum-max", type=int, default=12, help="Max m for exact enumeration cross-check (default: 12)")
    parser.add_argument("--j-max", type=int, default=6, help="Max layer depth j to check polynomiality (default: 6)")
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-hard-boundary] start", flush=True)

    if args.k_max < 0:
        raise SystemExit("--k-max must be non-negative")
    if args.m_enum_max < 0:
        raise SystemExit("--m-enum-max must be non-negative")
    if args.j_max < 0:
        raise SystemExit("--j-max must be non-negative")

    m_max = 2 * args.k_max + 1
    a = build_a_table(m_max)

    # --- Cross-check recurrence table against exact enumeration for small m ---
    enum_ok = True
    enum_fail_head: List[Dict[str, object]] = []
    for m in range(0, min(args.m_enum_max, m_max) + 1):
        counts = enumerate_a_mk(m)
        for k in range(0, _kmax(m) + 1):
            if a[m][k] != counts[k]:
                enum_ok = False
                enum_fail_head.append({"m": m, "k": k, "a_rec": a[m][k], "a_enum": counts[k]})
                break
        if not enum_ok:
            break

    # --- Polynomiality checks via forward differences (Newton series) ---
    A_checks: Dict[str, object] = {}
    B_checks: Dict[str, object] = {}
    poly_ok = True

    for j in range(0, args.j_max + 1):
        # Even
        degA = 4 * j + 2
        seqA = _seq_A(a, j=j, k_max=args.k_max)
        okA, cA = _check_polynomial_by_differences(seqA, degree=degA)
        # Exact degree and normalization
        degA_ok = okA and len(cA) == degA + 1 and cA[degA] == 1
        # Lower-triangular sparsity: A_j(k)=0 for k<j implies c_r=0 for r<j.
        lowerA_ok = True
        for r in range(0, min(j, len(cA))):
            if cA[r] != 0:
                lowerA_ok = False
                break
        A_checks[str(j)] = {
            "degree": degA,
            "diff_degree_plus_one_all_zero": bool(okA),
            "leading_binom_coeff_is_1": (len(cA) == degA + 1 and cA[degA] == 1),
            "lower_binom_coeffs_vanish_up_to_r=j-1": bool(lowerA_ok),
            "binom_coeffs_c_r": cA,
            "values_A_j_k_head": seqA[: min(len(seqA), 20)],
        }
        poly_ok = poly_ok and bool(degA_ok) and bool(lowerA_ok)

        # Odd
        degB = 4 * j
        seqB = _seq_B(a, j=j, k_max=args.k_max)
        okB, cB = _check_polynomial_by_differences(seqB, degree=degB)
        degB_ok = okB and len(cB) == degB + 1 and cB[degB] == 1
        lowerB_ok = True
        # B_j(k)=0 for k<j-1 implies c_r=0 for r<j-1.
        for r in range(0, min(max(j - 1, 0), len(cB))):
            if cB[r] != 0:
                lowerB_ok = False
                break
        B_checks[str(j)] = {
            "degree": degB,
            "diff_degree_plus_one_all_zero": bool(okB),
            "leading_binom_coeff_is_1": (len(cB) == degB + 1 and cB[degB] == 1),
            "lower_binom_coeffs_vanish_up_to_r=j-2": bool(lowerB_ok),
            "binom_coeffs_d_r": cB,
            "values_B_j_k_head": seqB[: min(len(seqB), 20)],
        }
        poly_ok = poly_ok and bool(degB_ok) and bool(lowerB_ok)

    # --- Closed-form coefficient checks for j=1..3 (A) and j=1..2 (B) ---
    def _expect_dict_A() -> Dict[int, List[int]]:
        return {
            1: [0, 2, 5, 9, 7, 4, 1],
            2: [0, 0, 3, 14, 39, 59, 63, 45, 22, 7, 1],
            3: [0, 0, 0, 4, 30, 119, 273, 439, 507, 437, 283, 135, 46, 10, 1],
        }

    def _expect_dict_B() -> Dict[int, List[int]]:
        return {
            1: [1, 4, 4, 3, 1],
            2: [0, 2, 11, 23, 32, 28, 16, 6, 1],
        }

    closed_ok = True
    closed_fail: List[Dict[str, object]] = []

    expA = _expect_dict_A()
    for j, c_exp in expA.items():
        deg = 4 * j + 2
        seq = _seq_A(a, j=j, k_max=args.k_max)
        ok, c = _check_polynomial_by_differences(seq, degree=deg)
        if (not ok) or (c[: len(c_exp)] != c_exp):
            closed_ok = False
            closed_fail.append({"family": "A", "j": j, "expected": c_exp, "got": c[: len(c_exp)], "deg": deg})

    expB = _expect_dict_B()
    for j, c_exp in expB.items():
        deg = 4 * j
        seq = _seq_B(a, j=j, k_max=args.k_max)
        ok, c = _check_polynomial_by_differences(seq, degree=deg)
        if (not ok) or (c[: len(c_exp)] != c_exp):
            closed_ok = False
            closed_fail.append({"family": "B", "j": j, "expected": c_exp, "got": c[: len(c_exp)], "deg": deg})

    # --- Polynomial-form checks for A_1 and B_1 ---
    def A1_poly(k: int) -> int:
        num = k**6 + 9 * k**5 + 55 * k**4 + 435 * k**3 - 56 * k**2 + 996 * k
        if num % 720 != 0:
            raise AssertionError(f"A1 numerator not divisible by 720 at k={k}")
        return num // 720

    def B1_poly(k: int) -> int:
        num = k**4 + 6 * k**3 + 23 * k**2 + 66 * k + 24
        if num % 24 != 0:
            raise AssertionError(f"B1 numerator not divisible by 24 at k={k}")
        return num // 24

    poly_form_ok = True
    for k in range(0, args.k_max + 1):
        if _seq_A(a, j=1, k_max=args.k_max)[k] != A1_poly(k):
            poly_form_ok = False
            break
        if _seq_B(a, j=1, k_max=args.k_max)[k] != B1_poly(k):
            poly_form_ok = False
            break

    # --- Generating function check for A_1 ---
    # A_1(t) = (2t - 5t^2 + 9t^3 - 10t^4 + 7t^5 - 2t^6) / (1-t)^7.
    gen_ok = True
    num = {1: 2, 2: -5, 3: 9, 4: -10, 5: 7, 6: -2}
    for k in range(0, args.k_max + 1):
        pred = 0
        for i, ci in num.items():
            if k >= i:
                # coeff of t^(k-i) in (1-t)^(-7) is C((k-i)+6,6)
                pred += ci * _binom((k - i) + 6, 6)
        if pred != _seq_A(a, j=1, k_max=args.k_max)[k]:
            gen_ok = False
            break

    checks = {
        "recurrence_table_matches_exact_enumeration_up_to_m_enum_max": enum_ok,
        "poly_degree_and_normalization_ok_for_all_j_up_to_j_max": bool(poly_ok),
        "closed_form_binom_coeffs_ok": bool(closed_ok),
        "closed_form_fail_head": closed_fail[:5],
        "A1_and_B1_polynomial_forms_ok": bool(poly_form_ok),
        "A1_generating_function_ok": bool(gen_ok),
    }

    payload: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "generated_at_unix_s": float(time.time()),
            "seconds": float(time.time() - t0),
        },
        "params": {
            "k_max": int(args.k_max),
            "m_max": int(m_max),
            "m_enum_max": int(args.m_enum_max),
            "j_max": int(args.j_max),
        },
        "checks": checks,
        "fail_head": {"enum": enum_fail_head[:5]},
        "derived": {
            "A_layers": A_checks,
            "B_layers": B_checks,
        },
    }

    if not args.no_output:
        out_json = export_dir() / "fold_zm_hard_boundary_coeffs_audit.json"
        _write_json(out_json, payload)

        out_tex = generated_dir() / "eq_fold_zm_hard_boundary_coeffs_audit.tex"
        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_fold_zm_hard_boundary_coeffs_audit.py",
                "% Minimal audit artifact (not necessarily included in the paper).",
                "\\[",
                "\\mathcal A_1(t)=\\frac{2t-5t^2+9t^3-10t^4+7t^5-2t^6}{(1-t)^7}.",
                "\\]",
                "",
            ]
        )
        _write_text(out_tex, tex)

        print(f"[fold-zm-hard-boundary] wrote {out_json}", flush=True)
        print(f"[fold-zm-hard-boundary] wrote {out_tex}", flush=True)

    print(
        "[fold-zm-hard-boundary] checks:"
        f" enum_ok={enum_ok} poly_ok={poly_ok} closed_ok={closed_ok} poly_form_ok={poly_form_ok} gen_ok={gen_ok}",
        flush=True,
    )
    print("[fold-zm-hard-boundary] done", flush=True)


if __name__ == "__main__":
    main()

