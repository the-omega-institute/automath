#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit fixed-k low-weight coefficient quasipolynomials for Z_m(y).

This script is English-only by repository convention.

We work with coefficients a_{m,k} = [y^k] Z_m(y), where Z_m(y) is the Fold
fiber-weight partition polynomial in the paper.

Checks performed:
  - Build a_{m,k} for m up to m_max via the local 2D recurrence (seeded by exact
    enumeration for m<=3).
  - For each fixed k<=k_max, fit polynomials P_k(m) and Q_k(m) such that
        a_{m,k} = P_k(m) + (-1)^m Q_k(m)
    holds on a stable range m >= m0(k) (we use m0(k)=3k+3).
  - Verify deg(P_k)=2k+1, deg(Q_k)=k, and the leading coefficients satisfy
        [m^{2k+1}] P_k(m) = 1/(2^{k+1}(2k+1)!)
        [m^{k}]   Q_k(m) = 1/(2^{2k+2}k!).
  - Verify the paper's closed forms for k<=3 (in parity-polynomial form) agree
    with the table values on a wide test window.
  - Verify the numerator-polynomial golden factor pattern:
        Phi_gold(t) := t^2 - t - 1 divides P_{5n+4}(t),
    via reduction in Z[t]/(Phi_gold) and the 5-step scaling identity
        M^5 = -(55 t + 34) I_2.

Outputs (default):
  - artifacts/export/fold_zm_low_weight_quasipolynomial_audit.json
  - sections/generated/eq_fold_zm_low_weight_quasipolynomial_audit.tex
"""

from __future__ import annotations

import argparse
import json
import time
from itertools import product
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir
from common_phi_fold import fold_m


class _PhiGold:
    """Ring element in Z[t]/(t^2 - t - 1), represented as a + b t."""

    __slots__ = ("a", "b")

    def __init__(self, a: int, b: int) -> None:
        self.a = int(a)
        self.b = int(b)

    def __add__(self, other: "_PhiGold") -> "_PhiGold":
        return _PhiGold(self.a + other.a, self.b + other.b)

    def __neg__(self) -> "_PhiGold":
        return _PhiGold(-self.a, -self.b)

    def __sub__(self, other: "_PhiGold") -> "_PhiGold":
        return _PhiGold(self.a - other.a, self.b - other.b)

    def __mul__(self, other: "_PhiGold") -> "_PhiGold":
        # (a + b t)(c + d t) with t^2 = t + 1.
        a, b = self.a, self.b
        c, d = other.a, other.b
        return _PhiGold(a * c + b * d, a * d + b * c + b * d)

    def __rmul__(self, n: int) -> "_PhiGold":
        return _PhiGold(n * self.a, n * self.b)

    def is_zero(self) -> bool:
        return self.a == 0 and self.b == 0

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, _PhiGold):
            return False
        return self.a == other.a and self.b == other.b

    def to_json(self) -> Dict[str, int]:
        return {"a": int(self.a), "b": int(self.b)}

    def __repr__(self) -> str:
        return f"({self.a}+{self.b}t)"


_PHI_ONE = _PhiGold(1, 0)
_PHI_ZERO = _PhiGold(0, 0)
_PHI_T = _PhiGold(0, 1)


def _phi_pow(x: _PhiGold, n: int) -> _PhiGold:
    r = _PHI_ONE
    b = x
    e = int(n)
    while e:
        if e & 1:
            r = r * b
        b = b * b
        e >>= 1
    return r


def _mat2_mul(A: List[List[_PhiGold]], B: List[List[_PhiGold]]) -> List[List[_PhiGold]]:
    return [
        [A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]],
        [A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]],
    ]


def _mat2_pow(M: List[List[_PhiGold]], n: int) -> List[List[_PhiGold]]:
    I = [[_PHI_ONE, _PHI_ZERO], [_PHI_ZERO, _PHI_ONE]]
    r = I
    b = M
    e = int(n)
    while e:
        if e & 1:
            r = _mat2_mul(r, b)
        b = _mat2_mul(b, b)
        e >>= 1
    return r


def _pk_mod_phi_gold(k_max: int) -> List[_PhiGold]:
    """Compute numerator polynomials P_k(t) reduced mod (t^2 - t - 1), for 0<=k<=k_max."""
    if k_max < 0:
        raise ValueError("k_max must be non-negative")

    # P_0(t)=1.
    P0 = _PHI_ONE

    # P_1(t) = -t (t^4 - t^3 - 1).
    t = _PHI_T
    P1 = -t * (_phi_pow(t, 4) - _phi_pow(t, 3) - _PHI_ONE)

    # P_2(t) = t^3 (t^5 - 2 t^4 - t^3 + t^2 + t + 1).
    P2 = _phi_pow(t, 3) * (
        _phi_pow(t, 5)
        - 2 * _phi_pow(t, 4)
        - _phi_pow(t, 3)
        + _phi_pow(t, 2)
        + t
        + _PHI_ONE
    )

    P: List[_PhiGold] = [_PHI_ZERO] * (k_max + 1)
    P[0] = P0
    if k_max >= 1:
        P[1] = P1
    if k_max >= 2:
        P[2] = P2

    # Reduced recurrence in Z[t]/(t^2 - t - 1):
    #   P_k = -t P_{k-1} - (3 t + 2) P_{k-2},  for k>=3.
    coef1 = -t
    coef2 = -_PhiGold(2, 3)  # -(2 + 3 t)
    for k in range(3, k_max + 1):
        P[k] = coef1 * P[k - 1] + coef2 * P[k - 2]

    return P


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _kmax(m: int) -> int:
    # max number of 1s in a golden-mean legal word of length m
    return (m + 1) // 2  # ceil(m/2)


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


def _poly_to_json(poly: sp.Poly) -> Dict[str, object]:
    n = poly.gens[0]
    coeffs = poly.all_coeffs()  # descending
    return {
        "degree": int(poly.degree(n)),
        # Coefficients are exact rationals; keep them as canonical strings.
        "coeffs_desc": [str(c) for c in coeffs],
    }


def _solve_pq_from_samples(samples: List[Tuple[int, int]], deg_p: int, deg_q: int) -> Tuple[sp.Poly, sp.Poly]:
    """Solve for P(m), Q(m) from samples of a_{m,k} = P(m) + (-1)^m Q(m).

    The unknowns are the monomial coefficients of P (degree deg_p) and Q (degree deg_q).
    """
    m = sp.Symbol("m")
    unknown_count = (deg_p + 1) + (deg_q + 1)
    if len(samples) != unknown_count:
        raise ValueError(f"need exactly {unknown_count} samples, got {len(samples)}")

    rows: List[List[sp.Rational]] = []
    rhs: List[sp.Integer] = []
    for mm, val in samples:
        mm_i = sp.Integer(mm)
        sgn = sp.Integer(-1) if (mm % 2) else sp.Integer(1)
        row = [mm_i**i for i in range(deg_p + 1)]
        row += [sgn * (mm_i**j) for j in range(deg_q + 1)]
        rows.append(row)
        rhs.append(sp.Integer(val))

    A = sp.Matrix(rows)
    b = sp.Matrix(rhs)
    try:
        coeffs = A.LUsolve(b)
    except Exception:
        coeffs, params = A.gauss_jordan_solve(b)
        if params.cols != 0:
            raise AssertionError("underdetermined system while fitting P,Q")

    p_coeffs = list(coeffs[: deg_p + 1, 0])
    q_coeffs = list(coeffs[deg_p + 1 :, 0])

    P_expr = sum(p_coeffs[i] * m**i for i in range(deg_p + 1))
    Q_expr = sum(q_coeffs[j] * m**j for j in range(deg_q + 1))
    P = sp.Poly(sp.expand(P_expr), m, domain=sp.QQ)
    Q = sp.Poly(sp.expand(Q_expr), m, domain=sp.QQ)
    return P, Q


def _closed_form_poly(k: int, parity: str) -> sp.Poly:
    """Return the paper's closed-form polynomial for k<=3 and parity in {'even','odd'}."""
    n = sp.Symbol("n")
    if parity not in {"even", "odd"}:
        raise ValueError("parity must be 'even' or 'odd'")

    if k == 0:
        expr = n + 1
    elif k == 1 and parity == "even":
        expr = sp.Rational(1, 3) * n**3 + sp.Rational(3, 2) * n**2 + sp.Rational(1, 6) * n
    elif k == 1 and parity == "odd":
        expr = sp.Rational(1, 3) * n**3 + sp.Integer(2) * n**2 + sp.Rational(5, 3) * n + 1
    elif k == 2 and parity == "even":
        expr = (
            sp.Rational(1, 30) * n**5
            + sp.Rational(3, 8) * n**4
            - sp.Rational(1, 12) * n**3
            - sp.Rational(7, 8) * n**2
            + sp.Rational(11, 20) * n
        )
    elif k == 2 and parity == "odd":
        expr = (
            sp.Rational(1, 30) * n**5
            + sp.Rational(11, 24) * n**4
            + sp.Rational(3, 4) * n**3
            - sp.Rational(11, 24) * n**2
            + sp.Rational(13, 60) * n
        )
    elif k == 3 and parity == "even":
        expr = (
            sp.Rational(1, 630) * n**7
            + sp.Rational(1, 30) * n**6
            + sp.Rational(7, 360) * n**5
            - sp.Rational(17, 24) * n**4
            + sp.Rational(523, 360) * n**3
            - sp.Rational(33, 40) * n**2
            + sp.Rational(11, 420) * n
        )
    elif k == 3 and parity == "odd":
        expr = (
            sp.Rational(1, 630) * n**7
            + sp.Rational(7, 180) * n**6
            + sp.Rational(23, 180) * n**5
            - sp.Rational(19, 36) * n**4
            + sp.Rational(29, 180) * n**3
            + sp.Rational(22, 45) * n**2
            - sp.Rational(61, 210) * n
        )
    else:
        raise ValueError("closed form only provided for k<=3")

    return sp.Poly(sp.expand(expr), n, domain=sp.QQ)


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit fixed-k low-weight coefficient quasipolynomials for Z_m(y)")
    parser.add_argument("--k-max", type=int, default=6, help="Max k to check for stable quasipolynomial structure (default: 6)")
    parser.add_argument("--m-max", type=int, default=260, help="Max m to build the (m,k) table (default: 260)")
    parser.add_argument("--n-check-max", type=int, default=120, help="Max n to verify k<=3 closed forms (default: 120)")
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-low-weight-quasi] start", flush=True)

    if args.k_max < 0:
        raise SystemExit("--k-max must be non-negative")
    if args.m_max < 0:
        raise SystemExit("--m-max must be non-negative")
    if args.n_check_max < 0:
        raise SystemExit("--n-check-max must be non-negative")

    a = build_a_table(args.m_max)
    m_sym = sp.Symbol("m")

    checks: Dict[str, object] = {"k_max": args.k_max, "m_max": args.m_max, "n_check_max": args.n_check_max}
    per_k: Dict[str, object] = {}

    all_ok = True
    for k in range(0, args.k_max + 1):
        deg_p = 2 * k + 1
        deg_q = k
        unknown_count = (deg_p + 1) + (deg_q + 1)

        # Stable range start: large enough that any finite-support polynomial part in A_k(t)
        # does not interfere with the quasipolynomial representation.
        m0 = 3 * k + 3
        if args.m_max < m0 + unknown_count - 1:
            raise SystemExit(
                f"--m-max too small for k={k}: need at least {m0 + unknown_count - 1} to fit/verify (got {args.m_max})"
            )

        def get_a(mm: int) -> int:
            row = a[mm]
            return row[k] if k < len(row) else 0

        samples = [(mm, get_a(mm)) for mm in range(m0, m0 + unknown_count)]
        P, Q = _solve_pq_from_samples(samples=samples, deg_p=deg_p, deg_q=deg_q)

        # Verify on the whole stable range.
        stable_ok = True
        first_mismatch_m = None
        for mm in range(m0, args.m_max + 1):
            pred = P.eval(mm) + ((-1) ** mm) * Q.eval(mm)
            if sp.Integer(get_a(mm)) != sp.Integer(pred):
                stable_ok = False
                first_mismatch_m = int(mm)
                break

        # Degree + leading coefficient of P.
        expected_lc_p = sp.Rational(1, 2 ** (k + 1) * sp.factorial(2 * k + 1))
        deg_p_ok = int(P.degree(m_sym)) == int(deg_p)
        deg_q_ok = int(Q.degree(m_sym)) == int(deg_q)
        lc_p_ok = deg_p_ok and (sp.simplify(P.LC() - expected_lc_p) == 0)

        # Leading coefficient of Q.
        expected_lc_q = sp.Rational(1, 2 ** (2 * k + 2) * sp.factorial(k))
        lc_q_ok = deg_q_ok and (sp.simplify(Q.LC() - expected_lc_q) == 0)

        # Closed forms for k<=3 (parity-polynomial forms in n).
        closed_ok = None
        closed_checked_up_to_n = None
        if k <= 3:
            poly_even = _closed_form_poly(k=k, parity="even")
            poly_odd = _closed_form_poly(k=k, parity="odd")
            n_even_max = args.m_max // 2
            n_odd_max = (args.m_max - 1) // 2
            n_check = min(args.n_check_max, n_even_max, n_odd_max)
            closed_checked_up_to_n = int(n_check)
            closed_ok = True
            for n in range(0, n_check + 1):
                if sp.Integer(get_a(2 * n)) != sp.Integer(poly_even.eval(n)):
                    closed_ok = False
                    break
                if sp.Integer(get_a(2 * n + 1)) != sp.Integer(poly_odd.eval(n)):
                    closed_ok = False
                    break

        ok_k = stable_ok and deg_p_ok and deg_q_ok and lc_p_ok and lc_q_ok and (True if closed_ok is None else bool(closed_ok))
        all_ok = all_ok and ok_k

        per_k[str(k)] = {
            "deg_p": int(deg_p),
            "deg_q_bound": int(deg_q),
            "m0_stable_range": int(m0),
            "stable_ok": bool(stable_ok),
            "first_mismatch_m": first_mismatch_m,
            "deg_p_ok": bool(deg_p_ok),
            "deg_q_ok": bool(deg_q_ok),
            "leading_coeff_p_expected": str(expected_lc_p),
            "leading_coeff_p": str(P.LC()),
            "leading_coeff_p_ok": bool(lc_p_ok),
            "leading_coeff_q_expected": str(expected_lc_q),
            "leading_coeff_q": str(Q.LC()),
            "leading_coeff_q_ok": bool(lc_q_ok),
            "P": _poly_to_json(P),
            "Q": _poly_to_json(Q),
            "closed_form_k_le_3_ok": (None if closed_ok is None else bool(closed_ok)),
            "closed_form_checked_up_to_n": closed_checked_up_to_n,
            "ok": bool(ok_k),
        }

    # Golden-factor check for the numerator polynomials P_k(t) modulo t^2 - t - 1.
    k_phi_max = max(34, 5 * args.k_max + 4)
    pk_mod = _pk_mod_phi_gold(k_phi_max)

    # Check M^5 = -(55 t + 34) I_2 in Mat_2(Z[t]/(t^2 - t - 1)).
    t_el = _PHI_T
    M = [[-t_el, -_PhiGold(2, 3)], [_PHI_ONE, _PHI_ZERO]]
    M5 = _mat2_pow(M, 5)
    scale = -_PhiGold(34, 55)  # -(34 + 55 t)
    M5_expected = [[scale, _PHI_ZERO], [_PHI_ZERO, scale]]
    m5_ok = (M5 == M5_expected)

    idxs: List[int] = []
    rems: Dict[str, object] = {}
    phi_ok = True
    n = 0
    while True:
        k_idx = 5 * n + 4
        if k_idx > k_phi_max:
            break
        idxs.append(k_idx)
        r = pk_mod[k_idx]
        rems[str(k_idx)] = r.to_json()
        phi_ok = phi_ok and r.is_zero()
        n += 1

    checks["numerator_phi_gold"] = {
        "phi_poly": "t^2 - t - 1",
        "k_max_checked": int(k_phi_max),
        "indices_5n_plus_4_checked": idxs,
        "remainders_mod_phi": rems,
        "all_remainders_zero": bool(phi_ok),
        "matrix_M5_ok": bool(m5_ok),
        "matrix_M5_scale": scale.to_json(),
    }

    all_ok = all_ok and bool(phi_ok) and bool(m5_ok)

    checks["per_k"] = per_k
    checks["all_ok"] = bool(all_ok)
    checks["elapsed_s"] = float(time.time() - t0)

    if not args.no_output:
        out_json = export_dir() / "fold_zm_low_weight_quasipolynomial_audit.json"
        out_tex = generated_dir() / "eq_fold_zm_low_weight_quasipolynomial_audit.tex"

        _write_json(out_json, checks)

        # Keep the TeX output compact; detailed formulas live in the paper body.
        tex_lines = [
            "% Auto-generated by scripts/exp_fold_zm_low_weight_quasipolynomial_audit.py",
            "\\[",
            "a_{2n,k}=\\frac{2^{k}}{(2k+1)!}n^{2k+1}+O\\!\\left(n^{2k}\\right),\\qquad",
            "a_{2n+1,k}=\\frac{2^{k}}{(2k+1)!}n^{2k+1}+O\\!\\left(n^{2k}\\right)\\qquad(n\\to\\infty).",
            "\\]",
            "",
        ]
        _write_text(out_tex, "\n".join(tex_lines))

        print(f"[fold-zm-low-weight-quasi] wrote {out_json}", flush=True)
        print(f"[fold-zm-low-weight-quasi] wrote {out_tex}", flush=True)

    print(f"[fold-zm-low-weight-quasi] checks: all_ok={all_ok}", flush=True)
    print("[fold-zm-low-weight-quasi] done", flush=True)


if __name__ == "__main__":
    main()

