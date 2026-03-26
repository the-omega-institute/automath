#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the Fold fiber-weight bivariate partition function Z_m(y).

This script is English-only by repository convention.

We verify, by exact small-m enumeration and symbolic algebra:
  - The order-4 recurrence and rational t-generating function for Z_m(y)
  - The characteristic quartic Pi(lambda,y)
  - Discriminant factorization and the real Lee–Yang boundary root
  - LLN/CLT constants (mean/variance rates) and higher cumulant rates via the analytic branch at (lambda,y)=(2,1)
  - The local (m,k) 2D recurrence for coefficients a_{m,k}
  - Exact finite-m closed forms for M1(m), M2(m), Var(H_m), and kappa_3(H_m)
  - The quintic elimination certificate for the LDP saddlepoint y(alpha)

Outputs (default):
  - artifacts/export/fold_zm_bivariate_partition_audit.json
  - sections/generated/eq_fold_zm_bivariate_partition_audit.tex
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
import time
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fold_m


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def enumerate_a_mk(m: int) -> List[int]:
    # a_{m,k} = sum_{x in X_m, |x|_1=k} d_m(x) = # {a in Omega_m : |Fold_m(a)|_1 = k}
    counts = [0] * (m + 1)
    for bits in product([0, 1], repeat=m):
        x = fold_m(bits)
        k = sum(x)
        counts[k] += 1
    return counts


def build_Z_polys(m_max: int, prog: Progress) -> Tuple[sp.Symbol, List[sp.Expr], List[List[int]]]:
    y = sp.Symbol("y")
    Z_exprs: List[sp.Expr] = []
    a: List[List[int]] = []
    for m in range(m_max + 1):
        counts = enumerate_a_mk(m)
        a.append(counts)
        expr = sp.Integer(0)
        for k, c in enumerate(counts):
            if c:
                expr += sp.Integer(c) * (y**k)
        Z_exprs.append(sp.expand(expr))
        prog.tick(f"enumerate m={m} total_micro={1<<m}")
    return y, Z_exprs, a


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Z_m(y) recurrence, discriminant, and LLN/CLT constants")
    parser.add_argument("--m-max", type=int, default=12, help="Max m for exact enumeration checks (default: 12)")
    parser.add_argument(
        "--m-closed-max",
        type=int,
        default=80,
        help="Max m for closed-form checks via differentiated recurrences (default: 80)",
    )
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs")
    args = parser.parse_args()

    t0 = time.time()
    prog = Progress(label="fold-zm-audit", every_seconds=10.0)
    print("[fold-zm-audit] start", flush=True)

    # --- Exact enumeration for Z_m(y) as polynomials in y ---
    y, Zm, a_mk = build_Z_polys(args.m_max, prog)

    # --- Recurrence and generating function checks ---
    t = sp.Symbol("t")
    N = 1 + y * t - y * t**2 - y**2 * t**3
    D = 1 - t - (2 * y + 1) * t**2 + t**3 + y * (y + 1) * t**4

    rec_ok = True
    rec_fail: List[Dict[str, object]] = []
    for m in range(4, args.m_max + 1):
        lhs = Zm[m]
        rhs = sp.expand(Zm[m - 1] + (2 * y + 1) * Zm[m - 2] - Zm[m - 3] - y * (y + 1) * Zm[m - 4])
        diff = sp.expand(lhs - rhs)
        if diff != 0:
            rec_ok = False
            rec_fail.append({"m": m, "diff": str(diff)})

    # series expansion of N/D and compare coefficients to enumerated Z_m(y)
    gen_ok = True
    gen_fail: List[Dict[str, object]] = []
    series = sp.series(N / D, t, 0, args.m_max + 1).removeO()
    series = sp.expand(series)
    for m in range(0, args.m_max + 1):
        coeff = sp.expand(sp.series(N / D, t, 0, m + 1).removeO().coeff(t, m))
        if sp.expand(coeff - Zm[m]) != 0:
            gen_ok = False
            gen_fail.append({"m": m, "coeff_minus_Zm": str(sp.expand(coeff - Zm[m]))})

    # --- 2D (m,k) recurrence check for a_{m,k} ---
    rec2_ok = True
    rec2_fail: List[Dict[str, object]] = []
    for m in range(4, args.m_max + 1):
        k_max = (m + 1) // 2  # ceil(m/2)
        for k in range(0, k_max + 1):
            get = lambda mm, kk: (a_mk[mm][kk] if (0 <= kk < len(a_mk[mm])) else 0)
            lhs = get(m, k)
            rhs = (
                get(m - 1, k)
                + get(m - 2, k)
                + 2 * get(m - 2, k - 1)
                - get(m - 3, k)
                - get(m - 4, k - 1)
                - get(m - 4, k - 2)
            )
            if lhs != rhs:
                rec2_ok = False
                rec2_fail.append({"m": m, "k": k, "lhs": lhs, "rhs": rhs})
                break
        if not rec2_ok:
            break

    # --- Symbolic algebra for Pi(lambda,y) and discriminant ---
    lam = sp.Symbol("lam")
    Pi = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)
    disc = sp.factor(sp.discriminant(Pi, lam))
    disc_expected = -y * (y - 1) * (256 * y**3 + 411 * y**2 + 165 * y + 32)
    disc_ok = sp.factor(disc - disc_expected) == 0

    # Lee–Yang real root
    cubic = 256 * y**3 + 411 * y**2 + 165 * y + 32

    # --- Exterior-square sextic chi^(2)(mu;y) (wedge^2 companion) ---
    mu = sp.Symbol("mu")
    C = sp.Matrix([[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [-y * (y + 1), -1, 2 * y + 1, 1]])
    pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    W2 = sp.Matrix(6, 6, lambda r, c: C[pairs[r][0], pairs[c][0]] * C[pairs[r][1], pairs[c][1]] - C[pairs[r][0], pairs[c][1]] * C[pairs[r][1], pairs[c][0]])
    chi2_expected = mu**6 + (2 * y + 1) * mu**5 - (y**2 + y + 1) * mu**4 - (4 * y**3 + 7 * y**2 + 3 * y + 1) * mu**3 - (y**4 + 2 * y**3 + 2 * y**2 + y) * mu**2 + (2 * y**5 + 5 * y**4 + 4 * y**3 + y**2) * mu + y**3 * (y + 1) ** 3
    chi2_ok = sp.factor(sp.expand(W2.charpoly(mu).as_expr()) - chi2_expected) == 0
    disc2_ok = sp.factor(sp.factor(sp.discriminant(chi2_expected, mu)) - (y**4 * (y - 1) * (y + 1) ** 3 * (y**2 + y - 1) * cubic) ** 2) == 0
    chi2_minus1_ok = sp.factor(chi2_expected.subs({mu: -1}) - y * (y - 1) * (y**2 + y - 1) ** 2) == 0
    roots = [complex(r) for r in sp.nroots(cubic)]
    y_ly = None
    for r in roots:
        if abs(r.imag) < 1e-10:
            y_ly = float(r.real)
            break

    # --- Implicit differentiation at (lam,y)=(2,1) for mean/variance ---
    Pi_l = sp.diff(Pi, lam)
    Pi_y = sp.diff(Pi, y)
    Pi_ll = sp.diff(Pi, lam, 2)
    Pi_ly = sp.diff(Pi, lam, 1, y, 1)
    Pi_yy = sp.diff(Pi, y, 2)

    lam0 = sp.Integer(2)
    y0 = sp.Integer(1)
    A = sp.simplify(Pi_l.subs({lam: lam0, y: y0}))
    By = sp.simplify(Pi_y.subs({lam: lam0, y: y0}))
    lam1 = sp.simplify(-By / A)  # d lam / d y at y=1

    ll0 = sp.simplify(Pi_ll.subs({lam: lam0, y: y0}))
    ly0 = sp.simplify(Pi_ly.subs({lam: lam0, y: y0}))
    yy0 = sp.simplify(Pi_yy.subs({lam: lam0, y: y0}))
    lam2 = sp.simplify(-(yy0 + 2 * ly0 * lam1 + ll0 * lam1**2) / A)  # d^2 lam / d y^2 at y=1

    mean = sp.simplify((y0 * lam1) / lam0)  # psi'(0)
    var = sp.simplify(lam1 / lam0 + lam2 / lam0 - (lam1 / lam0) ** 2)  # psi''(0)

    mean_ok = sp.simplify(mean - sp.Rational(5, 18)) == 0
    var_ok = sp.simplify(var - sp.Rational(67, 972)) == 0

    # --- Higher cumulant rates via local series at y=1 ---
    ORDER = 9  # compute up to s^8 (kappa_8)
    u = sp.Symbol("u")
    c = sp.symbols("c1:9")  # c1,...,c8
    y_ser = y0 + u
    lam_ser = lam0 + sp.Add(*[c[j - 1] * u**j for j in range(1, 9)])
    Pi_u = sp.expand(Pi.subs({lam: lam_ser, y: y_ser}).series(u, 0, ORDER).removeO())
    eqs = [sp.Eq(Pi_u.coeff(u, k), 0) for k in range(1, 9)]
    sol = sp.solve(eqs, list(c), dict=True)[0]
    lam_ser_u = sp.expand(lam_ser.subs(sol))

    s = sp.Symbol("s")
    lam_ser_s = sp.expand(lam_ser_u.subs({u: sp.exp(s) - 1}).series(s, 0, ORDER).removeO())
    psi_ser = sp.expand((sp.log(lam_ser_s) - sp.log(2)).series(s, 0, ORDER).removeO())
    kappa = [sp.simplify(sp.diff(psi_ser, s, n).subs({s: 0})) for n in range(1, 9)]
    kappa1, kappa2, kappa3, kappa4, kappa5, kappa6, kappa7, kappa8 = kappa

    kappa3_ok = sp.simplify(kappa3 + sp.Rational(22, 2187)) == 0
    kappa4_ok = sp.simplify(kappa4 + sp.Rational(1763, 157464)) == 0

    # --- Nearest complex Lee--Yang branch pair in s=log y (principal branch) ---
    y_complex = [r for r in roots if abs(r.imag) >= 1e-10]
    y_c_plus = max(y_complex, key=lambda z: z.imag) if y_complex else None
    y_c_minus = y_c_plus.conjugate() if y_c_plus is not None else None
    s_c_plus = cmath.log(y_c_plus) if y_c_plus is not None else None
    rho_s = abs(s_c_plus) if s_c_plus is not None else None
    theta_s = math.atan2(s_c_plus.imag, s_c_plus.real) if s_c_plus is not None else None

    # Critical (lambda_c,y_c) and the square-root amplitude constant for psi(s)
    lam_c = None
    B_abs = None
    if y_c_plus is not None:
        lam_cubic = 16 * lam**3 - 9 * lam**2 + 1
        lam_crit_roots = [complex(r) for r in sp.nroots(lam_cubic)]

        def _y_of_lam(z: complex) -> complex:
            return (4 * z**3 - 3 * z**2 - 2 * z + 1) / (4 * z)

        lam_c, _ = min(((z, _y_of_lam(z)) for z in lam_crit_roots), key=lambda p: abs(p[1] - y_c_plus))
        dy_val = complex(sp.N(Pi_y.subs({lam: lam_c, y: y_c_plus}), 50))
        dll_val = complex(sp.N(Pi_ll.subs({lam: lam_c, y: y_c_plus}), 50))
        c_sq = -2.0 * dy_val / dll_val
        c_val = cmath.sqrt(c_sq)
        B_val = c_val * cmath.sqrt(y_c_plus) / lam_c
        B_abs = abs(B_val)

    # Self-inversive spot check at primitive cube root y = exp(2pi i/3)
    omega = complex(-0.5, math.sqrt(3) / 2.0)
    coeffs = [
        complex(sp.N(sp.Integer(1))),  # lam^4
        complex(sp.N(sp.Integer(-1))),  # lam^3
        complex(sp.N(-(2 * omega + 1))),  # lam^2
        complex(sp.N(sp.Integer(1))),  # lam^1
        complex(sp.N(omega * (omega + 1))),  # lam^0
    ]
    # Find c from a3 = c * conj(a1).
    c = coeffs[1] / coeffs[3].conjugate()
    self_inv_ok = abs(abs(c) - 1.0) < 1e-12
    for k in range(5):
        if abs(coeffs[k] - c * coeffs[4 - k].conjugate()) > 1e-10:
            self_inv_ok = False
            break

    # --- Exact finite-m closed forms (checked against differentiated recurrences) ---
    if args.m_max < 3:
        raise ValueError("--m-max must be >= 3 to seed differentiated recurrences from enumeration")
    m_closed_max = int(max(4, args.m_closed_max))

    # A_m = Z_m(1) = 2^m
    A_m = [1 << mm for mm in range(m_closed_max + 1)]
    B_m = [0] * (m_closed_max + 1)  # Z_m'(1)
    C_m = [0] * (m_closed_max + 1)  # Z_m''(1)
    D_m = [0] * (m_closed_max + 1)  # Z_m'''(1)

    for mm in range(0, 4):
        B_m[mm] = int(sp.diff(Zm[mm], y).subs({y: 1}))
        C_m[mm] = int(sp.diff(Zm[mm], y, 2).subs({y: 1}))
        D_m[mm] = int(sp.diff(Zm[mm], y, 3).subs({y: 1}))

    for mm in range(4, m_closed_max + 1):
        # Differentiate the order-4 recurrence at y=1 (Z_m(1)=2^m).
        B_m[mm] = (
            B_m[mm - 1]
            + 3 * B_m[mm - 2]
            + 2 * A_m[mm - 2]
            - B_m[mm - 3]
            - 2 * B_m[mm - 4]
            - 3 * A_m[mm - 4]
        )
        C_m[mm] = (
            C_m[mm - 1]
            + 3 * C_m[mm - 2]
            + 4 * B_m[mm - 2]
            - C_m[mm - 3]
            - 2 * C_m[mm - 4]
            - 6 * B_m[mm - 4]
            - 2 * A_m[mm - 4]
        )
        D_m[mm] = (
            D_m[mm - 1]
            + 3 * D_m[mm - 2]
            + 6 * C_m[mm - 2]
            - D_m[mm - 3]
            - 2 * D_m[mm - 4]
            - 9 * C_m[mm - 4]
            - 6 * B_m[mm - 4]
        )

    def _M1_closed(mm: int) -> Fraction:
        eps = -1 if (mm % 2 == 1) else 1
        return (
            (Fraction(5, 18) * mm - Fraction(1, 27)) * (1 << mm)
            + Fraction(1, 4)
            - (Fraction(mm, 18) + Fraction(23, 108)) * eps
        )

    def _M2_closed(mm: int) -> Fraction:
        eps = -1 if (mm % 2 == 1) else 1
        return (
            (Fraction(25, 324) * mm * mm + Fraction(47, 972) * mm + Fraction(113, 729)) * (1 << mm)
            + Fraction(mm, 8)
            + (Fraction(mm**3, 324) - Fraction(mm * mm, 54) - Fraction(31 * mm, 216) - Fraction(113, 729)) * eps
        )

    def _Var_closed(mm: int) -> Fraction:
        eps = -1 if (mm % 2 == 1) else 1
        term0 = Fraction(67, 972) * mm + Fraction(112, 729)
        term1 = Fraction(1, 2**mm) * (
            Fraction(1, 54)
            - Fraction(mm, 72)
            + (Fraction(mm**3, 324) + Fraction(mm * mm, 81) - Fraction(19 * mm, 648) - Fraction(83, 486)) * eps
        )
        term2 = Fraction(1, 2 ** (2 * mm)) * (
            Fraction(1, 16)
            - (Fraction(mm, 36) + Fraction(23, 216)) * eps
            + (Fraction(mm, 18) + Fraction(23, 108)) ** 2
        )
        return term0 + term1 - term2

    def _kappa3_closed(mm: int) -> Fraction:
        eps = -1 if (mm % 2 == 1) else 1
        q1 = Fraction(1, 2**mm)
        q2 = Fraction(1, 2 ** (2 * mm))
        q3 = Fraction(1, 2 ** (3 * mm))

        base = -Fraction(22, 2187) * mm + Fraction(52, 19683)
        P1 = (
            Fraction(mm * mm, 1728)
            + Fraction(151 * mm, 1728)
            - Fraction(293, 10368)
            + eps
            * (
                -Fraction(mm**5, 12960)
                + Fraction(7 * mm**4, 15552)
                + Fraction(41 * mm**3, 11664)
                - Fraction(487 * mm * mm, 46656)
                - Fraction(2699 * mm, 77760)
                + Fraction(2407, 279936)
            )
        )
        P2 = (
            Fraction(mm**4, 1944)
            + Fraction(47 * mm**3, 11664)
            + Fraction(35 * mm * mm, 11664)
            - Fraction(143 * mm, 3888)
            - Fraction(269, 2187)
            + eps * (-Fraction(mm**3, 432) - Fraction(5 * mm * mm, 432) + Fraction(7 * mm, 432) + Fraction(34, 243))
        )
        P3 = (
            Fraction(mm * mm, 216)
            + Fraction(23 * mm, 648)
            + Fraction(193, 1944)
            + eps
            * (
                -Fraction(mm**3, 2916)
                - Fraction(23 * mm * mm, 5832)
                - Fraction(629 * mm, 17496)
                - Fraction(15617, 157464)
            )
        )
        return base + q1 * P1 + q2 * P2 + q3 * P3

    def _check_closed_forms() -> Tuple[bool, List[Dict[str, object]]]:
        fails: List[Dict[str, object]] = []
        for mm in range(1, m_closed_max + 1):
            M1 = Fraction(B_m[mm], 1)
            M2 = Fraction(C_m[mm] + B_m[mm], 1)
            E1 = Fraction(B_m[mm], A_m[mm])
            E2 = Fraction(C_m[mm] + B_m[mm], A_m[mm])
            Var = E2 - E1 * E1
            M3 = Fraction(D_m[mm] + 3 * C_m[mm] + B_m[mm], 1)
            E3 = M3 / A_m[mm]
            k3 = E3 - 3 * E2 * E1 + 2 * E1 * E1 * E1

            ok = True
            if M1 != _M1_closed(mm):
                ok = False
            if M2 != _M2_closed(mm):
                ok = False
            if Var != _Var_closed(mm):
                ok = False
            if k3 != _kappa3_closed(mm):
                ok = False
            if not ok:
                fails.append({"m": int(mm)})
                if len(fails) >= 5:
                    break
        return (len(fails) == 0), fails

    closed_ok, closed_fail_head = _check_closed_forms()

    # --- Annihilator spot checks for raw moments M_r (r<=3) ---
    def _annihilator_coeffs(r: int) -> List[int]:
        # (E-2)^{r+1}(E-1)^r(E+1)^{2r} with integer coefficients in E^k.
        from math import comb

        def factor(c: int, n: int) -> List[int]:
            return [comb(n, j) * ((-c) ** (n - j)) for j in range(n + 1)]

        def conv(a: List[int], b: List[int]) -> List[int]:
            out = [0] * (len(a) + len(b) - 1)
            for i, ai in enumerate(a):
                for j, bj in enumerate(b):
                    out[i + j] += ai * bj
            return out

        coeff = [1]
        coeff = conv(coeff, factor(2, r + 1))
        coeff = conv(coeff, factor(1, r))
        coeff = conv(coeff, factor(-1, 2 * r))
        return coeff

    def _annihilator_holds(seq: List[int], coeff: List[int]) -> bool:
        deg = len(coeff) - 1
        for i in range(0, len(seq) - deg):
            s = 0
            for k, ck in enumerate(coeff):
                s += ck * seq[i + k]
            if s != 0:
                return False
        return True

    M0_seq = A_m
    M1_seq = B_m
    M2_seq = [C_m[mm] + B_m[mm] for mm in range(m_closed_max + 1)]
    M3_seq = [D_m[mm] + 3 * C_m[mm] + B_m[mm] for mm in range(m_closed_max + 1)]
    ann_ok = (
        _annihilator_holds(M0_seq, _annihilator_coeffs(0))
        and _annihilator_holds(M1_seq, _annihilator_coeffs(1))
        and _annihilator_holds(M2_seq, _annihilator_coeffs(2))
        and _annihilator_holds(M3_seq, _annihilator_coeffs(3))
    )

    # --- Quintic elimination certificate for y(alpha) ---
    alpha = sp.Symbol("alpha")
    Eq = alpha * lam * sp.diff(Pi, lam) + y * sp.diff(Pi, y)
    Res = sp.resultant(Pi, Eq, lam)
    F = (
        256 * alpha**4 * y**5
        + 411 * alpha**4 * y**4
        - 91 * alpha**4 * y**3
        - 379 * alpha**4 * y**2
        - 165 * alpha**4 * y
        - 32 * alpha**4
        - 512 * alpha**3 * y**5
        - 566 * alpha**3 * y**4
        + 337 * alpha**3 * y**3
        + 512 * alpha**3 * y**2
        + 197 * alpha**3 * y
        + 32 * alpha**3
        + 384 * alpha**2 * y**5
        + 228 * alpha**2 * y**4
        - 298 * alpha**2 * y**3
        - 214 * alpha**2 * y**2
        - 28 * alpha**2 * y
        - 128 * alpha * y**5
        - 8 * alpha * y**4
        + 86 * alpha * y**3
        + 16 * alpha * y**2
        - 4 * alpha * y
        + 16 * y**5
        - 8 * y**4
        - 4 * y**3
        + y**2
    )
    Res_poly = sp.Poly(Res, y, alpha)
    F_poly = sp.Poly(F, y, alpha)
    q_poly, r_poly = sp.div(Res_poly, F_poly)
    ldp_quintic_ok = bool(r_poly.is_zero and sp.factor(q_poly.as_expr()) == -y**2)

    payload: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "generated_at_unix_s": float(time.time()),
            "seconds": float(time.time() - t0),
        },
        "params": {"m_max": int(args.m_max), "m_closed_max": int(m_closed_max)},
        "checks": {
            "recurrence_order4_polynomial_ok": rec_ok,
            "recurrence_order4_fail_head": rec_fail[:5],
            "generating_function_series_ok": gen_ok,
            "generating_function_fail_head": gen_fail[:5],
            "recurrence_2d_amk_ok": rec2_ok,
            "recurrence_2d_fail_head": rec2_fail[:5],
            "discriminant_factorization_ok": bool(disc_ok),
            "exterior_square_charpoly_ok": bool(chi2_ok),
            "exterior_square_discriminant_square_ok": bool(disc2_ok),
            "exterior_square_mu_minus1_ok": bool(chi2_minus1_ok),
            "mean_ok_5_over_18": bool(mean_ok),
            "var_ok_67_over_972": bool(var_ok),
            "kappa3_rate_ok_neg_22_over_2187": bool(kappa3_ok),
            "kappa4_rate_ok_neg_1763_over_157464": bool(kappa4_ok),
            "self_inversive_check_at_omega_ok": bool(self_inv_ok),
            "closed_forms_moments_var_kappa3_ok": bool(closed_ok),
            "closed_forms_fail_head": closed_fail_head,
            "raw_moment_annihilators_r_le_3_ok": bool(ann_ok),
            "ldp_saddle_quintic_resultant_ok": bool(ldp_quintic_ok),
        },
        "polynomials": {
            "Pi_lambda_y": str(Pi),
            "Disc_lambda_factor": str(disc),
            "Disc_lambda_expected": str(disc_expected),
            "cubic_branch_factor": str(cubic),
            "ldp_saddle_quintic_F_alpha_y": str(F),
        },
        "numeric": {
            "y_LY_real_root": None if y_ly is None else float(y_ly),
            "mean": {"exact": str(mean), "float": float(sp.N(mean))},
            "var": {"exact": str(var), "float": float(sp.N(var))},
            "kappa3_rate": {"exact": str(kappa3), "float": float(sp.N(kappa3))},
            "kappa4_rate": {"exact": str(kappa4), "float": float(sp.N(kappa4))},
            "kappa5_rate": {"exact": str(kappa5), "float": float(sp.N(kappa5))},
            "kappa6_rate": {"exact": str(kappa6), "float": float(sp.N(kappa6))},
            "kappa7_rate": {"exact": str(kappa7), "float": float(sp.N(kappa7))},
            "kappa8_rate": {"exact": str(kappa8), "float": float(sp.N(kappa8))},
            "y_c_plus": None if y_c_plus is None else {"re": float(y_c_plus.real), "im": float(y_c_plus.imag)},
            "s_c_plus": None
            if s_c_plus is None
            else {"re": float(s_c_plus.real), "im": float(s_c_plus.imag), "abs": float(rho_s), "arg": float(theta_s)},
            "lambda_c": None if lam_c is None else {"re": float(lam_c.real), "im": float(lam_c.imag)},
            "B_abs": None if B_abs is None else float(B_abs),
        },
        "Z_m_coeffs_a_mk_head": [
            {"m": m, "a_mk": a_mk[m][: (m + 1)]} for m in range(min(args.m_max, 8) + 1)
        ],
    }

    if not args.no_output:
        out_json = export_dir() / "fold_zm_bivariate_partition_audit.json"
        _write_json(out_json, payload)

        def _latex_q(expr: sp.Expr) -> str:
            return sp.latex(sp.simplify(expr))

        # Minimal TeX snippet (optional in the paper).
        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_fold_zm_bivariate_partition_audit.py",
                "\\[",
                "\\Pi(\\lambda,y)=\\lambda^{4}-\\lambda^{3}-(2y+1)\\lambda^{2}+\\lambda+y(y+1).",
                "\\]",
                "\\[",
                "\\mathrm{Disc}_{\\lambda}(\\Pi)=-y\\,(y-1)\\,(256y^{3}+411y^{2}+165y+32).",
                "\\]",
                f"\\[y_{{\\mathrm{{LY}}}}\\approx {y_ly:.10f}.\\]" if y_ly is not None else "% y_LY not found",
                "\\[",
                "\\psi'(0)=\\frac{5}{18},\\qquad \\psi''(0)=\\frac{67}{972}.",
                "\\]",
                "\\[",
                f"\\psi^{{(3)}}(0)={_latex_q(kappa3)},\\qquad \\psi^{{(4)}}(0)={_latex_q(kappa4)}.",
                "\\]",
                "\\[",
                f"\\psi^{{(5)}}(0)={_latex_q(kappa5)},\\qquad \\psi^{{(6)}}(0)={_latex_q(kappa6)}.",
                "\\]",
                "\\[",
                f"\\psi^{{(7)}}(0)={_latex_q(kappa7)},\\qquad \\psi^{{(8)}}(0)={_latex_q(kappa8)}.",
                "\\]",
                "\\[",
                "16e^{4\\psi(s)}-8e^{3\\psi(s)}-4(2e^{s}+1)e^{2\\psi(s)}+2e^{\\psi(s)}+e^{2s}+e^{s}=0.",
                "\\]",
                "",
            ]
        )
        out_tex = generated_dir() / "eq_fold_zm_bivariate_partition_audit.tex"
        _write_text(out_tex, tex)

        print(f"[fold-zm-audit] wrote {out_json}", flush=True)
        print(f"[fold-zm-audit] wrote {out_tex}", flush=True)

    print(
        f"[fold-zm-audit] checks: rec={rec_ok} gen={gen_ok} disc={disc_ok} mean_ok={mean_ok} var_ok={var_ok} k3_ok={kappa3_ok} k4_ok={kappa4_ok} closed_ok={closed_ok} quintic_ok={ldp_quintic_ok} y_LY={y_ly}",
        flush=True,
    )
    print("[fold-zm-audit] done", flush=True)


if __name__ == "__main__":
    main()

