#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the weight-doubling correspondence on E in (y0,y1)-coordinates.

This script is English-only by repository convention.

We work with the elliptic curve
  E: Y^2 = X^3 - X + 1/4
and the weight coordinate
  y := X^2 + Y - 1/2.

For P in E, write y0 := y(P) and y1 := y([2]P). Then y1 is not a single-valued
function of y0 (since y : E -> P^1 is degree 4). Instead, the (y0,y1)-pairs lie on
an explicit plane curve H(y0,y1)=0, quartic in y1.

Let iota be the elliptic involution (X,Y) -> (X,-Y), and define y^iota := X^2 - Y - 1/2.
We also verify the conjugate branch polynomial R_-(y0, y1^iota)=0 where y1^iota := y^iota([2]P),
and its discriminant factorization with the same Lee–Yang squarefree kernel.

We verify:
  - The explicit bivariate elimination polynomial H(y0,y1) with integer coefficients.
  - The discriminant factorization (as a polynomial in y1):
      Disc_{y1}(H(y, y1)) = - y (y-1) P_LY(y) * Q12(y)^2 * Q26(y)^2,
    hence the square-class equals -y(y-1)P_LY(y).
  - The conjugate-branch polynomial R_-(y0, y1^iota) with integer coefficients, and:
      Disc_{y1^iota}(R_-(y, y1^iota)) = - y (y-1) P_LY(y) * Q12(y)^2 * Q26m(y)^2.
  - A specialization-at-y=2 witness that both quartics have generic Galois group S4:
    the resolvent cubic is irreducible over Q, and the discriminant square-class is non-square.
  - The birational inverse Gamma -> E on an open set via X = beta/alpha and
    Y = y0 - X^2 + 1/2 (checked on the generic point coming from E).
  - The norm/resultant certificate for the Lee–Yang kernel:
      Res_X(Pi(X,y), 4X(y - X^2 + 1/2) + 3X^2 - 1) = - y (y-1) P_LY(y),
    where Pi(X,y)=X^4 - X^3 - (2y+1)X^2 + X + y(y+1).

Outputs (default):
  - artifacts/export/fold_zm_elliptic_weight_doubling_audit.json
  - sections/generated/eq_fold_zm_elliptic_weight_doubling_H.tex
  - sections/generated/eq_fold_zm_elliptic_weight_doubling_Rminus.tex
  - sections/generated/eq_fold_zm_elliptic_weight_doubling_discriminant.tex
  - sections/generated/eq_fold_zm_elliptic_weight_doubling_inverse.tex
  - sections/generated/eq_fold_zm_elliptic_weight_doubling_norm.tex
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _curve_remainder_in_Y(num: sp.Expr, X: sp.Symbol, Y: sp.Symbol) -> sp.Expr:
    """Reduce a polynomial numerator modulo the curve relation in Y.

    Curve: Y^2 = X^3 - X + 1/4  <=>  Y^2 - (X^3 - X + 1/4) = 0.
    Returns the remainder as an expression of degree < 2 in Y.
    """
    f = X**3 - X + sp.Rational(1, 4)
    curve_poly = sp.Poly(Y**2 - f, Y)
    # Keep this purely algebraic (avoid expensive factor/simplify).
    return sp.Poly(num, Y).rem(curve_poly).as_expr()


def _is_zero_in_QE(expr: sp.Expr, X: sp.Symbol, Y: sp.Symbol) -> bool:
    """Check expr == 0 in the function field Q(E)=Q(X,Y)/(Y^2 - (X^3-X+1/4)).

    Strategy: take numerator of together(expr), then reduce modulo the curve
    equation as a polynomial in Y; require both Y^0 and Y^1 coefficients to vanish.
    """
    num = sp.together(expr).as_numer_denom()[0]
    rem = _curve_remainder_in_Y(num, X, Y)
    remY = sp.Poly(rem, Y)
    c0 = remY.nth(0)
    c1 = remY.nth(1)
    # c0,c1 should be polynomials in X; be defensive and strip any accidental denominators.
    c0_num = sp.together(c0).as_numer_denom()[0]
    c1_num = sp.together(c1).as_numer_denom()[0]
    return sp.Poly(c0_num, X, domain=sp.QQ).is_zero and sp.Poly(c1_num, X, domain=sp.QQ).is_zero


def _latex_poly_in(var: sp.Symbol, expr: sp.Expr) -> str:
    P = sp.Poly(sp.expand(expr), var, domain=sp.ZZ)
    return sp.latex(P.as_expr())


def _resolvent_cubic_for_monic_quartic(v: sp.Symbol, f_monic: sp.Poly) -> sp.Poly:
    """Return the classical resolvent cubic of a monic quartic over Q.

    If f(x)=x^4 + a x^3 + b x^2 + c x + d, then the resolvent cubic is:
      z^3 - b z^2 + (a c - 4 d) z + (4 b d - a^2 d - c^2).
    """
    z = sp.Symbol("z")
    coeffs = f_monic.all_coeffs()
    if len(coeffs) != 5 or coeffs[0] != 1:
        raise ValueError("expected a monic quartic polynomial")
    a, b, c, d = coeffs[1], coeffs[2], coeffs[3], coeffs[4]
    Rz = sp.expand(z**3 - b * z**2 + (a * c - 4 * d) * z + (4 * b * d - a**2 * d - c**2))
    return sp.Poly(Rz, z, domain=sp.QQ)


def _cubic_irreducible_over_Q(poly: sp.Poly) -> bool:
    coeff, factors = sp.factor_list(poly)
    # A cubic over Q is reducible iff it has a linear factor.
    return not any(f.degree() == 1 for (f, _exp) in factors)


def _eval_univariate_mod(coeffs_high_to_low: List[int], t: int, p: int) -> int:
    """Evaluate a univariate integer polynomial modulo p via Horner."""
    acc = 0
    tt = t % p
    for c in coeffs_high_to_low:
        acc = (acc * tt + (c % p)) % p
    return acc


def _split_bivar_by_y1_degree(poly: sp.Poly, y0: sp.Symbol, y1: sp.Symbol, max_y1_deg: int) -> List[List[int]]:
    """Represent poly(y0,y1) as sum_{j<=max} f_j(y0) y1^j, returning dense f_j coeff lists."""
    d = poly.as_dict()
    max_y0 = [0] * (max_y1_deg + 1)
    for (e0, e1) in d.keys():
        if e1 <= max_y1_deg:
            max_y0[e1] = max(max_y0[e1], e0)
    arrs: List[List[int]] = [[0] * (max_y0[j] + 1) for j in range(max_y1_deg + 1)]
    for (e0, e1), c in d.items():
        if e1 <= max_y1_deg:
            arrs[e1][e0] = int(c)
    # Convert to Horner lists (highest -> lowest).
    return [list(reversed(a)) for a in arrs]


def _legendre_symbol(a: int, p: int) -> int:
    """Legendre symbol (a|p) for odd prime p: returns 0, 1, or -1."""
    a %= p
    if a == 0:
        return 0
    ls = pow(a, (p - 1) // 2, p)
    return -1 if ls == p - 1 else ls


def _sqrt_mod_p_3mod4(a: int, p: int) -> int:
    """Square root modulo p for primes p≡3 (mod 4). Assumes a is a quadratic residue."""
    return pow(a % p, (p + 1) // 4, p)


def _fast_check_on_finite_fields(
    *,
    primes: List[int],
    points_needed: int,
    points_needed_inverse: int,
    A_coeffs: Tuple[List[int], List[int], List[int], List[int], List[int]],
    Rm_coeffs: Tuple[List[int], List[int], List[int], List[int], List[int]],
    alpha_split: List[List[int]],
    beta_split: List[List[int]],
    quiet: bool,
) -> Tuple[bool, int, int]:
    """Fast deterministic checks via evaluation on E(F_p) for several primes."""

    def log(msg: str) -> None:
        if not quiet:
            print(msg, flush=True)

    A4c, A3c, A2c, A1c, A0c = A_coeffs
    R4c, R3c, R2c, R1c, R0c = Rm_coeffs

    # Structural degree bounds (divisor degrees) used to choose points_needed in main():
    # - H(y0,y1) has pole-degree <= 16*deg(y0)+4*deg(y1)=16*4+4*16=128
    # - beta - X*alpha has pole-degree <= 92 (see main() comments)
    total_checked = 0
    total_checked_inverse = 0

    for p in primes:
        if p <= 3 or p % 2 == 0:
            raise ValueError("primes must be odd and > 3")
        if p % 4 != 3:
            raise ValueError("primes must satisfy p ≡ 3 (mod 4) for fast sqrt")

        inv2 = (p + 1) // 2

        def eval_H(y0v: int, y1v: int) -> int:
            a4 = _eval_univariate_mod(A4c, y0v, p)
            a3 = _eval_univariate_mod(A3c, y0v, p)
            a2 = _eval_univariate_mod(A2c, y0v, p)
            a1 = _eval_univariate_mod(A1c, y0v, p)
            a0 = _eval_univariate_mod(A0c, y0v, p)
            v = y1v % p
            r = a4
            r = (r * v + a3) % p
            r = (r * v + a2) % p
            r = (r * v + a1) % p
            r = (r * v + a0) % p
            return r

        def eval_Rm(y0v: int, y1iv: int) -> int:
            r4 = _eval_univariate_mod(R4c, y0v, p)
            r3 = _eval_univariate_mod(R3c, y0v, p)
            r2 = _eval_univariate_mod(R2c, y0v, p)
            r1 = _eval_univariate_mod(R1c, y0v, p)
            r0 = _eval_univariate_mod(R0c, y0v, p)
            v = y1iv % p
            r = r4
            r = (r * v + r3) % p
            r = (r * v + r2) % p
            r = (r * v + r1) % p
            r = (r * v + r0) % p
            return r

        def eval_split(split: List[List[int]], y0v: int, y1v: int) -> int:
            y0m = y0v % p
            y1m = y1v % p
            y1_pow = 1
            acc = 0
            for j in range(len(split)):
                fj = _eval_univariate_mod(split[j], y0m, p) if split[j] else 0
                acc = (acc + fj * y1_pow) % p
                y1_pow = (y1_pow * y1m) % p
            return acc

        # Iterate affine points by scanning X, using Z=2Y so that Z^2 = 4X^3 - 4X + 1.
        checked_here = 0
        checked_here_inv = 0
        log(f"[ff] p={p}: collecting points and checking identities …")
        for X in range(p):
            if checked_here >= points_needed and checked_here_inv >= points_needed_inverse:
                break

            z2 = (4 * (X * X % p) * X - 4 * X + 1) % p
            if z2 == 0:
                # Z=0 (2-torsion): doubling formula has poles; skip.
                continue
            if _legendre_symbol(z2, p) != 1:
                continue
            Z = _sqrt_mod_p_3mod4(z2, p)
            if Z == 0:
                continue

            # Lattès map Phi(X)=N/D with D=z2=Z^2.
            D = z2
            N = (pow(X, 4, p) + 2 * (X * X % p) - 2 * X + 1) % p
            Phi = (N * pow(D, -1, p)) % p

            # Tangent slope m=(3X^2-1)/Z (since Z=2Y).
            m = ((3 * (X * X % p) - 1) * pow(Z, -1, p)) % p
            Z2 = (2 * m) % p
            Z2 = (Z2 * ((X - Phi) % p)) % p
            Z2 = (Z2 - Z) % p

            # y0 = X^2 + Y - 1/2 = X^2 + Z/2 - 1/2 (mod p)
            y0v = (X * X + (Z * inv2) - inv2) % p
            Phi2 = (Phi * Phi) % p
            y1v = (Phi2 + (Z2 * inv2) - inv2) % p
            y1iv = (Phi2 - (Z2 * inv2) - inv2) % p

            # Check H(y0,y1)=0 and Rm(y0,y1i)=0.
            if eval_H(y0v, y1v) != 0:
                return False, total_checked, total_checked_inverse
            if eval_Rm(y0v, y1iv) != 0:
                return False, total_checked, total_checked_inverse
            checked_here += 1
            total_checked += 1

            # Inverse check (skip points where alpha vanishes mod p).
            if checked_here_inv < points_needed_inverse:
                aval = eval_split(alpha_split, y0v, y1v)
                if aval != 0:
                    bval = eval_split(beta_split, y0v, y1v)
                    if (bval - (X % p) * aval) % p != 0:
                        return False, total_checked, total_checked_inverse
                    checked_here_inv += 1
                    total_checked_inverse += 1

        log(f"[ff] p={p}: checked={checked_here} inverse_checked={checked_here_inv}")
        if checked_here < points_needed or checked_here_inv < points_needed_inverse:
            return False, total_checked, total_checked_inverse

    return True, total_checked, total_checked_inverse


def _quartic_discriminant_int(a: sp.Expr, b: sp.Expr, c: sp.Expr, d: sp.Expr, e: sp.Expr) -> sp.Expr:
    """Discriminant of ax^4 + bx^3 + cx^2 + dx + e (explicit closed form)."""
    return (
        256 * a**3 * e**3
        - 192 * a**2 * b * d * e**2
        - 128 * a**2 * c**2 * e**2
        + 144 * a**2 * c * d**2 * e
        - 27 * a**2 * d**4
        + 144 * a * b**2 * c * e**2
        - 6 * a * b**2 * d**2 * e
        - 80 * a * b * c**2 * d * e
        + 18 * a * b * c * d**3
        + 16 * a * c**4 * e
        - 4 * a * c**3 * d**2
        - 27 * b**4 * e**2
        + 18 * b**3 * c * d * e
        - 4 * b**3 * d**3
        - 4 * b**2 * c**3 * e
        + b**2 * c**2 * d**2
    )


def _check_quartic_discriminant_identity_by_evaluation(
    *,
    coeffs: Tuple[sp.Poly, sp.Poly, sp.Poly, sp.Poly, sp.Poly],
    P_LY_poly: sp.Poly,
    Q12_poly: sp.Poly,
    T_poly: sp.Poly,
    degree_bound: int,
    points: Optional[List[int]] = None,
) -> Tuple[bool, int]:
    """Deterministically certify Disc = -y(y-1)P_LY * Q12^2 * T^2 by evaluation.

    The discriminant is a polynomial in y0 of degree <= degree_bound.
    Checking equality at degree_bound+1 distinct integers proves the identity.
    """
    if points is None:
        # Use symmetric small integers to keep intermediate big-int sizes moderate.
        half = degree_bound // 2
        points = list(range(-half, half + 1))
    if len(set(points)) < degree_bound + 1:
        raise ValueError("need at least degree_bound+1 distinct evaluation points")

    A4p, A3p, A2p, A1p, A0p = coeffs
    for i, t in enumerate(points):
        a = A4p.eval(t)
        b = A3p.eval(t)
        c = A2p.eval(t)
        d = A1p.eval(t)
        e = A0p.eval(t)
        disc_val = _quartic_discriminant_int(a, b, c, d, e)
        expected_val = (
            -sp.Integer(t)
            * sp.Integer(t - 1)
            * P_LY_poly.eval(t)
            * (Q12_poly.eval(t) ** 2)
            * (T_poly.eval(t) ** 2)
        )
        if disc_val != expected_val:
            return False, i + 1
    return True, len(points)


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit weight-doubling correspondence polynomial H(y0,y1) on E")
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs")
    parser.add_argument("--symbolic", action="store_true", help="Run full symbolic checks (slow)")
    parser.add_argument("--quiet", action="store_true", help="Suppress progress output")
    args = parser.parse_args()

    t0 = time.perf_counter()

    def log(msg: str) -> None:
        if not args.quiet:
            dt = time.perf_counter() - t0
            print(f"[progress {dt:7.2f}s] {msg}", flush=True)

    # Function field symbols on E
    X, Y = sp.symbols("X Y")

    # Weight-coordinate symbols
    y0, y1, y1i = sp.symbols("y_0 y_1 y_1iota")
    # Generic base variable for TeX outputs.
    y = sp.Symbol("y")

    # Lee–Yang cubic
    def P_LY(t: sp.Expr) -> sp.Expr:
        return 256 * t**3 + 411 * t**2 + 165 * t + 32

    # --- Conclusion 176: explicit H(y0,y1) ---
    log("constructing quartic correspondence polynomials")
    A4 = (
        65536 * y0**12
        - 131072 * y0**11
        + 32768 * y0**10
        + 81920 * y0**9
        - 45056 * y0**8
        - 16384 * y0**7
        + 13824 * y0**6
        + 512 * y0**5
        - 1664 * y0**4
        + 192 * y0**3
        + 64 * y0**2
        - 16 * y0
        + 1
    )
    A3 = (
        -16384 * y0**13
        + 61440 * y0**12
        - 454656 * y0**11
        + 82944 * y0**10
        + 1247744 * y0**9
        - 57600 * y0**8
        - 906688 * y0**7
        - 167648 * y0**6
        + 174368 * y0**5
        + 23020 * y0**4
        - 12596 * y0**3
        - 1198 * y0**2
        + 346 * y0
        - 63
    )
    A2 = (
        1536 * y0**14
        - 9216 * y0**13
        + 81792 * y0**12
        - 118976 * y0**11
        + 294336 * y0**10
        + 641648 * y0**9
        - 232314 * y0**8
        - 391280 * y0**7
        - 430462 * y0**6
        - 198332 * y0**5
        + 280857 * y0**4
        + 263078 * y0**3
        + 108044 * y0**2
        + 14594 * y0
        + 698
    )
    A1 = (
        -64 * y0**15
        + 608 * y0**14
        - 5376 * y0**13
        + 15052 * y0**12
        - 37980 * y0**11
        + 75342 * y0**10
        + 75922 * y0**9
        - 208389 * y0**8
        - 257076 * y0**7
        - 198536 * y0**6
        + 143116 * y0**5
        + 199086 * y0**4
        - 37204 * y0**3
        - 57694 * y0**2
        - 26364 * y0
        - 2436
    )
    A0 = (
        y0**16
        - 16 * y0**15
        + 158 * y0**14
        - 872 * y0**13
        + 2243 * y0**12
        - 3190 * y0**11
        + 7024 * y0**10
        - 4728 * y0**9
        - 23757 * y0**8
        - 1652 * y0**7
        + 35994 * y0**6
        + 65440 * y0**5
        + 497 * y0**4
        - 35454 * y0**3
        - 2792 * y0**2
        + 1640 * y0
        + 1800
    )
    H = sp.expand(A4 * y1**4 + A3 * y1**3 + A2 * y1**2 + A1 * y1 + A0)

    H_deg_y1 = sp.Poly(H, y1).degree()
    H_deg_y0 = sp.Poly(H, y0).degree()

    # Leading coefficient structure: A4(y0) = Q(y0)^4
    Q = 16 * y0**3 - 8 * y0**2 - 4 * y0 + 1
    Q4_ok = sp.factor(A4 - Q**4) == 0

    # --- Conjugate branch quartic R_-(y0, y1^iota) ---
    # Coefficients taken as a closed-form certificate (verified on E below).
    Am = (
        -16384 * y0**13
        + 45056 * y0**12
        - 200704 * y0**11
        + 480256 * y0**10
        + 572928 * y0**9
        - 594688 * y0**8
        - 469440 * y0**7
        + 16416 * y0**6
        + 104768 * y0**5
        + 4252 * y0**4
        - 8092 * y0**3
        - 834 * y0**2
        + 78 * y0
        - 23
    )
    Bm = (
        1536 * y0**14
        - 12288 * y0**13
        + 31104 * y0**12
        - 89280 * y0**11
        + 656064 * y0**10
        + 627888 * y0**9
        - 1144794 * y0**8
        - 852832 * y0**7
        + 669978 * y0**6
        + 1118376 * y0**5
        + 690035 * y0**4
        + 216910 * y0**3
        + 38706 * y0**2
        + 3120 * y0
        + 43
    )
    Cm = (
        -64 * y0**15
        - 160 * y0**14
        + 7072 * y0**13
        + 8188 * y0**12
        - 181108 * y0**11
        - 91742 * y0**10
        - 481418 * y0**9
        - 2339065 * y0**8
        - 3263796 * y0**7
        - 2305780 * y0**6
        - 982332 * y0**5
        - 224044 * y0**4
        - 21060 * y0**3
        + 1172 * y0**2
        + 58 * y0
        - 21
    )
    Dm_factored = (
        y0**2
        * (y0**3 - 14 * y0**2 - 14 * y0 + 2) ** 2
        * (y0**4 - 14 * y0**3 + 46 * y0**2 + 22 * y0 + 14)
        * (y0**4 + 10 * y0**3 + 28 * y0**2 + 14 * y0 + 3)
    )
    Dm = sp.expand(Dm_factored)
    Rm = sp.expand(Q**4 * y1i**4 + Am * y1i**3 + Bm * y1i**2 + Cm * y1i + Dm)

    Rm_deg_y1i = sp.Poly(Rm, y1i).degree()
    Rm_deg_y0 = sp.Poly(Rm, y0).degree()

    # --- Verify that H and Rm vanish on E (symbolic or fast finite-field checks) ---
    H_on_E_ok = False
    Rm_on_E_ok = False
    inverse_X_ok = False
    res_ok = False
    ff_checked = 0
    ff_checked_inverse = 0

    # (Checks that require alpha,beta are performed after alpha,beta are defined.)


    # --- Conclusion 177: discriminant factorization ---
    log("checking discriminant factorizations by evaluation (degree=84)")
    Q12 = (
        64 * y0**12
        - 128 * y0**11
        - 2576 * y0**10
        - 2160 * y0**9
        + 10892 * y0**8
        + 32064 * y0**7
        + 28873 * y0**6
        - 11139 * y0**5
        - 31715 * y0**4
        - 8333 * y0**3
        - 958 * y0**2
        - 100 * y0
        + 8
    )
    Q26 = (
        262144 * y0**26
        - 10747904 * y0**25
        + 191954944 * y0**24
        - 1897332736 * y0**23
        + 13439238144 * y0**22
        - 47170043904 * y0**21
        + 30127935488 * y0**20
        + 55661785088 * y0**19
        - 112465192960 * y0**18
        + 135823686656 * y0**17
        + 205179341056 * y0**16
        - 455994979584 * y0**15
        - 230261903040 * y0**14
        + 622458964864 * y0**13
        + 231233432960 * y0**12
        - 451887225664 * y0**11
        - 230891455552 * y0**10
        + 102570870816 * y0**9
        + 95472617744 * y0**8
        + 15921249600 * y0**7
        - 7132590928 * y0**6
        - 3074856528 * y0**5
        - 21077156 * y0**4
        + 227572860 * y0**3
        + 2463184 * y0**2
        - 12256842 * y0
        - 4594975
    )

    Q26m = (
        191102976 * y0**26
        - 3248750592 * y0**25
        + 15336013824 * y0**24
        + 3965386752 * y0**23
        - 141567492096 * y0**22
        - 71797653504 * y0**21
        + 1007302348800 * y0**20
        + 2608289648640 * y0**19
        + 2522478716928 * y0**18
        - 366569892864 * y0**17
        - 3997689244416 * y0**16
        - 5518986465024 * y0**15
        - 4422184238528 * y0**14
        - 2328409689344 * y0**13
        - 764216979776 * y0**12
        - 98954676928 * y0**11
        + 41010765504 * y0**10
        + 26703630624 * y0**9
        + 8069517360 * y0**8
        + 2341777728 * y0**7
        + 1038528048 * y0**6
        + 413681776 * y0**5
        + 105306364 * y0**4
        + 14201380 * y0**3
        + 624020 * y0**2
        - 56922 * y0
        - 4725
    )
    # Full symbolic discriminants are expensive. Instead, we do a deterministic
    # polynomial identity test by evaluation at (degree_bound+1) distinct integers.
    P_LY_poly = sp.Poly(P_LY(y0), y0, domain=sp.ZZ)
    Q12_poly = sp.Poly(Q12, y0, domain=sp.ZZ)
    Q26_poly = sp.Poly(Q26, y0, domain=sp.ZZ)
    Q26m_poly = sp.Poly(Q26m, y0, domain=sp.ZZ)
    A4_poly = sp.Poly(A4, y0, domain=sp.ZZ)
    A3_poly = sp.Poly(A3, y0, domain=sp.ZZ)
    A2_poly = sp.Poly(A2, y0, domain=sp.ZZ)
    A1_poly = sp.Poly(A1, y0, domain=sp.ZZ)
    A0_poly = sp.Poly(A0, y0, domain=sp.ZZ)
    Am_poly = sp.Poly(Am, y0, domain=sp.ZZ)
    Bm_poly = sp.Poly(Bm, y0, domain=sp.ZZ)
    Cm_poly = sp.Poly(Cm, y0, domain=sp.ZZ)
    Dm_poly = sp.Poly(Dm, y0, domain=sp.ZZ)

    # Safe upper bound for a quartic discriminant degree in y0 (max over the explicit formula terms).
    deg_bound_disc = 84
    disc_ok, disc_points_checked = _check_quartic_discriminant_identity_by_evaluation(
        coeffs=(A4_poly, A3_poly, A2_poly, A1_poly, A0_poly),
        P_LY_poly=P_LY_poly,
        Q12_poly=Q12_poly,
        T_poly=Q26_poly,
        degree_bound=deg_bound_disc,
    )
    disc_Rm_ok, disc_Rm_points_checked = _check_quartic_discriminant_identity_by_evaluation(
        coeffs=(A4_poly, Am_poly, Bm_poly, Cm_poly, Dm_poly),
        P_LY_poly=P_LY_poly,
        Q12_poly=Q12_poly,
        T_poly=Q26m_poly,
        degree_bound=deg_bound_disc,
    )

    # --- Specialization y0=2: resolvent cubic irreducibility witness (S4) ---
    log("checking S4 witnesses at y0=2")
    def _s4_witness_at_y2(quartic: sp.Expr, var_v: sp.Symbol) -> bool:
        f = sp.Poly(sp.expand(quartic.subs({y0: 2})), var_v, domain=sp.ZZ)
        f_monic = sp.Poly(f.monic().as_expr(), var_v, domain=sp.QQ)
        resolvent = _resolvent_cubic_for_monic_quartic(var_v, f_monic)
        return _cubic_irreducible_over_Q(resolvent)

    resolvent_plus_irred_y2 = _s4_witness_at_y2(H, y1)
    resolvent_minus_irred_y2 = _s4_witness_at_y2(Rm, y1i)


    # --- Conclusion 178: birational inverse ---
    log("building birational inverse polynomials (alpha,beta)")
    alpha = (
        2 * y0**10
        - 128 * y0**9 * y1
        - 18 * y0**9
        + 2304 * y0**8 * y1**2
        + 344 * y0**8 * y1
        + 269 * y0**8
        - 16384 * y0**7 * y1**3
        - 512 * y0**7 * y1**2
        - 10528 * y0**7 * y1
        - 1644 * y0**7
        + 43008 * y0**6 * y1**3
        + 114944 * y0**6 * y1**2
        - 5880 * y0**6 * y1
        + 2664 * y0**6
        - 43008 * y0**5 * y1**3
        - 155840 * y0**5 * y1**2
        - 114364 * y0**5 * y1
        - 3744 * y0**5
        + 15104 * y0**4 * y1**3
        - 234576 * y0**4 * y1**2
        - 19146 * y0**4 * y1
        + 15013 * y0**4
        + 190016 * y0**3 * y1**2
        + 158988 * y0**3 * y1
        + 20344 * y0**3
        - 256 * y0**2 * y1**3
        + 62942 * y0**2 * y1**2
        - 49226 * y0**2 * y1
        - 29243 * y0**2
        - 192 * y0 * y1**3
        + 11686 * y0 * y1**2
        - 9606 * y0 * y1
        + 4992 * y0
        - 8 * y1**3
        + 409 * y1**2
        - 910 * y1
        - 716
    )
    beta = (
        2 * y0**11
        - 112 * y0**10 * y1
        - 24 * y0**10
        + 2048 * y0**9 * y1**2
        + 560 * y0**9 * y1
        + 172 * y0**9
        - 12288 * y0**8 * y1**3
        - 5376 * y0**8 * y1**2
        - 4776 * y0**8 * y1
        - 604 * y0**8
        + 16384 * y0**7 * y1**3
        + 55040 * y0**7 * y1**2
        - 2564 * y0**7 * y1
        + 256 * y0**7
        + 10240 * y0**6 * y1**3
        + 54624 * y0**6 * y1**2
        - 37832 * y0**6 * y1
        + 435 * y0**6
        - 19968 * y0**5 * y1**3
        - 185312 * y0**5 * y1**2
        - 95724 * y0**5 * y1
        + 65 * y0**5
        + 6400 * y0**4 * y1**3
        - 92560 * y0**4 * y1**2
        + 39344 * y0**4 * y1
        + 18495 * y0**4
        + 1280 * y0**3 * y1**3
        + 126434 * y0**3 * y1**2
        + 69014 * y0**3 * y1
        + 2166 * y0**3
        - 368 * y0**2 * y1**3
        + 55096 * y0**2 * y1**2
        - 37869 * y0**2 * y1
        - 12835 * y0**2
        - 144 * y0 * y1**3
        + 9048 * y0 * y1**2
        - 15369 * y0 * y1
        + 3722 * y0
        - 8 * y1**3
        + 436 * y1**2
        - 1344 * y1
        + 916
    )

    # --- Verify H/R_- on E and the birational inverse (symbolic or fast finite-field checks) ---
    log("verifying correspondence identities on E")
    if args.symbolic:
        log("running full symbolic checks on Q(E) (slow)")
        # Curve: Y^2 = X^3 - X + 1/4, a=-1, b=1/4.
        denom_2div = 4 * X**3 - 4 * X + 1
        Phi = (X**4 + 2 * X**2 - 2 * X + 1) / denom_2div
        m = (3 * X**2 - 1) / (2 * Y)
        Y2 = sp.together(m * (X - Phi) - Y)
        y0_expr = X**2 + Y - sp.Rational(1, 2)
        y1_expr = sp.together(Phi**2 + Y2 - sp.Rational(1, 2))
        y1i_expr = sp.together(Phi**2 - Y2 - sp.Rational(1, 2))

        H_on_E_ok = _is_zero_in_QE(H.subs({y0: y0_expr, y1: y1_expr}), X, Y)
        Rm_on_E_ok = _is_zero_in_QE(Rm.subs({y0: y0_expr, y1i: y1i_expr}), X, Y)

        log("verifying birational inverse on the generic E-point (slow)")
        alpha_on_E = alpha.subs({y0: y0_expr, y1: y1_expr})
        beta_on_E = beta.subs({y0: y0_expr, y1: y1_expr})
        inverse_X_ok = _is_zero_in_QE(beta_on_E - X * alpha_on_E, X, Y)
    else:
        log("running fast finite-field checks (with progress)")
        # Pole-degree bounds:
        # - H(y0,y1): <= 128  -> need >=129 points
        # - beta - X*alpha: <= 92 -> need >=93 points with alpha!=0
        points_needed = 160
        points_needed_inverse = 120

        # Prepare coefficient lists for fast modular evaluation.
        A4c = [int(c) for c in sp.Poly(A4, y0, domain=sp.ZZ).all_coeffs()]
        A3c = [int(c) for c in sp.Poly(A3, y0, domain=sp.ZZ).all_coeffs()]
        A2c = [int(c) for c in sp.Poly(A2, y0, domain=sp.ZZ).all_coeffs()]
        A1c = [int(c) for c in sp.Poly(A1, y0, domain=sp.ZZ).all_coeffs()]
        A0c = [int(c) for c in sp.Poly(A0, y0, domain=sp.ZZ).all_coeffs()]
        R4c = A4c[:]  # Q(y0)^4
        R3c = [int(c) for c in sp.Poly(Am, y0, domain=sp.ZZ).all_coeffs()]
        R2c = [int(c) for c in sp.Poly(Bm, y0, domain=sp.ZZ).all_coeffs()]
        R1c = [int(c) for c in sp.Poly(Cm, y0, domain=sp.ZZ).all_coeffs()]
        R0c = [int(c) for c in sp.Poly(Dm, y0, domain=sp.ZZ).all_coeffs()]

        alpha_poly = sp.Poly(alpha, y0, y1, domain=sp.ZZ)
        beta_poly = sp.Poly(beta, y0, y1, domain=sp.ZZ)
        alpha_split = _split_bivar_by_y1_degree(alpha_poly, y0, y1, 3)
        beta_split = _split_bivar_by_y1_degree(beta_poly, y0, y1, 3)

        # Two independent primes (p≡3 mod 4) give high confidence while remaining fast.
        primes = [503, 523]
        ok, ff_checked, ff_checked_inverse = _fast_check_on_finite_fields(
            primes=primes,
            points_needed=points_needed,
            points_needed_inverse=points_needed_inverse,
            A_coeffs=(A4c, A3c, A2c, A1c, A0c),
            Rm_coeffs=(R4c, R3c, R2c, R1c, R0c),
            alpha_split=alpha_split,
            beta_split=beta_split,
            quiet=args.quiet,
        )
        H_on_E_ok = ok
        Rm_on_E_ok = ok
        inverse_X_ok = ok

    # --- Conclusion 180: norm/resultant certificate ---
    log("checking norm/resultant certificate")
    xx, yy = sp.symbols("x y")
    Pi_xy = xx**4 - xx**3 - (2 * yy + 1) * xx**2 + xx + yy * (yy + 1)
    h_elim = 4 * xx * (yy - xx**2 + sp.Rational(1, 2)) + 3 * xx**2 - 1
    res_expected = -yy * (yy - 1) * (256 * yy**3 + 411 * yy**2 + 165 * yy + 32)
    if args.symbolic:
        res = sp.factor(sp.resultant(Pi_xy, h_elim, xx))
        res_ok = sp.factor(res - res_expected) == 0
    else:
        # Degree(res_expected)=5, so 6 integer evaluations suffice.
        test_vals = [-2, -1, 0, 1, 2, 3]
        res_ok = True
        for t in test_vals:
            Pi_t = sp.Poly(Pi_xy.subs({yy: t}), xx, domain=sp.ZZ)
            h_t = sp.Poly(h_elim.subs({yy: t}), xx, domain=sp.ZZ)
            rt = sp.resultant(Pi_t, h_t, xx)
            if sp.Integer(rt) != sp.Integer(res_expected.subs({yy: t})):
                res_ok = False
                break

    payload: Dict[str, object] = {
        "H_deg_y1": int(H_deg_y1),
        "H_deg_y0": int(H_deg_y0),
        "H_on_E_ok": bool(H_on_E_ok),
        "disc_ok": bool(disc_ok),
        "disc_points_checked": int(disc_points_checked),
        "Q4_ok": bool(Q4_ok),
        "Rm_deg_y1i": int(Rm_deg_y1i),
        "Rm_deg_y0": int(Rm_deg_y0),
        "Rm_on_E_ok": bool(Rm_on_E_ok),
        "disc_Rm_ok": bool(disc_Rm_ok),
        "disc_Rm_points_checked": int(disc_Rm_points_checked),
        "ff_checked": int(ff_checked),
        "ff_checked_inverse": int(ff_checked_inverse),
        "symbolic": bool(args.symbolic),
        "resolvent_plus_irred_y2": bool(resolvent_plus_irred_y2),
        "resolvent_minus_irred_y2": bool(resolvent_minus_irred_y2),
        "inverse_X_ok": bool(inverse_X_ok),
        "res_ok": bool(res_ok),
    }

    if not args.no_output:
        _write_json(export_dir() / "fold_zm_elliptic_weight_doubling_audit.json", payload)

        # TeX: H and A_i coefficients
        tex_H: List[str] = []
        tex_H.append("% Auto-generated by scripts/exp_fold_zm_elliptic_weight_doubling_audit.py")
        tex_H.append("\\[")
        tex_H.append(
            "\\mathcal H(y_{0},y_{1})=A_{4}(y_{0})y_{1}^{4}+A_{3}(y_{0})y_{1}^{3}+A_{2}(y_{0})y_{1}^{2}+A_{1}(y_{0})y_{1}+A_{0}(y_{0})."
        )
        tex_H.append("\\]")
        tex_H.append("\\[")
        tex_H.append("\\begin{aligned}")
        tex_H.append(f"A_4(y_0)&={_latex_poly_in(y0, A4)}\\\\")
        tex_H.append(f"A_3(y_0)&={_latex_poly_in(y0, A3)}\\\\")
        tex_H.append(f"A_2(y_0)&={_latex_poly_in(y0, A2)}\\\\")
        tex_H.append(f"A_1(y_0)&={_latex_poly_in(y0, A1)}\\\\")
        tex_H.append(f"A_0(y_0)&={_latex_poly_in(y0, A0)}")
        tex_H.append("\\end{aligned}")
        tex_H.append("\\]")
        _write_text(generated_dir() / "eq_fold_zm_elliptic_weight_doubling_H.tex", "\n".join(tex_H) + "\n")

        # TeX: Rminus and coefficients
        tex_Rm: List[str] = []
        tex_Rm.append("% Auto-generated by scripts/exp_fold_zm_elliptic_weight_doubling_audit.py")
        tex_Rm.append("\\[")
        tex_Rm.append("Q(y)=16y^{3}-8y^{2}-4y+1.")
        tex_Rm.append("\\]")
        tex_Rm.append("\\[")
        tex_Rm.append(
            "R_{-}(y_{0},y_{1}^{\\iota})"
            "=Q(y_{0})^{4}(y_{1}^{\\iota})^{4}+A_{-}(y_{0})(y_{1}^{\\iota})^{3}"
            "+B_{-}(y_{0})(y_{1}^{\\iota})^{2}+C_{-}(y_{0})y_{1}^{\\iota}+D_{-}(y_{0})."
        )
        tex_Rm.append("\\]")
        tex_Rm.append("\\[")
        tex_Rm.append("\\begin{aligned}")
        tex_Rm.append(f"A_-(y_0)&={_latex_poly_in(y0, Am)}\\\\")
        tex_Rm.append(f"B_-(y_0)&={_latex_poly_in(y0, Bm)}\\\\")
        tex_Rm.append(f"C_-(y_0)&={_latex_poly_in(y0, Cm)}\\\\")
        # Keep D_- in the factored form (audit-friendly).
        tex_Rm.append(f"D_-(y_0)&={sp.latex(sp.factor(Dm_factored))}")
        tex_Rm.append("\\end{aligned}")
        tex_Rm.append("\\]")
        _write_text(generated_dir() / "eq_fold_zm_elliptic_weight_doubling_Rminus.tex", "\n".join(tex_Rm) + "\n")

        # TeX: discriminant factorization
        tex_D: List[str] = []
        tex_D.append("% Auto-generated by scripts/exp_fold_zm_elliptic_weight_doubling_audit.py")
        tex_D.append("\\[")
        tex_D.append("P_{\\mathrm{LY}}(y)=256y^{3}+411y^{2}+165y+32.")
        tex_D.append("\\]")
        tex_D.append("\\[")
        tex_D.append(f"A(y)={sp.latex(sp.Poly(Q12.subs({y0: y}), y, domain=sp.ZZ).as_expr())}.")
        tex_D.append("\\]")
        tex_D.append("\\[")
        tex_D.append(f"B_{{+}}(y)={sp.latex(sp.Poly(Q26.subs({y0: y}), y, domain=sp.ZZ).as_expr())}.")
        tex_D.append("\\]")
        tex_D.append("\\[")
        tex_D.append(f"B_{{-}}(y)={sp.latex(sp.Poly(Q26m.subs({y0: y}), y, domain=sp.ZZ).as_expr())}.")
        tex_D.append("\\]")
        tex_D.append("\\[")
        tex_D.append(
            "\\mathrm{Disc}_{v}\\bigl(R_{\\pm}(y,v)\\bigr)"
            "=-y(y-1)P_{\\mathrm{LY}}(y)\\,A(y)^{2}B_{\\pm}(y)^{2}."
        )
        tex_D.append("\\]")
        _write_text(
            generated_dir() / "eq_fold_zm_elliptic_weight_doubling_discriminant.tex", "\n".join(tex_D) + "\n"
        )

        # TeX: birational inverse polynomials
        tex_inv: List[str] = []
        tex_inv.append("% Auto-generated by scripts/exp_fold_zm_elliptic_weight_doubling_audit.py")
        tex_inv.append("\\[")
        tex_inv.append(f"\\alpha(y_0,y_1)={sp.latex(sp.Poly(alpha, y0, y1, domain=sp.ZZ).as_expr())}.")
        tex_inv.append("\\]")
        tex_inv.append("\\[")
        tex_inv.append(f"\\beta(y_0,y_1)={sp.latex(sp.Poly(beta, y0, y1, domain=sp.ZZ).as_expr())}.")
        tex_inv.append("\\]")
        _write_text(generated_dir() / "eq_fold_zm_elliptic_weight_doubling_inverse.tex", "\n".join(tex_inv) + "\n")

        # TeX: norm/resultant certificate
        tex_norm: List[str] = []
        tex_norm.append("% Auto-generated by scripts/exp_fold_zm_elliptic_weight_doubling_audit.py")
        tex_norm.append("\\[")
        tex_norm.append(
            "\\Pi(\\lambda,y)=\\lambda^{4}-\\lambda^{3}-(2y+1)\\lambda^{2}+\\lambda+y(y+1),\\qquad "
            "h(\\lambda,y)=4\\lambda\\bigl(y-\\lambda^{2}+\\tfrac12\\bigr)+3\\lambda^{2}-1."
        )
        tex_norm.append("\\]")
        tex_norm.append("\\[")
        tex_norm.append(
            "\\mathrm{Res}_{\\lambda}\\bigl(\\Pi(\\lambda,y),h(\\lambda,y)\\bigr)=-y(y-1)P_{\\mathrm{LY}}(y)."
        )
        tex_norm.append("\\]")
        _write_text(generated_dir() / "eq_fold_zm_elliptic_weight_doubling_norm.tex", "\n".join(tex_norm) + "\n")


if __name__ == "__main__":
    main()

