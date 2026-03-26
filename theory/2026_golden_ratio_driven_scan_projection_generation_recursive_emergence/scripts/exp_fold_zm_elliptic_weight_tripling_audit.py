#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the weight-tripling correspondence on E in (y, y∘[3])-coordinates.

This script is English-only by repository convention.

We work with the elliptic curve
  E: Y^2 = X^3 - X + 1/4
and the weight coordinate
  y := X^2 + Y - 1/2.

For P in E, define y0 := y(P) and y3 := y([3]P). Since y : E -> P^1 has degree 4,
the map P ↦ y([3]P) does not descend to a single-valued rational function of y(P);
instead, (y0,y3) lies on an explicit plane curve M3(y0,y3)=0, quartic in y3.

We certify:
  - An explicit primitive integer polynomial M3(y0,y3) with bidegree (36,4).
  - A finite-field audit that M3(y(P), y([3]P))=0 on many points (enough for the
    pole-degree bound of the function on E).
  - A discriminant square-class factorization:
      Disc_{y3}(M3(y,y3)) = -y(y-1) P_LY(y) * A32(y)^2 * B66(y)^2
    and we output explicit A32,B66 in Z[y] (computed from the exact discriminant).

Outputs (default):
  - artifacts/export/fold_zm_elliptic_weight_tripling_audit.json
  - sections/generated/eq_fold_zm_elliptic_weight_tripling_M3.tex
  - sections/generated/eq_fold_zm_elliptic_weight_tripling_discriminant.tex
"""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _eval_univariate_mod(coeffs_high_to_low: List[int], t: int, p: int) -> int:
    """Evaluate a univariate integer polynomial modulo p via Horner."""
    acc = 0
    tt = t % p
    for c in coeffs_high_to_low:
        acc = (acc * tt + (c % p)) % p
    return acc


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


def _poly_sqrt_exact_in_ZZ(f: sp.Poly, var: sp.Symbol) -> sp.Poly:
    """Return g in ZZ[var] such that g^2 = f, assuming f is a perfect square in ZZ[var]."""
    if f.domain != sp.ZZ:
        raise ValueError("expected a polynomial over ZZ")
    deg = f.degree()
    if deg < 0:
        return sp.Poly(0, var, domain=sp.ZZ)
    if deg % 2 != 0:
        raise ValueError("polynomial degree is odd; cannot be a square in ZZ[var]")
    n = deg // 2

    # Coefficients a_k of var^k.
    a = [sp.Integer(f.nth(k)) for k in range(deg + 1)]
    lc = int(a[deg])
    if lc < 0:
        raise ValueError("negative leading coefficient; not a square in ZZ[var]")
    r = int(math.isqrt(lc))
    if r * r != lc:
        raise ValueError("leading coefficient is not a perfect square")

    b = [sp.Integer(0) for _ in range(n + 1)]
    b[n] = sp.Integer(r)
    two_bn = 2 * b[n]
    if two_bn == 0:
        raise ValueError("zero leading coefficient after sqrt")

    # Solve b[n-1],...,b[0] from top degrees downward.
    for k in range(1, n + 1):
        # Target degree: deg - k = 2n - k
        target = sp.Integer(a[deg - k])
        s = sp.Integer(0)
        for i in range(1, k):
            s += b[n - i] * b[n - (k - i)]
        bk = (target - s) / two_bn
        if bk.q != 1:
            raise ValueError("non-integral coefficient encountered in polynomial square root")
        b[n - k] = sp.Integer(bk.p)

    g = sp.Poly(sum(b[i] * var**i for i in range(n + 1)), var, domain=sp.ZZ)
    if sp.Poly(g.as_expr() ** 2 - f.as_expr(), var, domain=sp.ZZ).is_zero is not True:
        raise ValueError("polynomial square root verification failed")
    return g


def _fast_check_on_finite_fields(
    *,
    primes: List[int],
    points_needed: int,
    d4c: List[int],
    d3c: List[int],
    d2c: List[int],
    d1c: List[int],
    d0c: List[int],
    quiet: bool,
) -> Tuple[bool, int]:
    """Deterministic checks via evaluation on E(F_p) for several primes."""

    def log(msg: str) -> None:
        if not quiet:
            print(msg, flush=True)

    total_checked = 0
    for p in primes:
        if p <= 3 or p % 2 == 0:
            raise ValueError("primes must be odd and > 3")
        if p % 4 != 3:
            raise ValueError("primes must satisfy p ≡ 3 (mod 4) for fast sqrt")

        inv2 = (p + 1) // 2

        def eval_M3(y0v: int, y3v: int) -> int:
            a4 = _eval_univariate_mod(d4c, y0v, p)
            a3 = _eval_univariate_mod(d3c, y0v, p)
            a2 = _eval_univariate_mod(d2c, y0v, p)
            a1 = _eval_univariate_mod(d1c, y0v, p)
            a0 = _eval_univariate_mod(d0c, y0v, p)
            v = y3v % p
            r = a4
            r = (r * v + a3) % p
            r = (r * v + a2) % p
            r = (r * v + a1) % p
            r = (r * v + a0) % p
            return r

        checked_here = 0
        log(f"[ff] p={p}: collecting points and checking M3(y,y3)=0 …")

        for X in range(p):
            if checked_here >= points_needed:
                break

            # Work with Z=2Y so that Z^2 = 4X^3 - 4X + 1.
            z2 = (4 * (X * X % p) * X - 4 * X + 1) % p
            if z2 == 0:
                # 2-torsion (Z=0): skip to avoid division by Z in doubling.
                continue
            if _legendre_symbol(z2, p) != 1:
                continue
            Z = _sqrt_mod_p_3mod4(z2, p)
            if Z == 0:
                continue

            Y = (Z * inv2) % p

            # --- Doubling: Q=[2]P ---
            D = z2
            N = (pow(X, 4, p) + 2 * (X * X % p) - 2 * X + 1) % p
            X2 = (N * pow(D, -1, p)) % p

            m = ((3 * (X * X % p) - 1) * pow(Z, -1, p)) % p  # slope using Z=2Y
            Z2 = (2 * m) % p
            Z2 = (Z2 * ((X - X2) % p)) % p
            Z2 = (Z2 - Z) % p
            Y2 = (Z2 * inv2) % p

            # --- Addition: [3]P = P + [2]P ---
            dx = (X2 - X) % p
            if dx == 0:
                # P and [2]P share x; addition degenerates (P+[2]P is O or undefined in this chart).
                continue
            s = ((Y2 - Y) * pow(dx, -1, p)) % p
            X3 = (s * s - X - X2) % p
            Y3 = (s * ((X - X3) % p) - Y) % p

            # Weight coordinates.
            y0v = (X * X + (Z * inv2) - inv2) % p
            y3v = (X3 * X3 + Y3 - inv2) % p

            if eval_M3(y0v, y3v) != 0:
                return False, total_checked + checked_here

            checked_here += 1

        log(f"[ff] p={p}: checked={checked_here}")
        if checked_here < points_needed:
            return False, total_checked + checked_here
        total_checked += checked_here

    return True, total_checked


def _latex_poly_in(var: sp.Symbol, expr: sp.Expr) -> str:
    return sp.latex(sp.Poly(sp.expand(expr), var, domain=sp.ZZ).as_expr())


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit weight-tripling correspondence polynomial M3(y,y3) on E")
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs")
    parser.add_argument("--quiet", action="store_true", help="Suppress progress output")
    args = parser.parse_args()

    t0 = time.perf_counter()

    def log(msg: str) -> None:
        if not args.quiet:
            dt = time.perf_counter() - t0
            print(f"[progress {dt:7.2f}s] {msg}", flush=True)

    y0, y3 = sp.symbols("y_0 y_3")
    y = sp.Symbol("y")

    def P_LY(t: sp.Expr) -> sp.Expr:
        return 256 * t**3 + 411 * t**2 + 165 * t + 32

    # --- Certificate: M3(y0,y3) coefficients (as provided by elimination) ---
    log("constructing M3(y0,y3) certificate polynomial")
    d4 = (
        43046721 * y0**32
        - 688747536 * y0**31
        + 4763837124 * y0**30
        - 17046501516 * y0**29
        + 25741939158 * y0**28
        + 25789768848 * y0**27
        - 143109621126 * y0**26
        + 28353440232 * y0**25
        + 561153334869 * y0**24
        - 506592944604 * y0**23
        - 1410924836664 * y0**22
        + 1650903751800 * y0**21
        + 3251944933677 * y0**20
        - 3395499607116 * y0**19
        - 6495595687350 * y0**18
        + 3458169019404 * y0**17
        + 10470161005704 * y0**16
        + 1134354515940 * y0**15
        - 9612753683076 * y0**14
        - 7549195530096 * y0**13
        + 834177731067 * y0**12
        + 4924759007196 * y0**11
        + 4128797833398 * y0**10
        + 1959470248968 * y0**9
        + 614975112216 * y0**8
        + 122411459952 * y0**7
        + 13273878834 * y0**6
        - 282098052 * y0**5
        - 207375552 * y0**4
        - 16429140 * y0**3
        + 3575040 * y0**2
        - 164640 * y0
        + 2401
    )
    d3 = (
        -2125764 * y0**33
        + 52081218 * y0**32
        - 1702736964 * y0**31
        + 9810046566 * y0**30
        + 12732617772 * y0**29
        - 88461602145 * y0**28
        - 407787473250 * y0**27
        + 1061139208131 * y0**26
        + 2868672814074 * y0**25
        - 4785194878299 * y0**24
        - 11967861707100 * y0**23
        + 8282586721374 * y0**22
        + 30289111051491 * y0**21
        + 6857001780003 * y0**20
        - 48386465669457 * y0**19
        - 44531190093573 * y0**18
        + 35490043695519 * y0**17
        + 50283370211652 * y0**16
        - 32378237573238 * y0**15
        - 84156214294170 * y0**14
        - 60675678557163 * y0**13
        - 22032531968328 * y0**12
        - 8605488604401 * y0**11
        - 10499945499711 * y0**10
        - 12539901916534 * y0**9
        - 9625979844114 * y0**8
        - 4974249836532 * y0**7
        - 1797287591691 * y0**6
        - 462189941901 * y0**5
        - 84327005418 * y0**4
        - 10551198930 * y0**3
        - 818192577 * y0**2
        - 26576322 * y0
        - 98197
    )
    d2 = (
        39366 * y0**34
        - 1377810 * y0**33
        + 54561276 * y0**32
        - 564853986 * y0**31
        + 9626058630 * y0**30
        - 4289933907 * y0**29
        - 109161940599 * y0**28
        + 62050973643 * y0**27
        + 57821843925 * y0**26
        - 3297574421325 * y0**25
        + 2418240987324 * y0**24
        + 36401102596350 * y0**23
        + 36747944757999 * y0**22
        - 70383879427176 * y0**21
        - 193701104567559 * y0**20
        - 190004477356782 * y0**19
        + 29650272890496 * y0**18
        + 282956173062417 * y0**17
        + 233575974525600 * y0**16
        + 45186198866760 * y0**15
        + 36354920545362 * y0**14
        + 146585872287126 * y0**13
        + 213625813875141 * y0**12
        + 194575513669101 * y0**11
        + 122351361302301 * y0**10
        + 46583661416760 * y0**9
        + 4487606594244 * y0**8
        - 5581980204120 * y0**7
        - 3510987787557 * y0**6
        - 1071553266270 * y0**5
        - 196030960545 * y0**4
        - 21569299227 * y0**3
        - 1311173031 * y0**2
        - 30288324 * y0
        + 947751
    )
    d1 = (
        -324 * y0**35
        + 17334 * y0**34
        - 662148 * y0**33
        + 8929440 * y0**32
        - 172305036 * y0**31
        + 2261471967 * y0**30
        - 9883436676 * y0**29
        - 59470643706 * y0**28
        - 182289492982 * y0**27
        - 649590915456 * y0**26
        + 1055029871502 * y0**25
        + 4757052390939 * y0**24
        - 22942304659899 * y0**23
        - 93374941075107 * y0**22
        - 73379379713508 * y0**21
        + 117949817336913 * y0**20
        + 334382323253742 * y0**19
        + 448475351639219 * y0**18
        + 271850923401234 * y0**17
        - 218040559140777 * y0**16
        - 562300479311091 * y0**15
        - 569600254578741 * y0**14
        - 422414210740071 * y0**13
        - 195335632166301 * y0**12
        + 26935167033564 * y0**11
        + 118558095741312 * y0**10
        + 86833391066048 * y0**9
        + 31529940175209 * y0**8
        + 4576425994068 * y0**7
        - 931056595806 * y0**6
        - 591825856566 * y0**5
        - 125402926878 * y0**4
        - 12887142075 * y0**3
        - 478800873 * y0**2
        + 10708749 * y0
        + 1166445
    )
    d0 = (
        y0**36
        - 102 * y0**35
        + 4944 * y0**34
        - 132564 * y0**33
        + 1570443 * y0**32
        - 6481971 * y0**31
        + 187167333 * y0**30
        - 2298038718 * y0**29
        - 6358883775 * y0**28
        + 32283444508 * y0**27
        + 480012765867 * y0**26
        + 2391319625175 * y0**25
        + 4251599618373 * y0**24
        + 2568390944292 * y0**23
        + 11463204085224 * y0**22
        + 40025368143837 * y0**21
        + 45223861421178 * y0**20
        + 36530288588673 * y0**19
        + 76989708803188 * y0**18
        + 106380019860591 * y0**17
        + 109090574770452 * y0**16
        + 123354348411657 * y0**15
        + 26373145412910 * y0**14
        - 156402666048255 * y0**13
        - 206626660879476 * y0**12
        - 106893909733596 * y0**11
        - 8480879564646 * y0**10
        + 20890571702625 * y0**9
        + 13471182501174 * y0**8
        + 4189935324465 * y0**7
        + 693617327892 * y0**6
        + 32444001063 * y0**5
        - 9654939045 * y0**4
        - 1741765761 * y0**3
        - 21968496 * y0**2
        + 13997340 * y0
    )

    M3 = sp.expand(d4 * y3**4 + d3 * y3**3 + d2 * y3**2 + d1 * y3 + d0)
    M3_poly = sp.Poly(M3, y0, y3, domain=sp.ZZ)
    deg_y3 = M3_poly.degree(y3)
    deg_y0 = M3_poly.degree(y0)

    # Pole-degree bound on E: y has pole order 4 at O; y∘[3] has pole order 36.
    pole_deg_bound = max(4 * sp.Poly(d4, y0).degree() + 36 * 4, 4 * sp.Poly(d0, y0).degree())

    log("running finite-field audits (deterministic point-count bound)")
    points_needed = int(pole_deg_bound) + 32  # safety buffer
    primes = [2003, 2011]

    d4c = [int(c) for c in sp.Poly(d4, y0, domain=sp.ZZ).all_coeffs()]
    d3c = [int(c) for c in sp.Poly(d3, y0, domain=sp.ZZ).all_coeffs()]
    d2c = [int(c) for c in sp.Poly(d2, y0, domain=sp.ZZ).all_coeffs()]
    d1c = [int(c) for c in sp.Poly(d1, y0, domain=sp.ZZ).all_coeffs()]
    d0c = [int(c) for c in sp.Poly(d0, y0, domain=sp.ZZ).all_coeffs()]

    ff_ok, ff_checked = _fast_check_on_finite_fields(
        primes=primes,
        points_needed=points_needed,
        d4c=d4c,
        d3c=d3c,
        d2c=d2c,
        d1c=d1c,
        d0c=d0c,
        quiet=args.quiet,
    )

    # --- Discriminant factorization: Disc_{y3}(M3) = -y(y-1)P_LY(y) * square ---
    log("computing quartic discriminant and extracting square factors")
    disc_expr = _quartic_discriminant_int(d4, d3, d2, d1, d0)
    disc_poly = sp.Poly(sp.expand(disc_expr), y0, domain=sp.ZZ)
    kernel_poly = sp.Poly(-y0 * (y0 - 1) * P_LY(y0), y0, domain=sp.ZZ)
    q_poly = disc_poly.exquo(kernel_poly)

    # q_poly should be a perfect square in ZZ[y0].
    sqrt_q_poly = _poly_sqrt_exact_in_ZZ(q_poly, y0)

    # Try to split sqrt_q_poly into degrees (32,66) (optional; not required for correctness).
    coeff_S, factors_S = sp.factor_list(sqrt_q_poly)
    A32_poly = None
    B66_poly = None
    if coeff_S in {1, -1}:
        degs = sorted([(int(f.degree()), f) for (f, exp) in factors_S for _ in range(exp)], key=lambda t: t[0])
        if len(degs) == 2 and {degs[0][0], degs[1][0]} == {32, 66}:
            A32_poly = degs[0][1] if degs[0][0] == 32 else degs[1][1]
            B66_poly = degs[0][1] if degs[0][0] == 66 else degs[1][1]

    payload: Dict[str, object] = {
        "M3_deg_y3": int(deg_y3),
        "M3_deg_y": int(deg_y0),
        "pole_degree_bound": int(pole_deg_bound),
        "finite_field_ok": bool(ff_ok),
        "finite_field_points_needed": int(points_needed),
        "finite_field_points_checked_total": int(ff_checked),
        "disc_deg_y": int(disc_poly.degree()),
        "kernel_deg_y": int(kernel_poly.degree()),
        "q_deg_y": int(q_poly.degree()),
        "sqrt_q_deg_y": int(sqrt_q_poly.degree()),
        "sqrt_split_deg_32_66": bool(A32_poly is not None and B66_poly is not None),
    }

    if not args.no_output:
        _write_json(export_dir() / "fold_zm_elliptic_weight_tripling_audit.json", payload)

        # TeX: M3 and coefficients
        tex_M3: List[str] = []
        tex_M3.append("% Auto-generated by scripts/exp_fold_zm_elliptic_weight_tripling_audit.py")
        tex_M3.append("\\[")
        tex_M3.append("M_{3}(y,y_{3})=d_{4}(y)y_{3}^{4}+d_{3}(y)y_{3}^{3}+d_{2}(y)y_{3}^{2}+d_{1}(y)y_{3}+d_{0}(y).")
        tex_M3.append("\\]")
        tex_M3.append("\\[")
        tex_M3.append("\\begin{aligned}")
        tex_M3.append(f"d_4(y)&={_latex_poly_in(y, d4.subs({y0: y}))}\\\\")
        tex_M3.append(f"d_3(y)&={_latex_poly_in(y, d3.subs({y0: y}))}\\\\")
        tex_M3.append(f"d_2(y)&={_latex_poly_in(y, d2.subs({y0: y}))}\\\\")
        tex_M3.append(f"d_1(y)&={_latex_poly_in(y, d1.subs({y0: y}))}\\\\")
        tex_M3.append(f"d_0(y)&={_latex_poly_in(y, d0.subs({y0: y}))}")
        tex_M3.append("\\end{aligned}")
        tex_M3.append("\\]")
        _write_text(generated_dir() / "eq_fold_zm_elliptic_weight_tripling_M3.tex", "\n".join(tex_M3) + "\n")

        # TeX: discriminant factorization
        tex_D: List[str] = []
        tex_D.append("% Auto-generated by scripts/exp_fold_zm_elliptic_weight_tripling_audit.py")
        tex_D.append("\\[")
        tex_D.append("P_{\\mathrm{LY}}(y)=256y^{3}+411y^{2}+165y+32.")
        tex_D.append("\\]")
        tex_D.append("\\[")
        tex_D.append("T(y)=16y^{3}-8y^{2}-4y+1.")
        tex_D.append("\\]")
        if A32_poly is not None and B66_poly is not None:
            tex_D.append("\\[")
            tex_D.append(f"A_{{32}}(y)={sp.latex(A32_poly.as_expr().subs({y0: y}))}.")
            tex_D.append("\\]")
            tex_D.append("\\[")
            tex_D.append(f"B_{{66}}(y)={sp.latex(B66_poly.as_expr().subs({y0: y}))}.")
            tex_D.append("\\]")
            tex_D.append("\\[")
            tex_D.append(
                "\\mathrm{Disc}_{y_{3}}\\bigl(M_{3}(y,y_{3})\\bigr)"
                "=-y(y-1)P_{\\mathrm{LY}}(y)\\,A_{32}(y)^{2}B_{66}(y)^{2}."
            )
            tex_D.append("\\]")
        else:
            tex_D.append("\\[")
            tex_D.append(f"S_{{98}}(y)={sp.latex(sqrt_q_poly.as_expr().subs({y0: y}))}.")
            tex_D.append("\\]")
            tex_D.append("\\[")
            tex_D.append(
                "\\mathrm{Disc}_{y_{3}}\\bigl(M_{3}(y,y_{3})\\bigr)"
                "=-y(y-1)P_{\\mathrm{LY}}(y)\\,S_{98}(y)^{2}."
            )
            tex_D.append("\\]")
        _write_text(generated_dir() / "eq_fold_zm_elliptic_weight_tripling_discriminant.tex", "\n".join(tex_D) + "\n")


if __name__ == "__main__":
    main()

