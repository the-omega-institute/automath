#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the elliptic normalization of the Fold fiber-weight spectral curve Pi(lambda,y)=0.

This script is English-only by repository convention.

We verify symbolically and numerically:
  - Birational transform between Pi(lambda,y)=0 and the cubic Weierstrass model
      w^2 = 4 lambda^3 - 4 lambda + 1
    via w = 2 lambda^2 - 1 - 2 y, with inverse y = (2 lambda^2 - 1 - w)/2.
  - The associated short Weierstrass curve
      Y^2 = X^3 - X + 1/4
    has discriminant Delta=37 and j-invariant j=110592/37.
  - Resultant / branch locus:
      Res_lambda(Pi, dPi/dlambda) = -y(y-1)(256y^3+411y^2+165y+32).
  - Elimination of y from Pi=0 and dPi/dlambda=0 yields
      (lambda-1)(lambda+1)(16 lambda^3 - 9 lambda^2 + 1)=0,
    hence the nontrivial ramification lambda_LY is the unique real root of the cubic factor.
  - Closed-form back-substitution recovers y_LY from (lambda_LY, w_LY).
  - Puiseux amplitude at the Lee--Yang branch point:
      a_LY^2 = -2 * (∂_y Pi)/(∂_{λλ} Pi) evaluated at (lambda_LY, y_LY),
    and derived scaling constant pi^2 * lambda_LY^2 / a_LY^2.
  - Arithmetic of the Lee–Yang cubic g(y)=256y^3+411y^2+165y+32:
      Disc(g) = -3^9 * 31^2 * 37, squarefree part = -111,
      hence the unique quadratic subfield is Q(sqrt(-111)), with class number h(-111)=8.
  - Field arithmetic of the Lee–Yang cubic field K (maximal order):
      Disc(K) = -999 = -3^3 * 37, so only {3,37} ramify;
      3 is totally ramified, and 37 has factorization type (1)(2) (i.e., P * Q^2).
  - Discriminant of P2(lambda)=lambda^3-2lambda^2-2lambda+2 equals 148=4*37.

Outputs:
  - artifacts/export/fold_zm_elliptic_leyang_arithmetic_audit.json
  - sections/generated/eq_fold_zm_elliptic_leyang_arithmetic_audit.tex
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp
from sympy.polys.numberfields import prime_decomp
from sympy.polys.numberfields.basis import round_two

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _squarefree_part_from_factorint(fac: Dict[int, int]) -> int:
    out = 1
    for p, e in fac.items():
        if e % 2 == 1:
            out *= int(p)
    return int(out)


def _reduced_primitive_forms_negative_discriminant(D: int) -> List[Tuple[int, int, int]]:
    """
    Enumerate reduced primitive positive definite binary quadratic forms (a,b,c)
    of discriminant D<0 (D ≡ 0 or 1 mod 4).

    For negative fundamental discriminant D, the number of reduced primitive forms equals h(D).
    """
    if D >= 0:
        raise ValueError("Expected a negative discriminant D<0.")
    if D % 4 not in (0, 1):
        raise ValueError("Expected a discriminant D congruent to 0 or 1 mod 4.")

    max_a = int(math.isqrt(abs(D) // 3 + 1))
    parity = D & 1  # b ≡ D (mod 2)

    forms: List[Tuple[int, int, int]] = []
    for a in range(1, max_a + 1):
        for b in range(-a, a + 1):
            if (b - parity) & 1:
                continue
            disc_term = b * b - D
            denom = 4 * a
            if disc_term % denom != 0:
                continue
            c = disc_term // denom

            # Reduced conditions: |b| <= a <= c, with tie-breaker.
            if abs(b) > a:
                continue
            if a > c:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue

            # Primitive.
            if math.gcd(a, math.gcd(b, c)) != 1:
                continue

            forms.append((a, b, c))

    return forms


def _alpha_vec_to_poly_expr(alpha: List[int], x: sp.Symbol) -> sp.Expr:
    """
    Convert a PrimeIdeal.alpha vector (power-basis coordinates) to a polynomial in x.
    """
    expr = sp.Integer(0)
    for i, a in enumerate(alpha):
        ai = int(a)
        if ai == 0:
            continue
        expr += sp.Integer(ai) * (x**i)
    return sp.expand(expr)


@dataclass(frozen=True)
class PrimeIdealData:
    gen: str
    e: int
    f: int


@dataclass(frozen=True)
class Payload:
    # core identities
    birational_identity_ok: bool
    resultant_factorization_ok: bool
    elimination_lambda_cubic_ok: bool
    weierstrass_invariants_ok: bool
    # Lee–Yang branch values
    y_LY_from_cubic: str
    lambda_LY_from_cubic: str
    w_LY_positive: str
    y_LY_backsub: str
    y_LY_backsub_matches: bool
    # Puiseux amplitude at y_LY
    a_LY_sq: str
    lambda_LY_sq_over_a_LY_sq: str
    pi2_lambda_LY_sq_over_a_LY_sq: str
    # arithmetic
    disc_g: int
    disc_g_factorization: Dict[str, int]
    disc_g_squarefree_part: int
    quadratic_subfield: str
    quadratic_field_discriminant: int
    class_number: int
    reduced_forms: List[Tuple[int, int, int]]
    # cubic field K = Q(beta) (maximal order)
    disc_field_K: int
    disc_field_K_factorization: Dict[str, int]
    disc_field_K_squarefree_part: int
    signature_r1: int
    signature_r2: int
    ramified_primes_K: List[int]
    prime_decomposition_3: List[PrimeIdealData]
    prime_decomposition_37: List[PrimeIdealData]
    # P2
    disc_P2: int


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit elliptic normalization and Lee–Yang arithmetic for Pi(lambda,y).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    parser.add_argument("--dps", type=int, default=80, help="Decimal precision for nroots (default: 80).")
    args = parser.parse_args()

    dps = int(args.dps)
    if dps < 50:
        raise SystemExit("Require --dps >= 50 for stable outputs.")

    t0 = time.time()
    print("[fold-zm-elliptic-leyang-arith] start", flush=True)

    lam, y, w = sp.symbols("lam y w")
    Pi = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)

    # --- Birational identity (w = 2 lam^2 - 1 - 2 y) ---
    y_back = (2 * lam**2 - 1 - w) / 2
    bir = sp.factor(4 * sp.expand(Pi.subs({y: y_back})) - (w**2 - (4 * lam**3 - 4 * lam + 1)))
    birational_ok = bool(bir == 0)

    # --- Weierstrass invariants for Y^2 = X^3 - X + 1/4 ---
    a = sp.Integer(-1)
    b = sp.Rational(1, 4)
    Delta = sp.simplify(-16 * (4 * a**3 + 27 * b**2))
    c4 = sp.simplify(-48 * a)
    j = sp.simplify(c4**3 / Delta)
    invariants_ok = bool(Delta == 37 and j == sp.Rational(110592, 37))

    # --- Resultant factorization (branch locus) ---
    Res = sp.factor(sp.resultant(Pi, sp.diff(Pi, lam), lam))
    Res_expected = -y * (y - 1) * (256 * y**3 + 411 * y**2 + 165 * y + 32)
    resultant_ok = bool(sp.factor(Res - Res_expected) == 0)

    # --- Eliminate y from Pi=0 and dPi/dlam=0 ---
    y_expr = sp.simplify(sp.solve(sp.diff(Pi, lam), y)[0])
    rat = sp.together(Pi.subs({y: y_expr}))
    num, den = sp.together(rat).as_numer_denom()
    num = sp.factor(num)
    num_expected = -(lam - 1) * (lam + 1) * (16 * lam**3 - 9 * lam**2 + 1)
    elimination_ok = bool(sp.factor(num - num_expected) == 0)

    # --- Numeric Lee–Yang root(s) ---
    cubic_y = 256 * y**3 + 411 * y**2 + 165 * y + 32
    y_roots = sp.nroots(cubic_y, n=dps, maxsteps=200)
    y_LY = None
    for r in y_roots:
        if abs(sp.im(r)) < sp.Float(10) ** (-(dps // 2)) and float(sp.re(r)) < 0:
            y_LY = sp.N(sp.re(r), dps)
            break
    if y_LY is None:
        raise RuntimeError("Failed to locate the negative real Lee–Yang root of the cubic factor.")

    cubic_lam = 16 * lam**3 - 9 * lam**2 + 1
    lam_roots = sp.nroots(cubic_lam, n=dps, maxsteps=200)
    lam_LY = None
    for r in lam_roots:
        if abs(sp.im(r)) < sp.Float(10) ** (-(dps // 2)):
            lam_LY = sp.N(sp.re(r), dps)
            break
    if lam_LY is None:
        raise RuntimeError("Failed to locate the real ramification root lambda_LY.")

    w_LY = sp.sqrt(4 * lam_LY**3 - 4 * lam_LY + 1)  # principal (positive) sqrt
    y_backsub = sp.N((2 * lam_LY**2 - 1 - w_LY) / 2, dps)
    y_match = bool(abs(y_backsub - y_LY) < sp.Float(10) ** (-(dps // 2 - 5)))

    # --- Puiseux amplitude at (lambda_LY, y_LY) ---
    dPi_dy = sp.diff(Pi, y)
    d2Pi_dlam2 = sp.diff(Pi, lam, 2)
    a_LY_sq = sp.N(
        -2 * dPi_dy.subs({lam: lam_LY, y: y_backsub}) / d2Pi_dlam2.subs({lam: lam_LY, y: y_backsub}),
        dps,
    )
    lam_sq_over_a_sq = sp.N((lam_LY**2) / a_LY_sq, dps)
    pi2_lam_sq_over_a_sq = sp.N((sp.pi**2) * lam_sq_over_a_sq, dps)

    # --- Arithmetic of the Lee–Yang cubic ---
    disc_g = int(sp.discriminant(cubic_y, y))
    fac = sp.factorint(disc_g)
    sqfree = _squarefree_part_from_factorint(fac)

    # The quadratic subfield is Q(sqrt(disc_g)) = Q(sqrt(squarefree_part)).
    if sqfree != -111:
        raise RuntimeError(f"Unexpected squarefree part: got {sqfree}, expected -111.")
    D = int(sqfree)  # -111 is a fundamental discriminant (≡1 mod 4, squarefree).
    forms = _reduced_primitive_forms_negative_discriminant(D)
    h = len(forms)

    # --- Field discriminant + prime decompositions for the Lee–Yang cubic field ---
    # Work with an integral generator theta := 256*beta, where beta is a root of g(y)=0.
    # Then theta is a root of a monic integer cubic, generating the same cubic field.
    th = sp.Symbol("th")
    poly_theta = sp.Poly(th**3 + 411 * th**2 + 42240 * th + 2097152, th, domain=sp.ZZ)
    ZK, disc_field_K = round_two(poly_theta)
    disc_field_K = int(disc_field_K)
    disc_field_fac_abs = sp.factorint(abs(disc_field_K))
    disc_field_sqfree = _squarefree_part_from_factorint(disc_field_fac_abs)
    if disc_field_K < 0:
        disc_field_sqfree = -int(disc_field_sqfree)

    # For a cubic field, Disc(K)<0 iff signature is (1,1).
    r1 = 1 if disc_field_K < 0 else 3
    r2 = (3 - r1) // 2

    # Ramified primes are exactly those dividing the field discriminant.
    ramified_primes_K = sorted(int(p) for p in disc_field_fac_abs.keys())

    # Prime ideal decompositions above the ramified primes (local structure).
    def _prime_decomp_data(p: int) -> List[PrimeIdealData]:
        ideals = prime_decomp(int(p), T=poly_theta, ZK=ZK, dK=disc_field_K)
        items: List[PrimeIdealData] = []
        for P in ideals:
            gen_expr = _alpha_vec_to_poly_expr(P.alpha.coeffs, th)
            items.append(PrimeIdealData(gen=sp.sstr(gen_expr), e=int(P.e), f=int(P.f)))
        items.sort(key=lambda it: (-it.e, -it.f, it.gen))
        return items

    decomp_3 = _prime_decomp_data(3)
    decomp_37 = _prime_decomp_data(37)

    # Sanity checks against the expected tame/wild ramification portrait.
    if disc_field_K != -999:
        raise RuntimeError(f"Unexpected field discriminant: got {disc_field_K}, expected -999.")
    if disc_field_sqfree != -111:
        raise RuntimeError(f"Unexpected field discriminant squarefree part: got {disc_field_sqfree}, expected -111.")
    if ramified_primes_K != [3, 37]:
        raise RuntimeError(f"Unexpected ramified primes: got {ramified_primes_K}, expected [3, 37].")
    if not (len(decomp_3) == 1 and decomp_3[0].e == 3 and decomp_3[0].f == 1):
        raise RuntimeError(f"Unexpected decomposition at p=3: got {decomp_3}.")
    if not (
        len(decomp_37) == 2
        and sorted([(it.e, it.f) for it in decomp_37]) == [(1, 1), (2, 1)]
    ):
        raise RuntimeError(f"Unexpected decomposition at p=37: got {decomp_37}.")

    # --- Discriminant of P2(lambda) ---
    lam2 = sp.Symbol("lam2")
    P2 = lam2**3 - 2 * lam2**2 - 2 * lam2 + 2
    disc_P2 = int(sp.discriminant(P2, lam2))

    payload = Payload(
        birational_identity_ok=birational_ok,
        resultant_factorization_ok=resultant_ok,
        elimination_lambda_cubic_ok=elimination_ok,
        weierstrass_invariants_ok=invariants_ok,
        y_LY_from_cubic=sp.sstr(y_LY),
        lambda_LY_from_cubic=sp.sstr(lam_LY),
        w_LY_positive=sp.sstr(sp.N(w_LY, dps)),
        y_LY_backsub=sp.sstr(y_backsub),
        y_LY_backsub_matches=y_match,
        a_LY_sq=sp.sstr(a_LY_sq),
        lambda_LY_sq_over_a_LY_sq=sp.sstr(lam_sq_over_a_sq),
        pi2_lambda_LY_sq_over_a_LY_sq=sp.sstr(pi2_lam_sq_over_a_sq),
        disc_g=int(disc_g),
        disc_g_factorization={str(int(p)): int(e) for p, e in fac.items()},
        disc_g_squarefree_part=int(sqfree),
        quadratic_subfield=f"Q(sqrt({int(sqfree)}))",
        quadratic_field_discriminant=int(D),
        class_number=int(h),
        reduced_forms=forms,
        disc_field_K=int(disc_field_K),
        disc_field_K_factorization={str(int(p)): int(e) for p, e in sp.factorint(abs(disc_field_K)).items()},
        disc_field_K_squarefree_part=int(disc_field_sqfree),
        signature_r1=int(r1),
        signature_r2=int(r2),
        ramified_primes_K=[int(p) for p in ramified_primes_K],
        prime_decomposition_3=decomp_3,
        prime_decomposition_37=decomp_37,
        disc_P2=int(disc_P2),
    )

    if not args.no_output:
        out_json = export_dir() / "fold_zm_elliptic_leyang_arithmetic_audit.json"
        _write_json(out_json, asdict(payload))

        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_fold_zm_elliptic_leyang_arithmetic_audit.py",
                "\\[",
                "w:=2\\lambda^{2}-1-2y,\\qquad 4\\Pi(\\lambda,y)=w^{2}-(4\\lambda^{3}-4\\lambda+1).",
                "\\]",
                "\\[",
                "E:\\ Y^{2}=X^{3}-X+\\frac14,\\qquad \\Delta(E)=37,\\qquad j(E)=\\frac{110592}{37}.",
                "\\]",
                "\\[",
                "\\mathrm{Res}_{\\lambda}(\\Pi,\\partial_{\\lambda}\\Pi)=-y(y-1)(256y^{3}+411y^{2}+165y+32).",
                "\\]",
                "\\[",
                "16\\lambda^{3}-9\\lambda^{2}+1=0\\ \\Rightarrow\\ \\lambda_{\\mathrm{LY}}\\approx "
                + f"{float(lam_LY):.16f}",
                "\\]",
                "\\[",
                "y_{\\mathrm{LY}}=\\frac{2\\lambda_{\\mathrm{LY}}^{2}-1-\\sqrt{4\\lambda_{\\mathrm{LY}}^{3}-4\\lambda_{\\mathrm{LY}}+1}}{2}\\ \\approx\\ "
                + f"{float(y_LY):.16f}",
                "\\]",
                "\\[",
                "a_{\\mathrm{LY}}^{2}=-\\,\\frac{2\\,\\partial_{y}\\Pi(\\lambda_{\\mathrm{LY}},y_{\\mathrm{LY}})}{\\partial_{\\lambda\\lambda}\\Pi(\\lambda_{\\mathrm{LY}},y_{\\mathrm{LY}})}\\ \\approx\\ "
                + f"{float(a_LY_sq):.16f}",
                "\\]",
                "\\[",
                "\\frac{\\lambda_{\\mathrm{LY}}^{2}}{a_{\\mathrm{LY}}^{2}}\\ \\approx\\ " + f"{float(lam_sq_over_a_sq):.16f}",
                "\\qquad",
                "\\pi^{2}\\frac{\\lambda_{\\mathrm{LY}}^{2}}{a_{\\mathrm{LY}}^{2}}\\ \\approx\\ "
                + f"{float(pi2_lam_sq_over_a_sq):.16f}",
                "\\]",
                "\\[",
                "\\mathrm{Disc}(256y^{3}+411y^{2}+165y+32)=-3^{9}\\cdot 31^{2}\\cdot 37,\\quad \\text{sqfree part }=-111,\\quad h(-111)=8.",
                "\\]",
                "\\[",
                "\\mathrm{Disc}(K)=-999=-3^{3}\\cdot 37,\\qquad 3\\mathcal O_K=\\mathfrak p_3^{3},\\qquad 37\\mathcal O_K=\\mathfrak p_{37}^{2}\\mathfrak q_{37}.",
                "\\]",
                "\\[",
                "\\mathrm{Disc}(\\lambda^{3}-2\\lambda^{2}-2\\lambda+2)=148=4\\cdot 37.",
                "\\]",
                "",
            ]
        )
        out_tex = generated_dir() / "eq_fold_zm_elliptic_leyang_arithmetic_audit.tex"
        _write_text(out_tex, tex)

        print(f"[fold-zm-elliptic-leyang-arith] wrote {out_json}", flush=True)
        print(f"[fold-zm-elliptic-leyang-arith] wrote {out_tex}", flush=True)

    dt = time.time() - t0
    print(
        "[fold-zm-elliptic-leyang-arith] checks:"
        f" bir={birational_ok} inv={invariants_ok} res={resultant_ok} elim={elimination_ok}"
        f" y_match={y_match} disc_field_K={disc_field_K} disc_P2={disc_P2} h(-111)={h} seconds={dt:.3f}",
        flush=True,
    )
    print("[fold-zm-elliptic-leyang-arith] done", flush=True)


if __name__ == "__main__":
    main()

