#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the Lee–Yang discriminant hyperelliptic curve

    C_LY:  w^2 = -y(y-1)(256y^3+411y^2+165y+32)

by computing a single good-prime local L-factor and checking irreducibility.

This script is English-only by repository convention.

We verify at p=13:
  - p is a good prime (squarefree RHS mod p).
  - Point counts N1 = #C(F_p), N2 = #C(F_{p^2}).
  - The genus-2 local factor
      L_p(T) = 1 - a1 T + a2 T^2 - a1 p T^3 + p^2 T^4,
    where a1 = p+1-N1 and a2 is recovered from N2.
  - Irreducibility of L_p(T) over Q, hence obstruction to an elliptic product.

Outputs:
  - artifacts/export/fold_zm_leyang_discriminant_curve_local_factor_audit.json
  - sections/generated/eq_fold_zm_leyang_discriminant_curve_local_factor_audit.tex
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


Fp2 = Tuple[int, int]  # a + b*alpha, alpha^2 = d in F_p


def _find_nonsquare(p: int) -> int:
    for d in range(2, p):
        if pow(d, (p - 1) // 2, p) == p - 1:
            return int(d)
    raise RuntimeError(f"Failed to find a nonsquare in F_{p}.")


def _fp2_add(u: Fp2, v: Fp2, *, p: int) -> Fp2:
    return ((u[0] + v[0]) % p, (u[1] + v[1]) % p)


def _fp2_sub(u: Fp2, v: Fp2, *, p: int) -> Fp2:
    return ((u[0] - v[0]) % p, (u[1] - v[1]) % p)


def _fp2_mul(u: Fp2, v: Fp2, *, p: int, d: int) -> Fp2:
    a, b = u
    c, e = v
    return ((a * c + b * e * d) % p, (a * e + b * c) % p)


def _fp2_sqr(u: Fp2, *, p: int, d: int) -> Fp2:
    return _fp2_mul(u, u, p=p, d=d)


def _fp2_pow(u: Fp2, n: int, *, p: int, d: int) -> Fp2:
    r: Fp2 = (1, 0)
    a = u
    k = int(n)
    while k > 0:
        if k & 1:
            r = _fp2_mul(r, a, p=p, d=d)
        a = _fp2_mul(a, a, p=p, d=d)
        k >>= 1
    return r


def _fp2_is_zero(u: Fp2, *, p: int) -> bool:
    return (u[0] % p == 0) and (u[1] % p == 0)


def _fp2_from_int(a: int, *, p: int) -> Fp2:
    return (a % p, 0)


def _quad_char_fp2(u: Fp2, *, p: int, d: int) -> int:
    """
    Quadratic character on F_{p^2}.
      0  if u == 0
      1  if u is a square
     -1  if u is a nonsquare
    """
    if _fp2_is_zero(u, p=p):
        return 0
    q = p * p
    t = _fp2_pow(u, (q - 1) // 2, p=p, d=d)
    if t == (1, 0):
        return 1
    if t == (p - 1, 0):
        return -1
    raise RuntimeError(f"Unexpected quadratic character value in F_{p**2}: {t}.")


def _rhs_fp(y: int, *, p: int) -> int:
    """
    RHS f(y) mod p for f(y) = -y(y-1)(256y^3+411y^2+165y+32).
    """
    y %= p
    poly = (256 * y * y * y + 411 * y * y + 165 * y + 32) % p
    return (-y * (y - 1) * poly) % p


def _rhs_fp2(y: Fp2, *, p: int, d: int) -> Fp2:
    y2 = _fp2_sqr(y, p=p, d=d)
    y3 = _fp2_mul(y2, y, p=p, d=d)
    poly = _fp2_add(
        _fp2_from_int(32, p=p),
        _fp2_add(
            _fp2_mul(_fp2_from_int(165, p=p), y, p=p, d=d),
            _fp2_add(
                _fp2_mul(_fp2_from_int(411, p=p), y2, p=p, d=d),
                _fp2_mul(_fp2_from_int(256, p=p), y3, p=p, d=d),
                p=p,
            ),
            p=p,
        ),
        p=p,
    )
    term = _fp2_mul(y, _fp2_sub(y, _fp2_from_int(1, p=p), p=p), p=p, d=d)
    return _fp2_mul(_fp2_from_int(-1, p=p), _fp2_mul(term, poly, p=p, d=d), p=p, d=d)


@dataclass(frozen=True)
class Payload:
    p: int
    nonsquare_d: int
    good_prime: bool
    rhs_squarefree_gcd_degree: int
    N1: int
    N2: int
    a1: int
    a2: int
    L_p_T: str
    L_p_T_factor_Z: str
    irreducible_over_Q: bool
    disc_in_U: int


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit a good-prime local L-factor for the Lee–Yang discriminant curve.")
    parser.add_argument("--p", type=int, default=13, help="Odd prime to use (default: 13).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    p = int(args.p)
    if p <= 2:
        raise SystemExit("--p must be an odd prime.")

    t0 = time.time()
    print("[fold-zm-leyang-disc-curve] start", flush=True)

    # --- Good prime check: gcd(f, f') == 1 in F_p[y] ---
    y = sp.Symbol("y")
    f = -y * (y - 1) * (256 * y**3 + 411 * y**2 + 165 * y + 32)
    f_mod = sp.Poly(f, y, modulus=p)
    df_mod = sp.Poly(sp.diff(f, y), y, modulus=p)
    g = sp.gcd(f_mod, df_mod)
    good = bool(g.degree() == 0)

    if not good:
        raise RuntimeError(f"Bad reduction at p={p}: gcd(f,f') has degree {g.degree()} (expected 0).")

    # --- Choose a nonsquare d to represent F_{p^2} as F_p[alpha]/(alpha^2-d) ---
    d = _find_nonsquare(p)

    # --- Count points over F_p ---
    N1 = 1  # point at infinity (deg(f)=5 is odd)
    for yy in range(p):
        rhs = _rhs_fp(yy, p=p)
        if rhs == 0:
            N1 += 1
        else:
            ls = pow(rhs, (p - 1) // 2, p)  # Legendre symbol mod p
            if ls == 1:
                N1 += 2

    # --- Count points over F_{p^2} ---
    q = p * p
    N2 = 1  # point at infinity
    for a in range(p):
        for b in range(p):
            yy2 = (a, b)
            rhs2 = _rhs_fp2(yy2, p=p, d=d)
            if _fp2_is_zero(rhs2, p=p):
                N2 += 1
            else:
                chi = _quad_char_fp2(rhs2, p=p, d=d)
                if chi == 1:
                    N2 += 2

    # --- Recover local factor coefficients ---
    a1 = p + 1 - int(N1)
    s2 = q + 1 - int(N2)  # sum alpha_i^2
    a2 = int((a1 * a1 - s2) // 2)

    T = sp.Symbol("T")
    Lp = sp.expand(1 - a1 * T + a2 * T**2 - a1 * p * T**3 + (p * p) * T**4)
    Lp_factor = sp.factor(Lp)
    irreducible = bool(Lp_factor == Lp)

    # Discriminant as a polynomial in U=T^2 (useful for the a1=0 symmetry case).
    U = sp.Symbol("U")
    polyU = sp.Poly(Lp.subs({T**2: U, T**4: U**2, T**3: T * U}), U, domain="ZZ")
    # If a1=0, Lp is even in T and polyU is well-defined without ambiguity.
    discU = int(sp.discriminant(polyU.as_expr(), U))

    payload = Payload(
        p=int(p),
        nonsquare_d=int(d),
        good_prime=bool(good),
        rhs_squarefree_gcd_degree=int(g.degree()),
        N1=int(N1),
        N2=int(N2),
        a1=int(a1),
        a2=int(a2),
        L_p_T=sp.sstr(Lp),
        L_p_T_factor_Z=sp.sstr(Lp_factor),
        irreducible_over_Q=bool(irreducible),
        disc_in_U=int(discU),
    )

    if not args.no_output:
        out_json = export_dir() / "fold_zm_leyang_discriminant_curve_local_factor_audit.json"
        _write_json(out_json, asdict(payload))

        out_tex = generated_dir() / "eq_fold_zm_leyang_discriminant_curve_local_factor_audit.tex"
        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_fold_zm_leyang_discriminant_curve_local_factor_audit.py",
                "\\[",
                "\\mathcal C_{\\mathrm{LY}}:\\ w^{2}=-y(y-1)(256y^{3}+411y^{2}+165y+32).",
                "\\]",
                "\\[",
                f"\\#\\mathcal C_{{\\mathrm{{LY}}}}(\\mathbb{{F}}_{{{p}}})={int(N1)},\\qquad "
                f"\\#\\mathcal C_{{\\mathrm{{LY}}}}(\\mathbb{{F}}_{{{p}^{{2}}}})={int(N2)}.",
                "\\]",
                "\\[",
                f"L_{{{p}}}(T)={sp.latex(Lp)}\\qquad\\text{{(factor over $\\mathbb{{Z}}$: }}{sp.latex(Lp_factor)}\\text{{)}}.",
                "\\]",
            ]
        )
        _write_text(out_tex, tex + "\n")

    dt = time.time() - t0
    print(
        "[fold-zm-leyang-disc-curve] checks:"
        f" p={p} good={good} N1={N1} N2={N2} a1={a1} a2={a2} irreducible={irreducible} seconds={dt:.3f}",
        flush=True,
    )
    print("[fold-zm-leyang-disc-curve] done", flush=True)


if __name__ == "__main__":
    main()

