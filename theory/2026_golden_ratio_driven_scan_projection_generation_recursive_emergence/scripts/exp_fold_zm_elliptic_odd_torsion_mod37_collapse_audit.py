#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit odd-torsion y-image collapses mod 37 on the Lee--Yang elliptic model.

This script is English-only by repository convention.

We work with the elliptic curve
  E: Y^2 = X^3 - X + 1/4
and the weight coordinate
  y := X^2 + Y - 1/2.

Eliminating Y gives the quartic spectral curve relation
  Pi(X,y) := X^4 - X^3 - (2y+1) X^2 + X + y(y+1) = 0.

For odd n, let psi_n(X) be the n-division polynomial in X for E. Define the
elimination polynomial
  L_n(y) := Res_X(psi_n(X), Pi(X,y)) in Z[y].

We certify, at the bad prime p=37:
  - L_3(y) ≡ 7 (y-6)^6 (y^2 - 5y - 1) (mod 37).
  - L_5(y) is irreducible of degree 24 over Q and
        L_5(y) ≡ -4 (y-6)^20 (y^4 + y^3 + 10y^2 + 9y + 4) (mod 37).
  - Over F_37, the degree-48 elimination polynomial satisfies
        Res_X(psi_7(X), Pi(X,y)) = -4 (y-6)^42 (y^6 - 11y^5 + 18y^4 + 7y^3 - 6y^2 - 13y - 9).

Outputs:
  - artifacts/export/fold_zm_elliptic_odd_torsion_mod37_collapse_audit.json
  - sections/generated/eq_fold_zm_elliptic_odd_torsion_mod37_collapse_audit.tex
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


@dataclass(frozen=True)
class Payload:
    l3_degree: int
    l3_matches_expected_ZZ: bool
    l3_mod37_matches_expected: bool
    l5_degree: int
    l5_lc: int
    l5_coeffs_high_to_low: List[int]
    l5_irreducible_over_Q: bool
    l5_mod37_matches_expected: bool
    psi7_degree: int
    psi7_lc: int
    l7_mod37_degree: int
    l7_mod37_y6_multiplicity: int
    l7_mod37_matches_expected: bool
    seconds: float


def _normalize_primitive_ZZ(poly: sp.Poly, var: sp.Symbol) -> sp.Poly:
    """Primitive content-free polynomial in ZZ[var] with positive leading coefficient."""
    if poly.domain != sp.ZZ:
        poly = sp.Poly(poly.as_expr(), var, domain=sp.ZZ)
    _content, prim = poly.primitive()
    if prim.LC() < 0:
        prim = -prim
    return prim


def _y6_multiplicity_mod_p(f: sp.Poly, *, p: int, y: sp.Symbol) -> int:
    """Return multiplicity of (y-6) dividing f in F_p[y]."""
    if f.get_modulus() != p:
        f = sp.Poly(f.as_expr(), y, modulus=p)
    lin = sp.Poly(y - 6, y, modulus=p)
    k = 0
    cur = f
    while True:
        q, r = sp.div(cur, lin, domain=sp.GF(p))
        if r.is_zero:
            k += 1
            cur = q
        else:
            break
    return k


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit odd-torsion y-image collapses mod 37 on E.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-elliptic-odd-torsion-mod37] start", flush=True)

    X, y = sp.symbols("X y")

    Pi = X**4 - X**3 - (2 * y + 1) * X**2 + X + y * (y + 1)

    # --- n=3 ---
    psi3 = 3 * X**4 - 6 * X**2 + 3 * X - 1
    res3 = sp.resultant(psi3, Pi, X)
    L3 = _normalize_primitive_ZZ(sp.Poly(sp.expand(res3), y, domain=sp.ZZ), y)
    L3_expected = sp.Poly(
        81 * y**8 - 324 * y**7 + 297 * y**6 + 729 * y**5 - 216 * y**4 - 1395 * y**3 - 480 * y**2 - 120 * y + 7,
        y,
        domain=sp.ZZ,
    )
    l3_matches_expected = L3 == L3_expected

    L3_mod37 = sp.Poly(L3.as_expr(), y, modulus=37)
    L3_mod37_expected = sp.Poly(7 * (y - 6) ** 6 * (y**2 - 5 * y - 1), y, modulus=37)
    l3_mod37_matches_expected = L3_mod37 == L3_mod37_expected

    # --- n=5 ---
    psi5 = (
        5 * X**12
        - 62 * X**10
        + 95 * X**9
        - 105 * X**8
        - 60 * X**7
        + 285 * X**6
        - 174 * X**5
        - 5 * X**4
        - 5 * X**3
        + 35 * X**2
        - 15 * X
        + 2
    )
    res5 = sp.resultant(psi5, Pi, X)
    L5 = _normalize_primitive_ZZ(sp.Poly(sp.expand(res5), y, domain=sp.ZZ), y)

    _c, factors_L5 = sp.factor_list(sp.Poly(L5.as_expr(), y, domain=sp.QQ))
    l5_irreducible = len(factors_L5) == 1 and int(factors_L5[0][0].degree()) == 24

    L5_mod37 = sp.Poly(L5.as_expr(), y, modulus=37)
    L5_mod37_expected = sp.Poly(-4 * (y - 6) ** 20 * (y**4 + y**3 + 10 * y**2 + 9 * y + 4), y, modulus=37)
    l5_mod37_matches_expected = L5_mod37 == L5_mod37_expected

    # --- n=7 (mod 37 only) ---
    # Use division polynomial identities for short Weierstrass curves to compute psi_7(X) in ZZ[X].
    # For E: Y^2 = X^3 + aX + b with a=-1, b=1/4:
    #   psi_2 = 2Y
    #   psi_3 = 3X^4 + 6aX^2 + 12bX - a^2
    #   psi_4 = 4Y*(X^6 + 5aX^4 + 20bX^3 - 5a^2X^2 - 4abX - 8b^2 - a^3)
    # and for odd indices: psi_5 = psi_4*psi_2^3 - psi_3^3, psi_7 = psi_5*psi_3^3 - psi_2*psi_4^3.
    a = -1
    b = sp.Rational(1, 4)
    E = X**3 + a * X + b
    F = X**6 + 5 * a * X**4 + 20 * b * X**3 - 5 * (a**2) * X**2 - 4 * a * b * X - 8 * (b**2) - a**3
    # Eliminate Y^4 by substituting (Y^2)^2 = E^2 in the odd-index formulas.
    psi5_expr = sp.expand(32 * E**2 * F - psi3**3)
    psi7_expr = sp.expand(psi5_expr * psi3**3 - 128 * E**2 * (F**3))
    psi7_poly = sp.Poly(psi7_expr, X, domain=sp.ZZ)

    psi7_mod37 = sp.Poly(psi7_poly.as_expr(), X, modulus=37)
    Pi_mod37 = sp.Poly(Pi, X, y, modulus=37)
    res7_mod37 = sp.resultant(psi7_mod37.as_expr(), Pi_mod37.as_expr(), X)
    L7_mod37 = sp.Poly(res7_mod37, y, modulus=37)

    L7_mod37_expected = sp.Poly(
        -4 * (y - 6) ** 42 * (y**6 - 11 * y**5 + 18 * y**4 + 7 * y**3 - 6 * y**2 - 13 * y - 9),
        y,
        modulus=37,
    )
    l7_mod37_matches_expected = L7_mod37 == L7_mod37_expected
    l7_y6_mult = _y6_multiplicity_mod_p(L7_mod37, p=37, y=y)

    dt = time.time() - t0
    payload = Payload(
        l3_degree=int(L3.degree()),
        l3_matches_expected_ZZ=bool(l3_matches_expected),
        l3_mod37_matches_expected=bool(l3_mod37_matches_expected),
        l5_degree=int(L5.degree()),
        l5_lc=int(L5.LC()),
        l5_coeffs_high_to_low=[int(c) for c in L5.all_coeffs()],
        l5_irreducible_over_Q=bool(l5_irreducible),
        l5_mod37_matches_expected=bool(l5_mod37_matches_expected),
        psi7_degree=int(psi7_poly.degree()),
        psi7_lc=int(psi7_poly.LC()),
        l7_mod37_degree=int(L7_mod37.degree()),
        l7_mod37_y6_multiplicity=int(l7_y6_mult),
        l7_mod37_matches_expected=bool(l7_mod37_matches_expected),
        seconds=float(dt),
    )

    if not args.no_output:
        out_json = export_dir() / "fold_zm_elliptic_odd_torsion_mod37_collapse_audit.json"
        _write_json(out_json, asdict(payload))

        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_fold_zm_elliptic_odd_torsion_mod37_collapse_audit.py",
                "\\[",
                r"L_{3}(y)\equiv 7\,(y-6)^{6}\,(y^{2}-5y-1)\pmod{37}.",
                "\\]",
                "\\[",
                f"L_{{5}}(y)={sp.latex(L5.as_expr())}.",
                "\\]",
                "\\[",
                r"L_{5}(y)\equiv -4\,(y-6)^{20}\,(y^{4}+y^{3}+10y^{2}+9y+4)\pmod{37}.",
                "\\]",
                "\\[",
                r"L_{7}^{(37)}(y)= -4\,(y-6)^{42}\,(y^{6}-11y^{5}+18y^{4}+7y^{3}-6y^{2}-13y-9).",
                "\\]",
                "",
            ]
        )
        out_tex = generated_dir() / "eq_fold_zm_elliptic_odd_torsion_mod37_collapse_audit.tex"
        _write_text(out_tex, tex)

        print(f"[fold-zm-elliptic-odd-torsion-mod37] wrote {out_json}", flush=True)
        print(f"[fold-zm-elliptic-odd-torsion-mod37] wrote {out_tex}", flush=True)

    print(
        "[fold-zm-elliptic-odd-torsion-mod37] checks:"
        f" L3_expected={l3_matches_expected} L3_mod37={l3_mod37_matches_expected}"
        f" L5_deg={L5.degree()} irreducible={l5_irreducible} L5_mod37={l5_mod37_matches_expected}"
        f" psi7_deg={psi7_poly.degree()} L7_mod37_deg={L7_mod37.degree()} y6_mult={l7_y6_mult} L7_mod37={l7_mod37_matches_expected}"
        f" seconds={dt:.3f}",
        flush=True,
    )
    print("[fold-zm-elliptic-odd-torsion-mod37] done", flush=True)


if __name__ == "__main__":
    main()

