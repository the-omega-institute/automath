#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit Q5/A7 subresultants and Galois certificates.

This script checks several explicit algebraic fingerprints used in the xi section:
  - Q5(y) discriminant factorization, mod-p factor patterns (5-cycle + transposition => S5),
  - the first subresultant SRes_1(F_delta, d/dT F_delta) closed form and the delta_*(y) formula,
  - the characteristic-31 total collapse fiber F_delta(T;y0) ≡ T^4 (mod 31),
  - A7(y) mod-p factor patterns (7-cycle + transposition => S7),
  - quadratic subfield mismatch for linear disjointness (PLY vs Q5).

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import paper_root, scripts_dir


@dataclass(frozen=True)
class ModFactorSummary:
    p: int
    degrees: List[int]
    exponents: List[int]


def _factor_degrees_mod(poly: sp.Poly, p: int) -> ModFactorSummary:
    fp = sp.Poly(poly.as_expr(), poly.gens[0], modulus=p)
    _, factors = fp.factor_list()
    degrees: List[int] = []
    exponents: List[int] = []
    for f, e in factors:
        degrees.append(int(f.degree()))
        exponents.append(int(e))
    return ModFactorSummary(p=p, degrees=degrees, exponents=exponents)


def _valuation(n: int, p: int) -> int:
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def _modp_rational(q: sp.Rational, p: int) -> int:
    num, den = sp.fraction(sp.together(q))
    num_i = int(num)
    den_i = int(den)
    den_inv = pow(den_i % p, -1, p)
    return int((num_i % p) * den_inv % p)


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Q5/A7 subresultant and Galois certificates.")
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(paper_root() / "artifacts" / "export" / "xi_leyang_q5_a7_subresultant_galois_audit.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    y, T = sp.symbols("y T")

    PLY = 256 * y**3 + 411 * y**2 + 165 * y + 32
    Q5 = 4096 * y**5 + 5376 * y**4 - 464 * y**3 - 2749 * y**2 - 723 * y + 80

    A7 = (
        45056 * y**7
        + 60160 * y**6
        - 11984 * y**5
        - 19765 * y**4
        + 18906 * y**3
        + 14723 * y**2
        + 2216 * y
        + 200
    )

    # F_delta(T;y) in Z[y][T]
    F_delta = T**4 + (8 * y - 3) * T**3 + (2 * y**2 - 34 * y - 4) * T**2 - y * (y - 1) * PLY
    dF = sp.diff(F_delta, T)

    # Q5 discriminant (in Z) and mod-p patterns
    disc_Q5 = int(sp.discriminant(sp.Poly(Q5, y), y))
    disc_Q5_factors = sp.factorint(abs(disc_Q5))
    mod_Q5_7 = _factor_degrees_mod(sp.Poly(Q5, y), 7)
    mod_Q5_727 = _factor_degrees_mod(sp.Poly(Q5, y), 727)

    # A7 discriminant and mod-p patterns
    disc_A7 = int(sp.discriminant(sp.Poly(A7, y), y))
    disc_A7_factors = sp.factorint(abs(disc_A7))
    mod_A7_23 = _factor_degrees_mod(sp.Poly(A7, y), 23)
    mod_A7_5651 = _factor_degrees_mod(sp.Poly(A7, y), 5651)

    # SRes_1 closed form
    sres_list = sp.subresultants(sp.Poly(F_delta, T), sp.Poly(dF, T))
    # SymPy's ordering is implementation-defined; select the unique degree-1 subresultant in T.
    sres_polys = [sp.Poly(sr, T) for sr in sres_list]
    deg1 = [p for p in sres_polys if p.degree() == 1]
    if len(deg1) != 1:
        raise RuntimeError(f"Expected exactly one degree-1 subresultant, got {len(deg1)}")
    sres1 = deg1[0].as_expr()
    sres1_expected = -4 * A7 * T - y * (y - 1) * (8 * y - 3) * (16 * y + 11) * (32 * y + 19) * PLY
    sres1_ok = sp.expand(sres1 - sres1_expected) == 0

    # gcd checks in Z[y]
    gcd_A7_y_y1_PLY = sp.gcd(sp.Poly(A7, y), sp.Poly(y * (y - 1) * PLY, y)).as_expr()
    gcd_A7_Q5 = sp.gcd(sp.Poly(A7, y), sp.Poly(Q5, y)).as_expr()

    # characteristic-31 total collapse at y0 = 3/8 ≡ 12 (mod 31)
    y0 = sp.Rational(3, 8)
    coeff_T3 = _modp_rational(sp.Rational(8) * y0 - 3, 31)
    coeff_T2 = _modp_rational(2 * y0**2 - 34 * y0 - 4, 31)
    ply_y0 = sp.together(PLY.subs(y, y0))
    # Check PLY(y0) has 31^2 factor (numerator)
    ply_num, ply_den = sp.fraction(ply_y0)
    ply_num_int = int(sp.factor(ply_num))
    ply_den_int = int(sp.factor(ply_den))
    v31_num = _valuation(abs(ply_num_int), 31)
    v31_den = _valuation(abs(ply_den_int), 31)

    # Linear disjointness via quadratic subfields (squarefree discriminant parts)
    disc_PLY = int(sp.discriminant(sp.Poly(PLY, y), y))
    # squarefree kernel
    disc_PLY_sf = int(sp.factorint(abs(disc_PLY)).copy() and 1)
    # compute squarefree part explicitly
    sf_PLY = 1
    for p, e in sp.factorint(abs(disc_PLY)).items():
        if e % 2 == 1:
            sf_PLY *= p
    sf_Q5 = 1
    for p, e in disc_Q5_factors.items():
        if e % 2 == 1:
            sf_Q5 *= p
    sf_PLY_signed = -sf_PLY if disc_PLY < 0 else sf_PLY
    sf_Q5_signed = -sf_Q5 if disc_Q5 < 0 else sf_Q5

    out: Dict[str, object] = {
        "Q5": {
            "poly": str(sp.expand(Q5)),
            "disc": int(disc_Q5),
            "disc_factorint_abs": {int(k): int(v) for k, v in disc_Q5_factors.items()},
            "mod7": asdict(mod_Q5_7),
            "mod727": asdict(mod_Q5_727),
        },
        "PLY": {
            "poly": str(sp.expand(PLY)),
            "disc": int(disc_PLY),
        },
        "linear_disjointness_quadratic_kernels": {
            "disc_squarefree_part_PLY_signed": int(sf_PLY_signed),
            "disc_squarefree_part_Q5_signed": int(sf_Q5_signed),
            "equal": bool(sf_PLY_signed == sf_Q5_signed),
        },
        "A7": {
            "poly": str(sp.expand(A7)),
            "disc": int(disc_A7),
            "disc_factorint_abs": {int(k): int(v) for k, v in disc_A7_factors.items()},
            "mod23": asdict(mod_A7_23),
            "mod5651": asdict(mod_A7_5651),
        },
        "F_delta": {
            "poly_T": str(sp.expand(F_delta)),
            "sres1_ok": bool(sres1_ok),
            "sres1": str(sp.expand(sres1)),
            "sres1_expected": str(sp.expand(sres1_expected)),
            "gcd_A7__y(y-1)PLY": str(gcd_A7_y_y1_PLY),
            "gcd_A7__Q5": str(gcd_A7_Q5),
        },
        "char31_total_collapse": {
            "y0_rational": "3/8",
            "coeff_T3_mod31": int(coeff_T3),
            "coeff_T2_mod31": int(coeff_T2),
            "PLY_y0_num": int(ply_num_int),
            "PLY_y0_den": int(ply_den_int),
            "v31_num": int(v31_num),
            "v31_den": int(v31_den),
        },
        "meta": {
            "script": Path(__file__).name,
            "scripts_dir": str(scripts_dir()),
        },
    }

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Hard assertions for pipeline gating
    assert sres1_ok, "SRes_1 closed form mismatch"
    assert gcd_A7_y_y1_PLY == 1, "gcd(A7, y(y-1)PLY) != 1 over Z"
    assert gcd_A7_Q5 == 1, "gcd(A7, Q5) != 1 over Z"
    assert mod_Q5_7.degrees == [5] and mod_Q5_7.exponents == [1], "Q5 mod 7 not irreducible degree 5"
    assert 2 in mod_Q5_727.exponents, "Q5 mod 727 does not show a repeated factor"
    assert mod_A7_23.degrees == [7] and mod_A7_23.exponents == [1], "A7 mod 23 not irreducible degree 7"
    assert 2 in mod_A7_5651.exponents, "A7 mod 5651 does not show a repeated factor"
    assert int(coeff_T3) == 0 and int(coeff_T2) == 0, "Char-31 coefficient vanish check failed"
    assert v31_num >= 2 and v31_den == 0, "PLY(3/8) does not have 31^2 in numerator as expected"


if __name__ == "__main__":
    main()

