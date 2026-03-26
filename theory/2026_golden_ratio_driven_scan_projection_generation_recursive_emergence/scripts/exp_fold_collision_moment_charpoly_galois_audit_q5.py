#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Arithmetic/Galois audit for the 5th collision-moment characteristic polynomial P_5.

We audit:
  - discriminant and its prime support,
  - mod-p factorizations used for Frobenius cycle-type certificates,
  - monogenicity and field discriminant for K_5 = Q(rho_5),
  - elimination/resultant certificates for natural S_5-subrepresentations:
      * pairwise sums  alpha_i + alpha_j  (degree 10),
      * pairwise products alpha_i alpha_j (degree 10),
      * ordered ratios alpha_j^2/alpha_i  (degree 20, i!=j).

Outputs:
  - artifacts/export/fold_collision_moment_charpoly_galois_audit_q5.json
"""

from __future__ import annotations

import argparse
import json
import warnings
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp
from sympy.polys.numberfields.basis import round_two

from common_paths import export_dir

try:
    from sympy.utilities.exceptions import SymPyDeprecationWarning

    warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)
except Exception:
    pass


def _squarefree_part_from_factorint(fac: Dict[int, int]) -> int:
    out = 1
    for p, e in fac.items():
        if int(p) == -1:
            continue
        if int(e) % 2 == 1:
            out *= int(p)
    if int(fac.get(-1, 0)) % 2 == 1:
        out = -out
    return int(out)


def _factor_mod_p(poly: sp.Poly, p: int) -> Tuple[bool, List[int], List[Tuple[str, int]]]:
    x = poly.gens[0]
    f = sp.Poly(poly.as_expr(), x, modulus=p)
    g = sp.gcd(f, f.diff())
    squarefree = (g.degree() == 0)
    _, facs = sp.factor_list(f, modulus=p)
    degs: List[int] = []
    fac_list: List[Tuple[str, int]] = []
    for ff, ee in facs:
        ff_poly = sp.Poly(ff, x, modulus=p)
        degs.extend([int(ff_poly.degree())] * int(ee))
        fac_list.append((sp.sstr(ff_poly.as_expr()), int(ee)))
    degs.sort(reverse=True)
    return bool(squarefree), degs, fac_list


def _poly_P5() -> sp.Poly:
    x = sp.Symbol("x")
    expr = x**5 - 2 * x**4 - 11 * x**3 - 8 * x**2 - 20 * x + 10
    return sp.Poly(sp.expand(expr), x)


def _poly_Rplus_expected() -> sp.Poly:
    s = sp.Symbol("s")
    expr = (
        s**10
        - 8 * s**9
        - 9 * s**8
        + 158 * s**7
        + 107 * s**6
        - 1482 * s**5
        - 711 * s**4
        + 2262 * s**3
        + 432 * s**2
        + 10350 * s
        + 7200
    )
    return sp.Poly(sp.expand(expr), s)


def _poly_Rtimes_expected() -> sp.Poly:
    p = sp.Symbol("p")
    expr = (
        p**10
        + 11 * p**9
        + 36 * p**8
        + 436 * p**7
        - 1540 * p**6
        + 7080 * p**5
        - 18700 * p**4
        - 2900 * p**3
        + 24000 * p**2
        + 8000 * p
        + 10000
    )
    return sp.Poly(sp.expand(expr), p)


def _poly_Newman_expected() -> sp.Poly:
    u = sp.Symbol("u")
    expr = (
        500 * u**20
        - 25000 * u**19
        - 177700 * u**18
        - 3823100 * u**17
        + 40765660 * u**16
        + 1496266360 * u**15
        + 9983236609 * u**14
        + 36022632766 * u**13
        + 64996856413 * u**12
        - 87017173082 * u**11
        - 763519868228 * u**10
        + 2321405618236 * u**9
        - 2486082754184 * u**8
        + 244212607720 * u**7
        + 786872105380 * u**6
        - 96473453600 * u**5
        - 197869496000 * u**4
        - 17361320000 * u**3
        - 2353600000 * u**2
        - 46000000 * u
        + 5000000
    )
    return sp.Poly(sp.expand(expr), u)


@dataclass(frozen=True)
class FactorModP:
    p: int
    squarefree: bool
    factor_degrees: List[int]
    factors: List[Tuple[str, int]]


@dataclass(frozen=True)
class Payload:
    P5: str
    disc_P5: int
    disc_P5_factorization: Dict[str, int]
    disc_P5_squarefree_part: int
    ramified_primes_P5: List[int]
    modp_certificates_P5: List[FactorModP]
    OK_equals_Zrho5: bool
    disc_field_K5: int
    index_squared: int
    # eliminations
    Rplus: str
    Rtimes: str
    Newman_poly: str
    disc_Rplus: int
    disc_Rtimes: int
    disc_Rplus_factorization: Dict[str, int]
    disc_Rtimes_factorization: Dict[str, int]


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit arithmetic/Galois invariants for the q=5 collision-moment charpoly.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_moment_charpoly_galois_audit_q5.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    P5 = _poly_P5()
    x = P5.gens[0]

    disc_P5 = int(P5.discriminant())
    disc_fac = sp.factorint(disc_P5)
    disc_sqfree = int(_squarefree_part_from_factorint(disc_fac))
    ramified_primes = sorted({abs(int(p)) for p in disc_fac.keys() if int(p) not in {-1, 1}})

    # Monogenicity + field discriminant by maximal-order algorithm.
    ZK, disc_field = round_two(P5)
    disc_field = int(disc_field)
    index_squared = int(disc_P5 // disc_field)
    OK_equals_Zrho5 = bool(index_squared == 1)

    # Mod-p certificates used in the paper text.
    certs: List[FactorModP] = []
    for p in [17, 29]:
        sqf, degs, fac_list = _factor_mod_p(P5, p)
        certs.append(FactorModP(p=int(p), squarefree=bool(sqf), factor_degrees=degs, factors=fac_list))

    # Full local list at ramified primes (used for index checks in the writeup).
    for p in [2, 3, 5, 11, 13, 17383]:
        sqf, degs, fac_list = _factor_mod_p(P5, p)
        certs.append(FactorModP(p=int(p), squarefree=bool(sqf), factor_degrees=degs, factors=fac_list))

    # Elimination: pairwise sums.
    s = sp.Symbol("s")
    Rplus = _poly_Rplus_expected()
    res_sum = sp.resultant(P5.as_expr(), sp.expand(P5.as_expr().subs(x, s - x)), x)
    res_sum_poly = sp.Poly(sp.expand(res_sum), s)
    diag_sum = sp.Poly(sp.expand(32 * P5.as_expr().subs(x, sp.Rational(1, 2) * s)), s)
    q_sum, r_sum = sp.div(res_sum_poly, diag_sum)
    if not r_sum.is_zero:
        raise RuntimeError("Sum resultant not divisible by diagonal factor 32*P5(s/2).")
    q2_sum, r2_sum = sp.div(q_sum, sp.Poly(Rplus.as_expr() ** 2, s))
    if not r2_sum.is_zero:
        raise RuntimeError("Sum resultant quotient not divisible by Rplus(s)^2.")

    # Elimination: pairwise products.
    p = sp.Symbol("p")
    Rtimes = _poly_Rtimes_expected()
    prod_constraint = sp.expand(x**5 * P5.as_expr().subs(x, p / x))
    res_prod = sp.resultant(P5.as_expr(), prod_constraint, x)
    res_prod_poly = sp.Poly(sp.expand(res_prod), p)
    q_prod, r_prod = sp.div(res_prod_poly, sp.Poly(Rtimes.as_expr() ** 2, p))
    if not r_prod.is_zero:
        raise RuntimeError("Product resultant not divisible by Rtimes(p)^2.")

    # Elimination: ordered ratios u = y^2/x.
    u = sp.Symbol("u")
    y = sp.Symbol("y")
    Newman = _poly_Newman_expected()
    res_y = sp.resultant(P5.as_expr().subs(x, y), u * x - y**2, y)
    res_y_poly = sp.Poly(sp.expand(res_y), x, u)
    # full elimination in x
    res_u = sp.resultant(P5.as_expr(), res_y_poly.as_expr(), x)
    res_u_poly = sp.Poly(sp.expand(res_u), u)
    q_u, r_u = sp.div(res_u_poly, sp.Poly(P5.as_expr().subs(x, u), u))
    if not r_u.is_zero:
        raise RuntimeError("Ratio resultant not divisible by P5(u).")
    q_u2, r_u2 = sp.div(q_u, sp.Poly(Newman.as_expr(), u))
    if not r_u2.is_zero:
        raise RuntimeError("Ratio resultant quotient not divisible by Newman polynomial.")

    # Discriminants for degree-10 subfields.
    disc_Rplus = int(Rplus.discriminant())
    disc_Rtimes = int(Rtimes.discriminant())
    disc_Rplus_fac = sp.factorint(disc_Rplus)
    disc_Rtimes_fac = sp.factorint(disc_Rtimes)

    # Sanity-check the main discriminant value (hard failure if mismatch).
    if disc_P5 != -16107783120:
        raise RuntimeError(f"Unexpected Disc(P5)={disc_P5}.")

    out = Payload(
        P5=sp.sstr(P5.as_expr()),
        disc_P5=int(disc_P5),
        disc_P5_factorization={str(int(k)): int(v) for k, v in sorted(disc_fac.items(), key=lambda kv: int(kv[0]))},
        disc_P5_squarefree_part=int(disc_sqfree),
        ramified_primes_P5=[int(pp) for pp in ramified_primes],
        modp_certificates_P5=certs,
        OK_equals_Zrho5=bool(OK_equals_Zrho5),
        disc_field_K5=int(disc_field),
        index_squared=int(index_squared),
        Rplus=sp.sstr(Rplus.as_expr()),
        Rtimes=sp.sstr(Rtimes.as_expr()),
        Newman_poly=sp.sstr(Newman.as_expr()),
        disc_Rplus=int(disc_Rplus),
        disc_Rtimes=int(disc_Rtimes),
        disc_Rplus_factorization={str(int(k)): int(v) for k, v in sorted(disc_Rplus_fac.items(), key=lambda kv: int(kv[0]))},
        disc_Rtimes_factorization={str(int(k)): int(v) for k, v in sorted(disc_Rtimes_fac.items(), key=lambda kv: int(kv[0]))},
    )

    out_path = Path(str(args.json_out)).expanduser()
    if not out_path.is_absolute():
        out_path = export_dir() / out_path

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(asdict(out), indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
