#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from math import factorial
from pathlib import Path
from typing import Dict, Optional

import sympy as sp
from sympy.polys.numberfields import galois_group


@dataclass(frozen=True)
class Audit:
    t_value: int
    degree: int
    f_ZZ: str
    irreducible_over_QQ: bool
    mod31_irreducible_over_F31: bool
    mod7_factor_degrees: list[int]
    discriminant_ZZ: str
    discriminant_factorization: Dict[int, int]
    discriminant_is_square: bool
    galois_group_order: Optional[int]
    galois_is_full_symmetric_by_order: Optional[bool]


def paper_root() -> Path:
    return Path(__file__).resolve().parents[1]


def E_t_mu(t: sp.Expr, mu: sp.Symbol) -> sp.Expr:
    return sp.expand(
        2 * t**3 * (mu**2 + 1) ** 2 * (mu**2 - mu - 1) ** 2 + mu**5 * (3 * mu**2 - 2 * mu - 1) ** 3
    )


def poly_is_irreducible_over_QQ(poly: sp.Poly) -> bool:
    coeff, factors = sp.factor_list(poly.as_expr(), gens=poly.gens, domain=sp.QQ)
    _ = coeff
    return len(factors) == 1 and int(factors[0][1]) == 1


def poly_is_irreducible_over_Fp(expr: sp.Expr, var: sp.Symbol, p: int) -> bool:
    poly = sp.Poly(expr, var, modulus=p)
    coeff, factors = sp.factor_list(poly.as_expr(), gens=(var,), modulus=p)
    _ = coeff
    return len(factors) == 1 and int(factors[0][1]) == 1


def factor_degrees_over_Fp(expr: sp.Expr, var: sp.Symbol, p: int) -> list[int]:
    poly = sp.Poly(expr, var, modulus=p)
    coeff, factors = sp.factor_list(poly.as_expr(), gens=(var,), modulus=p)
    _ = coeff
    degs: list[int] = []
    for f, e in factors:
        degs.extend([int(sp.Poly(f, var, modulus=p).degree())] * int(e))
    return sorted(degs)


def discriminant_is_square_from_factorization(fac: Dict[int, int]) -> bool:
    # disc is a square in ZZ iff all prime exponents are even.
    return all((int(e) % 2 == 0) for e in fac.values())


def main() -> None:
    mu = sp.Symbol("mu")
    t_val = 3

    f_expr = E_t_mu(sp.Integer(t_val), mu)
    f_QQ = sp.Poly(f_expr, mu, domain=sp.QQ)

    irreducible_QQ = bool(poly_is_irreducible_over_QQ(f_QQ))
    mod31_irred = bool(poly_is_irreducible_over_Fp(f_expr, mu, 31))
    mod7_degs = factor_degrees_over_Fp(f_expr, mu, 7)

    disc = sp.discriminant(f_expr, mu)
    disc_int = int(sp.Integer(disc))
    disc_fac = {int(p): int(e) for p, e in sp.factorint(abs(disc_int)).items()}
    disc_is_square = bool(discriminant_is_square_from_factorization(disc_fac))

    g_order: Optional[int] = None
    is_full_sym: Optional[bool] = None
    try:
        G, _ = galois_group(f_QQ)
        g_order = int(G.order())
        is_full_sym = g_order == factorial(int(f_QQ.degree()))
    except Exception:
        # Some environments may not support degree-11 galois_group computation.
        g_order = None
        is_full_sym = None

    out = Audit(
        t_value=t_val,
        degree=int(f_QQ.degree()),
        f_ZZ=str(f_expr),
        irreducible_over_QQ=irreducible_QQ,
        mod31_irreducible_over_F31=mod31_irred,
        mod7_factor_degrees=mod7_degs,
        discriminant_ZZ=str(disc_int),
        discriminant_factorization=disc_fac,
        discriminant_is_square=disc_is_square,
        galois_group_order=g_order,
        galois_is_full_symmetric_by_order=is_full_sym,
    )

    export_path = paper_root() / "artifacts" / "export" / "xi_degree11_Et_S11_audit.json"
    export_path.parent.mkdir(parents=True, exist_ok=True)
    export_path.write_text(json.dumps(asdict(out), indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

