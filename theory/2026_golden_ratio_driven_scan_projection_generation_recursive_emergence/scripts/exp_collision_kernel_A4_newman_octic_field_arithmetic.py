#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Arithmetic invariants of the Newman-critical octic field for the 4th-collision kernel.

Context (paper-local):
  In parts/subsec__pom-s4.tex (Remark rem:pom-collision-rh-break-a4-threshold),
  the Newman-critical elimination along the negative-real channel introduces the
  sparse degree-8 polynomial

    Z_4(z) = z^8 - 2 z^6 - 2 z^5 - 2 z^4 - 2 z^3 - 2,

  whose (positive) root z_*=-mu_* parameterizes the edge-weight threshold and
  related certificates.

This script audits the associated octic number field K=Q(theta) with theta a
root of Z_4:
  - monogenicity (O_K = Z[theta]) via round-two maximal order algorithm,
  - field discriminant and its factorization (ramified primes),
  - signature and Dirichlet unit rank,
  - prime ideal decompositions above the ramified primes {2,7,23,1151},
  - a two-prime Frobenius cycle-type certificate for Gal(splitting field / Q)=S_8
    using unramified primes 13 (irreducible) and 37 (factor degrees 3+5).

Outputs:
  - artifacts/export/collision_kernel_A4_newman_octic_field_arithmetic.json
"""

from __future__ import annotations

import argparse
import json
import warnings
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp
from sympy.polys.numberfields import prime_decomp
from sympy.polys.numberfields.basis import round_two

from common_paths import export_dir

try:
    from sympy.utilities.exceptions import SymPyDeprecationWarning

    warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)
except Exception:
    # Non-fatal: warning classes may move across SymPy versions.
    pass


def _poly_Z4() -> sp.Poly:
    x = sp.Symbol("x")
    expr = x**8 - 2 * x**6 - 2 * x**5 - 2 * x**4 - 2 * x**3 - 2
    return sp.Poly(sp.expand(expr), x)


def _squarefree_part_from_factorint(fac: Dict[int, int]) -> int:
    out = 1
    for p, e in fac.items():
        if e % 2 == 1:
            out *= int(p)
    return int(out)


def _factor_degrees_mod_p(poly: sp.Poly, p: int) -> Tuple[bool, List[int], List[Tuple[str, int]]]:
    """
    Factor poly modulo p and return:
      (squarefree?, degrees list (desc), [(factor_expr_str, multiplicity), ...]).
    """
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


def _count_real_roots(poly: sp.Poly, *, dps: int) -> int:
    """
    Count real roots of poly by numerical root finding.
    """
    roots = poly.nroots(n=dps, maxsteps=200)
    imag_eps = sp.Float(10) ** (-(dps // 2))
    return int(sum(1 for r in roots if abs(sp.im(r)) <= imag_eps))


def _alpha_vec_to_poly_expr(alpha: List[int], x: sp.Symbol) -> sp.Expr:
    """
    Convert a PrimeIdeal.alpha vector (power-basis coordinates) to a polynomial in x.
    """
    expr = sp.Integer(0)
    for i, a in enumerate(alpha):
        if int(a) == 0:
            continue
        expr += sp.Integer(int(a)) * (x**i)
    return sp.expand(expr)


@dataclass(frozen=True)
class PrimeIdealData:
    gen: str
    e: int
    f: int


@dataclass(frozen=True)
class PrimeDecompData:
    p: int
    ideals: List[PrimeIdealData]


@dataclass(frozen=True)
class FactorModPData:
    p: int
    squarefree: bool
    factor_degrees: List[int]
    factors: List[Tuple[str, int]]


@dataclass(frozen=True)
class Payload:
    polynomial_Z4: str
    # discriminants / index
    disc_poly: int
    disc_poly_factorization: Dict[str, int]
    disc_poly_squarefree_part: int
    disc_field: int
    index_squared: int
    integral_power_basis: bool
    # archimedean data
    signature_r1: int
    signature_r2: int
    unit_rank: int
    # local data
    ramified_primes: List[int]
    prime_decomposition_ramified: List[PrimeDecompData]
    # Galois certificate data (cycle types from unramified primes)
    factorization_mod_p_certificate: List[FactorModPData]


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit arithmetic invariants of the Newman-critical octic field.")
    parser.add_argument("--dps", type=int, default=120, help="Decimal precision for nroots-based signature audit.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_kernel_A4_newman_octic_field_arithmetic.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    dps = int(args.dps)
    if dps < 60:
        raise SystemExit("Require --dps >= 60 for stable signature output.")

    poly = _poly_Z4()
    x = poly.gens[0]

    disc_poly = int(poly.discriminant())
    disc_fac = sp.factorint(disc_poly)
    disc_sqfree = int(_squarefree_part_from_factorint(disc_fac))

    # Maximal order + field discriminant (round-two algorithm).
    ZK, disc_field = round_two(poly)
    disc_field = int(disc_field)
    index_squared = int(disc_poly // disc_field)
    integral_power_basis = bool(index_squared == 1)

    # Signature + unit rank.
    r1 = _count_real_roots(poly, dps=dps)
    r2 = (int(poly.degree()) - int(r1)) // 2
    unit_rank = int(r1 + r2 - 1)

    # Ramified primes from discriminant.
    ramified_primes = sorted({abs(int(p)) for p in disc_fac.keys() if int(p) not in {-1, 1}})

    # Prime ideal decompositions above ramified primes.
    prime_decomposition_ramified: List[PrimeDecompData] = []
    for p in [2, 7, 23, 1151]:
        ideals = prime_decomp(p, T=poly, ZK=ZK, dK=disc_field)
        items: List[PrimeIdealData] = []
        for P in ideals:
            gen_expr = _alpha_vec_to_poly_expr(P.alpha.coeffs, x)
            items.append(PrimeIdealData(gen=sp.sstr(gen_expr), e=int(P.e), f=int(P.f)))
        # stable ordering for downstream diffs
        items.sort(key=lambda it: (-it.e, -it.f, it.gen))
        prime_decomposition_ramified.append(PrimeDecompData(p=int(p), ideals=items))

    # Two-prime cycle-type certificate (unramified primes only).
    certificate: List[FactorModPData] = []
    for p in [13, 37]:
        if p in ramified_primes:
            raise RuntimeError(f"Certificate prime p={p} unexpectedly ramified.")
        squarefree, degs, facs = _factor_degrees_mod_p(poly, p)
        if not squarefree:
            raise RuntimeError(f"Expected Z_4 mod p to be squarefree for unramified p={p}.")
        certificate.append(FactorModPData(p=int(p), squarefree=bool(squarefree), factor_degrees=degs, factors=facs))

    payload = Payload(
        polynomial_Z4=sp.sstr(poly.as_expr()),
        disc_poly=int(disc_poly),
        disc_poly_factorization={str(int(p)): int(e) for p, e in disc_fac.items()},
        disc_poly_squarefree_part=int(disc_sqfree),
        disc_field=int(disc_field),
        index_squared=int(index_squared),
        integral_power_basis=bool(integral_power_basis),
        signature_r1=int(r1),
        signature_r2=int(r2),
        unit_rank=int(unit_rank),
        ramified_primes=[int(p) for p in ramified_primes],
        prime_decomposition_ramified=prime_decomposition_ramified,
        factorization_mod_p_certificate=certificate,
    )

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[A4-newman-octic-field-arithmetic] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

