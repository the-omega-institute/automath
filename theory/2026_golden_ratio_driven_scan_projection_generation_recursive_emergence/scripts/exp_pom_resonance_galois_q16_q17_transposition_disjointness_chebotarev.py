#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit certificates for the resonance-window characteristic polynomials P_16 and P_17:

- irreducibility mod p (transitivity)
- a unique double root mod p with v_p(Disc)=1 (simple ramification -> transposition inertia)
- explicit primes witnessing simultaneous irreducibility and prescribed factor-degree patterns

Outputs:
  - artifacts/export/pom_resonance_galois_q16_q17_transposition_disjointness_chebotarev.json
"""

from __future__ import annotations

import json
import warnings
from dataclasses import asdict, dataclass

import sympy as sp

from common_paths import export_dir

try:
    from sympy.utilities.exceptions import SymPyDeprecationWarning

    warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)
except Exception:
    pass


def poly_P16_P17(q: int) -> sp.Poly:
    lam = sp.Symbol("lam")
    rec_c: dict[int, tuple[int, ...]] = {
        16: (2, 1611, 62312, 2559407, -24862788, -585266591, 62312, -44606766, 24862794, 255692, -124624, 8, -8),
        17: (
            2,
            2599,
            125872,
            6569850,
            -96034590,
            -2764163954,
            -643026032,
            -15022392733,
            769974566,
            15329386299,
            642908352,
            1347896340,
            -673948170,
        ),
    }
    cs = rec_c[int(q)]
    d = len(cs)
    expr = lam**d
    for i, c in enumerate(cs, start=1):
        expr -= sp.Integer(c) * lam ** (d - i)
    return sp.Poly(expr, lam, domain=sp.ZZ)


def vp(n: int, p: int) -> int:
    n = int(n)
    p = int(p)
    if p <= 1:
        raise ValueError("p must be >= 2")
    if n == 0:
        raise ValueError("v_p(0) is undefined in this audit")
    n = abs(n)
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return int(e)


def factor_list_mod_p(poly: sp.Poly, p: int) -> list[dict[str, object]]:
    lam = poly.gens[0]
    f = sp.Poly(poly.as_expr(), lam, modulus=int(p))
    _, facs = sp.factor_list(f, modulus=int(p))
    rows: list[dict[str, object]] = []
    for ff, ee in facs:
        ff_poly = sp.Poly(ff, lam, modulus=int(p))
        rows.append(
            {
                "degree": int(ff_poly.degree()),
                "exponent": int(ee),
                "coeffs_mod_p": [int(c) for c in ff_poly.all_coeffs()],
            }
        )
    rows.sort(key=lambda r: (-(int(r["degree"])), -(int(r["exponent"]))))
    return rows


def factor_degrees_mod_p(poly: sp.Poly, p: int) -> list[int]:
    lam = poly.gens[0]
    f = sp.Poly(poly.as_expr(), lam, modulus=int(p))
    _, facs = sp.factor_list(f, modulus=int(p))
    degs: list[int] = []
    for ff, ee in facs:
        deg = int(sp.Poly(ff, lam, modulus=int(p)).degree())
        degs.extend([deg] * int(ee))
    degs.sort(reverse=True)
    return degs


def is_irreducible_mod_p(poly: sp.Poly, p: int) -> bool:
    lam = poly.gens[0]
    f = sp.Poly(poly.as_expr(), lam, modulus=int(p))
    _, facs = sp.factor_list(f, modulus=int(p))
    return bool(len(facs) == 1 and int(facs[0][1]) == 1 and int(sp.Poly(facs[0][0], lam, modulus=int(p)).degree()) == poly.degree())


@dataclass(frozen=True)
class Audit:
    q: int
    degree: int
    p_irr: int
    irr_mod_p: bool
    disc_vp: int
    p_double: int
    factorization_mod_p_double: list[dict[str, object]]
    repeated_linear_root: int | None
    p_simultaneous_irr_example: int
    simultaneous_irr_at_example: bool
    p_splitting_example: int
    splitting_degrees_at_example: list[int]


def main() -> None:
    lam = sp.Symbol("lam")

    P16 = poly_P16_P17(16)
    P17 = poly_P16_P17(17)

    disc16 = int(sp.discriminant(P16, lam))
    disc17 = int(sp.discriminant(P17, lam))

    # Irreducibility primes already used elsewhere in the manuscript.
    p16_irr = 239
    p17_irr = 31

    # Unique-double-root primes (simple ramification certificates).
    p16_double = 59
    p17_double = 62927

    # Chebotarev explicit examples in the manuscript text.
    p_sim = 4003
    p_split = 1373

    # Identify the repeated linear root for the mod-p double-root prime.
    def repeated_linear_root(poly: sp.Poly, p: int) -> int | None:
        lam0 = poly.gens[0]
        f = sp.Poly(poly.as_expr(), lam0, modulus=int(p))
        g = sp.gcd(f, f.diff())
        if g.degree() == 0:
            return None
        # For the audited cases, g is expected to be linear (a single double root).
        if g.degree() != 1:
            return None
        # g = a*lam + b; root is -b/a in F_p.
        a, b = [int(c) for c in sp.Poly(g, lam0, modulus=int(p)).all_coeffs()]
        a_inv = int(sp.invert(a % p, p))
        r = (-b * a_inv) % int(p)
        return int(r)

    a16 = repeated_linear_root(P16, p16_double)
    a17 = repeated_linear_root(P17, p17_double)

    audits = [
        Audit(
            q=16,
            degree=int(P16.degree()),
            p_irr=int(p16_irr),
            irr_mod_p=bool(is_irreducible_mod_p(P16, p16_irr)),
            disc_vp=int(vp(disc16, p16_double)),
            p_double=int(p16_double),
            factorization_mod_p_double=factor_list_mod_p(P16, p16_double),
            repeated_linear_root=a16,
            p_simultaneous_irr_example=int(p_sim),
            simultaneous_irr_at_example=bool(is_irreducible_mod_p(P16, p_sim) and is_irreducible_mod_p(P17, p_sim)),
            p_splitting_example=int(p_split),
            splitting_degrees_at_example=factor_degrees_mod_p(P16, p_split),
        ),
        Audit(
            q=17,
            degree=int(P17.degree()),
            p_irr=int(p17_irr),
            irr_mod_p=bool(is_irreducible_mod_p(P17, p17_irr)),
            disc_vp=int(vp(disc17, p17_double)),
            p_double=int(p17_double),
            factorization_mod_p_double=factor_list_mod_p(P17, p17_double),
            repeated_linear_root=a17,
            p_simultaneous_irr_example=int(p_sim),
            simultaneous_irr_at_example=bool(is_irreducible_mod_p(P16, p_sim) and is_irreducible_mod_p(P17, p_sim)),
            p_splitting_example=int(p_split),
            splitting_degrees_at_example=factor_degrees_mod_p(P17, p_split),
        ),
    ]

    payload = {
        "checks": {
            "P16_irreducible_mod_239": bool(is_irreducible_mod_p(P16, p16_irr)),
            "P17_irreducible_mod_31": bool(is_irreducible_mod_p(P17, p17_irr)),
            "vp59_Disc_P16": int(vp(disc16, p16_double)),
            "vp62927_Disc_P17": int(vp(disc17, p17_double)),
            "P16_and_P17_irreducible_mod_4003": bool(is_irreducible_mod_p(P16, p_sim) and is_irreducible_mod_p(P17, p_sim)),
            "deg_pattern_P16_mod_1373": factor_degrees_mod_p(P16, p_split),
            "deg_pattern_P17_mod_1373": factor_degrees_mod_p(P17, p_split),
        },
        "audits": [asdict(a) for a in audits],
        # Discriminants are included as strings to avoid JSON integer size issues across toolchains.
        "discriminants": {
            "Disc_P16": str(disc16),
            "Disc_P17": str(disc17),
        },
    }

    out = export_dir() / "pom_resonance_galois_q16_q17_transposition_disjointness_chebotarev.json"
    out.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

    # Minimal stdout summary for human inspection.
    print(f"Wrote {out}")
    print(f"P16 mod 59 repeated root: {a16}")
    print(f"P17 mod 62927 repeated root: {a17}")
    print(f"v_59(Disc(P16))={vp(disc16, 59)}; v_62927(Disc(P17))={vp(disc17, 62927)}")
    print(f"P16,P17 irreducible mod 4003? {is_irreducible_mod_p(P16, 4003) and is_irreducible_mod_p(P17, 4003)}")
    print(f"deg(P16 mod 1373)={factor_degrees_mod_p(P16, 1373)}")
    print(f"deg(P17 mod 1373)={factor_degrees_mod_p(P17, 1373)}")


if __name__ == "__main__":
    main()

