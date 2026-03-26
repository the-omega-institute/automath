#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit Disc_alpha(R(alpha,u)) factorization and Q19 Galois certificates.

We recompute the normalized resultant R(alpha,u) from:
  F(mu,u)=0,
  G(alpha,mu,u):=alpha*mu*F_mu(mu,u)+u*F_u(mu,u)=0,
then compute Disc_alpha(R) in Z[u] and factor it. We verify:
  Disc_alpha(R) = -u^11 (u-1) P10(u) Q19(u)^2,
with explicit Q19. We also provide mod-p factor patterns for S19.

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


def _u_adic_valuation(poly_u: sp.Poly) -> int:
    if poly_u.is_zero:
        return 0
    min_j = None
    for mon, coeff in poly_u.terms():
        j = int(mon[0])
        if coeff != 0:
            min_j = j if min_j is None else min(min_j, j)
    return int(min_j or 0)


def _disc_mod_prime(f: sp.Poly, p: int) -> int:
    """
    Discriminant modulo p via resultant:
      Disc(f) = (-1)^{n(n-1)/2} * lc(f)^{-1} * Res(f, f')  (mod p).
    """
    x = f.gens[0]
    n = int(f.degree())
    fp = sp.Poly(f.as_expr(), x, modulus=p)
    dfp = sp.Poly(sp.diff(fp.as_expr(), x), x, modulus=p)
    res = int(sp.resultant(fp, dfp, x)) % p
    lc = int(fp.LC()) % p
    lc_inv = pow(lc, -1, p)
    sign = -1 if ((n * (n - 1) // 2) % 2 == 1) else 1
    return int((sign * res * lc_inv) % p)


def _is_quadratic_residue(a: int, p: int) -> bool:
    a %= p
    if a == 0:
        return True
    return pow(a, (p - 1) // 2, p) == 1


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Disc_alpha(R) factorization and Q19 S19 certificates.")
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(paper_root() / "artifacts" / "export" / "fold_gauge_anomaly_rate_curve_discriminant_q19_audit.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    mu, u, alpha = sp.symbols("mu u alpha")

    # Must match exp_fold_gauge_anomaly_rate_curve_elimination.py
    F = mu**4 - mu**3 - (1 + 2 * u) * mu**2 + (2 * u - u**3) * mu + 2 * u
    G = sp.expand(alpha * mu * sp.diff(F, mu) + u * sp.diff(F, u))

    # Resultant and normalization (u-adic valuation + content gcd), identical to elimination script.
    R_raw = sp.resultant(F, G, mu)
    PR_raw = sp.Poly(R_raw, alpha, u, domain="ZZ")
    Pu_raw = sp.Poly(PR_raw.as_expr(), u, domain=sp.ZZ[alpha])
    v_u = _u_adic_valuation(Pu_raw)
    PR1 = sp.Poly(sp.expand(Pu_raw.as_expr() / (u**v_u)), alpha, u, domain="ZZ")
    content_removed = sp.Integer(sp.gcd_list(list(PR1.coeffs())))
    PR = sp.Poly(sp.expand(PR1.as_expr() / content_removed), alpha, u, domain="ZZ")

    # P10(u) from prop:fold-gauge-anomaly-P10-galois-discriminant
    P10 = (
        27 * u**10
        + 27 * u**9
        - 153 * u**8
        - 163 * u**7
        + 793 * u**6
        + 1061 * u**5
        - 832 * u**4
        - 816 * u**3
        + 1320 * u**2
        - 440 * u
        + 40
    )

    # Disc_alpha(R) in Z[u]
    disc_alpha = sp.discriminant(sp.Poly(PR.as_expr(), alpha), alpha)
    disc_poly = sp.Poly(sp.expand(disc_alpha), u, domain="ZZ")

    # Factorization in Z[u]
    disc_fac = sp.factor(disc_poly.as_expr())

    # Define the explicit Q19(u) asserted in the paper
    Q19 = (
        137781 * u**19
        + 629856 * u**18
        + 934578 * u**17
        - 1546209 * u**16
        - 6187752 * u**15
        + 1402704 * u**14
        + 15349014 * u**13
        - 3368736 * u**12
        - 17688806 * u**11
        + 2216732 * u**10
        + 17425320 * u**9
        - 4765670 * u**8
        - 11620472 * u**7
        + 7448180 * u**6
        + 2529720 * u**5
        - 4736240 * u**4
        + 2386300 * u**3
        - 612800 * u**2
        + 81800 * u
        - 4500
    )

    expected_disc = -u**11 * (u - 1) * P10 * (Q19**2)
    disc_matches = sp.expand(disc_poly.as_expr() - expected_disc) == 0

    # Irreducibility of Q19 over Q and mod-p patterns
    Q19_poly = sp.Poly(Q19, u, domain="ZZ")
    Q19_factor_QQ = sp.factor(Q19_poly.as_expr())
    Q19_irreducible_QQ = Q19_factor_QQ == Q19_poly.as_expr()
    mod_Q19_73 = _factor_degrees_mod(Q19_poly, 73)
    mod_Q19_17 = _factor_degrees_mod(Q19_poly, 17)

    # Discriminant non-square certificate via mod 13 discriminant
    disc_Q19_mod13 = _disc_mod_prime(sp.Poly(Q19, u, domain="ZZ"), 13)
    disc_Q19_mod13_is_square = _is_quadratic_residue(disc_Q19_mod13, 13)

    out: Dict[str, object] = {
        "R": {
            "deg_alpha": int(PR.degree(alpha)),
            "deg_u": int(PR.degree(u)),
            "u_adic_valuation_raw": int(v_u),
            "content_removed": str(content_removed),
        },
        "Disc_alpha_R": {
            "poly": str(disc_poly.as_expr()),
            "factorization": str(disc_fac),
            "matches_expected": bool(disc_matches),
        },
        "P10": {"poly": str(P10)},
        "Q19": {
            "poly": str(Q19_poly.as_expr()),
            "irreducible_over_Q": bool(Q19_irreducible_QQ),
            "mod73": asdict(mod_Q19_73),
            "mod17": asdict(mod_Q19_17),
            "disc_mod13": int(disc_Q19_mod13),
            "disc_mod13_is_square": bool(disc_Q19_mod13_is_square),
        },
        "meta": {"script": Path(__file__).name, "scripts_dir": str(scripts_dir())},
    }

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Hard assertions for pipeline gating
    assert disc_matches, "Disc_alpha(R) does not match -u^11(u-1)P10*Q19^2"
    assert Q19_irreducible_QQ, "Q19 factors over Q unexpectedly"
    assert mod_Q19_73.degrees == [19] and mod_Q19_73.exponents == [1], "Q19 mod 73 not irreducible degree 19"
    assert sorted(mod_Q19_17.degrees) == [8, 11], "Q19 mod 17 does not factor as degrees (11,8)"
    assert disc_Q19_mod13 == 8, "Disc(Q19) mod 13 mismatch"
    assert not disc_Q19_mod13_is_square, "Disc(Q19) mod 13 unexpectedly a square"


if __name__ == "__main__":
    main()

