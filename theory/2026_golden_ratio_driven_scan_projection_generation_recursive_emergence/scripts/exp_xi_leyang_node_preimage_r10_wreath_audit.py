#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit node-preimage elimination (R10) and wreath certificates.

This script checks explicit algebraic fingerprints used in the xi Lee--Yang
delta-closure node-preimage layer:
  - resultant_y(Q5(y), Q2(X,y)) equals primitive part of R10(X),
  - an alternative quadratic G_node(X;y) and its discriminant D8(y),
  - mod-p factor patterns for irreducibility (p=17) and Frobenius cycle type
    evidence (p=101 gives degrees 1,1,8),
  - discriminant factorization of R10 and its squarefree kernel,
  - norm identity N_{L/Q}(Delta_X(y)) = -3^25 * 31^10 via a resultant.

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

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


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit R10 node-preimage and wreath certificates.")
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(paper_root() / "artifacts" / "export" / "xi_leyang_node_preimage_r10_wreath_audit.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    X, y = sp.symbols("X y")

    # Node-layer quintic Q5(y)
    Q5 = 4096 * y**5 + 5376 * y**4 - 464 * y**3 - 2749 * y**2 - 723 * y + 80

    # Quadratic mediator in (X,y) for node preimages (Theorem: quadratic mediator)
    b = 65536 * y**4 + 47104 * y**3 - 35392 * y**2 - 22412 * y + 1774
    c = 110592 * y**4 + 67584 * y**3 - 60096 * y**2 - 32496 * y + 3075
    Q2 = 279 * X**2 + b * X + c

    # Degree-10 elimination polynomial R10(X)
    R10 = (
        4096 * X**10
        - 10240 * X**9
        + 4864 * X**8
        + 16384 * X**7
        - 26320 * X**6
        + 2744 * X**5
        + 20657 * X**4
        - 14144 * X**3
        - 4730 * X**2
        + 5768 * X
        + 505
    )

    # Resultant elimination check: Res_y(Q5, Q2) ~ R10 (up to a nonzero integer factor)
    res_y = sp.resultant(sp.Poly(Q5, y), sp.Poly(Q2, y), y)
    res_poly = sp.Poly(res_y, X)
    res_content, res_prim = res_poly.primitive()
    res_prim = sp.Poly(res_prim, X)
    if int(res_prim.LC()) < 0:
        res_prim = -res_prim

    R10_poly = sp.Poly(R10, X)
    _, R10_prim = R10_poly.primitive()
    R10_prim = sp.Poly(R10_prim, X)
    if int(R10_prim.LC()) < 0:
        R10_prim = -R10_prim

    res_matches_R10 = sp.expand(res_prim.as_expr() - R10_prim.as_expr()) == 0

    # Mod-p factor patterns for certificates
    mod_R10_17 = _factor_degrees_mod(sp.Poly(R10, X), 17)
    mod_R10_5 = _factor_degrees_mod(sp.Poly(R10, X), 5)
    mod_R10_101 = _factor_degrees_mod(sp.Poly(R10, X), 101)

    # Alternative quadratic G_node(X;y) and its discriminant certificate
    a_node = 1488 * y + 1023
    b_node = 32768 * y**4 + 23552 * y**3 - 14720 * y**2 - 11020 * y - 322
    c_node = -(8192 * y**4 + 5888 * y**3 - 2192 * y**2 - 1360 * y + 245)
    G_node = sp.expand(a_node * X**2 + b_node * X + c_node)

    D8 = sp.expand(
        67108864 * y**8
        + 96468992 * y**7
        - 25624576 * y**6
        - 85426176 * y**5
        - 15933952 * y**4
        + 20019264 * y**3
        + 7115981 * y**2
        + 186875 * y
        + 69139
    )
    disc_G_node = sp.discriminant(sp.Poly(G_node, X), X)
    disc_matches = sp.expand(disc_G_node - 16 * D8) == 0
    gcd_D8_Q5 = sp.Poly(D8, y).gcd(sp.Poly(Q5, y)).as_expr()

    # Elimination check via alternative quadratic (should also yield R10)
    res_y_gnode = sp.resultant(sp.Poly(Q5, y), sp.Poly(G_node, y), y)
    res_gnode_poly = sp.Poly(res_y_gnode, X)
    res_gnode_content, res_gnode_prim = res_gnode_poly.primitive()
    res_gnode_prim = sp.Poly(res_gnode_prim, X)
    if int(res_gnode_prim.LC()) < 0:
        res_gnode_prim = -res_gnode_prim
    res_gnode_matches_R10 = sp.expand(res_gnode_prim.as_expr() - R10_prim.as_expr()) == 0

    # Discriminant of R10
    disc_R10 = int(sp.discriminant(sp.Poly(R10, X), X))
    disc_R10_factors = sp.factorint(abs(disc_R10))
    sf_kernel = 1
    for p, e in disc_R10_factors.items():
        if int(e) % 2 == 1:
            sf_kernel *= int(p)
    sf_kernel_signed = -sf_kernel if disc_R10 < 0 else sf_kernel

    # Quadratic discriminant Delta_X(y) and its norm over L=Q(y)/Q via a resultant
    Delta_X = sp.expand(b**2 - 4 * 279 * c)
    res_Delta = int(sp.resultant(sp.Poly(Q5, y), sp.Poly(Delta_X, y), y))
    norm_Delta = res_Delta // (4096**8)

    out: Dict[str, object] = {
        "Q5": {
            "poly": str(sp.expand(Q5)),
        },
        "quadratic_mediator": {
            "Q2_X_y": str(sp.expand(Q2)),
            "Delta_X_y": str(Delta_X),
        },
        "R10": {
            "poly": str(sp.expand(R10)),
            "resultant_y_Q5_Q2_content": int(res_content),
            "resultant_y_Q5_Q2_degree": int(res_prim.degree()),
            "resultant_y_Q5_Q2_matches_R10": bool(res_matches_R10),
            "mod5": asdict(mod_R10_5),
            "mod17": asdict(mod_R10_17),
            "mod101": asdict(mod_R10_101),
            "disc": int(disc_R10),
            "disc_factorint_abs": {int(k): int(v) for k, v in disc_R10_factors.items()},
            "disc_squarefree_kernel_signed": int(sf_kernel_signed),
        },
        "G_node_D8": {
            "G_node_X_y": str(G_node),
            "disc_G_node": str(sp.expand(disc_G_node)),
            "D8_y": str(D8),
            "disc_matches_16D8": bool(disc_matches),
            "gcd_D8_Q5": str(gcd_D8_Q5),
            "resultant_y_Q5_G_node_content": int(res_gnode_content),
            "resultant_y_Q5_G_node_degree": int(res_gnode_prim.degree()),
            "resultant_y_Q5_G_node_matches_R10": bool(res_gnode_matches_R10),
        },
        "norm_identity": {
            "resultant_y_Q5_DeltaX": int(res_Delta),
            "normalized_norm": int(norm_Delta),
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
    assert res_matches_R10, "Res_y(Q5, Q2) primitive part does not match R10"
    assert disc_matches, "Disc_X(G_node) != 16*D8"
    assert str(gcd_D8_Q5) == "1", "gcd(D8,Q5) is not 1"
    assert res_gnode_matches_R10, "Res_y(Q5, G_node) primitive part does not match R10"
    assert sorted(mod_R10_5.degrees) == [1, 1, 2, 2, 4], "R10 mod 5 factor degrees not [1,1,2,2,4]"
    assert mod_R10_17.degrees == [10] and mod_R10_17.exponents == [1], "R10 mod 17 not irreducible degree 10"
    assert sorted(mod_R10_101.degrees) == [1, 1, 8], "R10 mod 101 factor degrees not [1,1,8]"
    expected_disc_factors = {
        2: 88,
        3: 17,
        11: 4,
        31: 2,
        727: 2,
        5146068463: 2,
    }
    assert disc_R10_factors == expected_disc_factors, "Disc(R10) factorization mismatch (abs)"
    assert sf_kernel_signed == -3, "Disc(R10) squarefree kernel is not -3"
    assert 37 not in disc_R10_factors, "Unexpected factor 37 in Disc(R10)"
    assert res_Delta % (4096**8) == 0, "Resultant divisibility by 4096^8 failed"
    assert norm_Delta == -(3**25) * (31**10), "Norm identity mismatch"


if __name__ == "__main__":
    main()

