#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit delta-plane quintic node tangent discriminants and wreath certificates.

This script checks explicit algebraic fingerprints used for the "node splitting
directions" layer on the plane model C_delta: F_delta(T;y)=0.

It verifies:
  - the tangent-cone discriminant reduction D(y) (a quartic in y),
  - the norm/resultant identity Res_y(Q5(y), D(y)) / 4096^4,
  - the degree-10 elimination polynomial P(z)=Res_y(Q5(y), z^2-D(y)) and its
    explicit even-power coefficient vector,
  - a split prime p=3229 where Q5 splits completely and the Legendre symbols
    of D(y_i) vary across the five roots (excluding the 1-dim trivial submodule).

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


def _roots_mod_linear(poly: sp.Poly, p: int) -> List[int]:
    fp = sp.Poly(poly.as_expr(), poly.gens[0], modulus=p)
    _, factors = fp.factor_list()
    roots: List[int] = []
    x = poly.gens[0]
    for f, e in factors:
        if int(f.degree()) == 1 and int(e) == 1:
            a = int(f.all_coeffs()[0]) % p
            b = int(f.all_coeffs()[1]) % p
            # f(x) = a*x + b, root is -b/a mod p
            inv = pow(a, -1, p)
            roots.append((-b * inv) % p)
    return sorted(roots)


def _legendre_symbol(a: int, p: int) -> int:
    a %= p
    if a == 0:
        return 0
    t = pow(a, (p - 1) // 2, p)
    return -1 if t == p - 1 else int(t)


def _poly_even_coeffs(poly: sp.Poly) -> Dict[int, int]:
    d: Dict[int, int] = {}
    for exp, coeff in poly.as_dict().items():
        (k,) = exp
        d[int(k)] = int(coeff)
    return d


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit delta node tangent discriminants and wreath certificates.")
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(paper_root() / "artifacts" / "export" / "xi_leyang_delta_node_tangent_wreath_audit.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    y, z = sp.symbols("y z")

    # Node-layer quintic Q5(y)
    Q5 = 4096 * y**5 + 5376 * y**4 - 464 * y**3 - 2749 * y**2 - 723 * y + 80

    # Tangent-cone discriminant reduction D(y) for nodes on C_delta (quartic)
    D = 2 * (19072 * y**4 + 51120 * y**3 + 45129 * y**2 + 14759 * y + 1032)

    Q5_poly = sp.Poly(Q5, y)
    D_poly = sp.Poly(D, y)

    # Resultant and normalized norm identity
    res_Q5_D = int(sp.resultant(Q5_poly, D_poly, y))
    norm_Q5_D = sp.Rational(res_Q5_D, 4096**4)

    # Degree-10 elimination polynomial P(z)=Res_y(Q5, z^2 - D(y))
    P10_expr = sp.resultant(Q5_poly, sp.Poly(z**2 - D, y), y)
    P10_poly = sp.Poly(P10_expr, z)
    P10_content, P10_prim = P10_poly.primitive()
    P10_prim = sp.Poly(P10_prim, z)
    if int(P10_prim.LC()) < 0:
        P10_prim = -P10_prim

    # mod p certificates at p=3229
    p = 3229
    mod_Q5_3229 = _factor_degrees_mod(Q5_poly, p)
    roots_3229 = _roots_mod_linear(Q5_poly, p)

    # Evaluate Legendre symbols of D at the five roots
    legendre_at_roots = {r: _legendre_symbol(int(D_poly.eval(r)), p) for r in roots_3229}

    expected_roots = [61, 601, 740, 1696, 1946]
    expected_legendre = {
        61: -1,
        601: +1,
        740: -1,
        1696: -1,
        1946: -1,
    }

    # Expected elimination polynomial coefficients (even powers only).
    # We compare the primitive part (content removed) with positive leading coefficient.
    expected_P10_coeffs = {
        10: 16777216,
        8: -1897083633664,
        6: 7820079733545728,
        4: 8189770598748183555,
        2: 2512279077174710784864,
        0: 245846622126647065658112,
    }
    P10_coeffs = _poly_even_coeffs(P10_prim)

    out: Dict[str, object] = {
        "Q5": {"poly": str(sp.expand(Q5))},
        "D": {"poly": str(sp.expand(D))},
        "resultant_and_norm": {
            "resultant_y_Q5_D": int(res_Q5_D),
            "normalized_norm": str(norm_Q5_D),
        },
        "P10": {
            "content": int(P10_content),
            "primitive_poly": str(P10_prim.as_expr()),
            "degree": int(P10_prim.degree()),
            "coeffs": {int(k): int(v) for k, v in sorted(P10_coeffs.items())},
        },
        "mod_3229": {
            "Q5_factor_degrees": asdict(mod_Q5_3229),
            "roots": roots_3229,
            "legendre_D_at_roots": {int(k): int(v) for k, v in legendre_at_roots.items()},
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
    expected_res_factors = {2: 32, 3: 17, 11: 4, 31: 2, 727: 2}
    assert sp.factorint(abs(res_Q5_D)) == expected_res_factors, "Res_y(Q5,D) factorization mismatch (abs)"
    expected_norm = -sp.Rational((3**17) * (11**4) * (31**2) * (727**2), 2**16)
    assert norm_Q5_D == expected_norm, "Normalized norm mismatch"
    assert mod_Q5_3229.degrees == [1, 1, 1, 1, 1] and mod_Q5_3229.exponents == [1, 1, 1, 1, 1], "Q5 mod 3229 not split into 5 linear factors"
    assert roots_3229 == expected_roots, "Q5 roots mod 3229 mismatch"
    assert {k: legendre_at_roots[k] for k in expected_roots} == expected_legendre, "Legendre symbols of D(y_i) mod 3229 mismatch"
    assert int(P10_prim.degree()) == 10, "P10 degree mismatch"
    # P10 is even in z: only even powers should appear
    assert all(k % 2 == 0 for k in P10_coeffs.keys()), "P10 has odd-power terms"
    # Compare expected even-power coefficient vector
    for k, v in expected_P10_coeffs.items():
        assert P10_coeffs.get(k) == v, f"P10 coefficient mismatch at z^{k}"


if __name__ == "__main__":
    main()

