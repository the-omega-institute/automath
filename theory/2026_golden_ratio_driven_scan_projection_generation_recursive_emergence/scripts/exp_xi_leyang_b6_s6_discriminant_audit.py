#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the B6 elimination identity, discriminant, and S6 certificate.

This script checks fingerprints used in the xi section:
  - the exact polynomial identity 93*N(y) + 4*A7(y)*P4(y) = Q5(y)*B6(y),
  - mod-p factor patterns for irreducibility (6-cycle) and a transposition witness,
  - the exact integer discriminant factorization and the ramification prime 59.

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


def _primitive_part(poly: sp.Poly) -> sp.Poly:
    """Return the primitive part of a Z[y] polynomial."""
    _c, prim = poly.primitive()
    return prim


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit B6 identity, discriminant, and S6 certificate.")
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(paper_root() / "artifacts" / "export" / "xi_leyang_b6_s6_discriminant_audit.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    y = sp.Symbol("y")

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
    P4 = 8192 * y**4 + 5888 * y**3 - 3680 * y**2 - 2848 * y + 152
    N = y * (y - 1) * (8 * y - 3) * (16 * y + 11) * (32 * y + 19) * PLY

    numerator = 93 * N + 4 * A7 * P4
    num_poly = sp.Poly(numerator, y, domain=sp.ZZ)
    q5_poly = sp.Poly(Q5, y, domain=sp.ZZ)

    quo, rem = sp.div(num_poly, q5_poly, domain=sp.ZZ)

    B6_expected = sp.Poly(
        360448 * y**6
        + 267264 * y**5
        - 221824 * y**4
        + 18600 * y**3
        + 149481 * y**2
        + 25423 * y
        + 1520,
        y,
        domain=sp.ZZ,
    )

    # Discriminant and exact factor identity as used in the paper.
    disc_B6 = int(sp.discriminant(B6_expected, y))
    p_star = 16381178872545177926239240820863
    disc_factor_target = (2**41) * (3**9) * (31**2) * 59 * p_star

    mod_B6_97 = _factor_degrees_mod(B6_expected, 97)
    mod_B6_59 = _factor_degrees_mod(B6_expected, 59)
    # Extract the unique repeated linear factor root mod 59 (expected y-23).
    fp59 = sp.Poly(B6_expected.as_expr(), y, modulus=59)
    _, factors59 = fp59.factor_list()
    repeated_linear_roots: List[int] = []
    for f, e in factors59:
        if int(f.degree()) == 1 and int(e) >= 2:
            # f(y) = a*y + b over F_p; root is -b/a.
            a = int(f.all_coeffs()[0]) % 59
            b = int(f.all_coeffs()[1]) % 59
            root = (-b * pow(a, -1, 59)) % 59
            repeated_linear_roots.append(int(root))

    out: Dict[str, object] = {
        "B6": {
            "poly": str(B6_expected.as_expr()),
            "disc": int(disc_B6),
            "disc_target": int(disc_factor_target),
            "disc_matches_target": bool(disc_B6 == disc_factor_target),
            "mod97": asdict(mod_B6_97),
            "mod59": asdict(mod_B6_59),
            "repeated_linear_roots_mod59": repeated_linear_roots,
        },
        "identity": {
            "numerator": str(sp.expand(numerator)),
            "q5": str(sp.expand(Q5)),
            "quotient": str(quo.as_expr()),
            "remainder": str(rem.as_expr()),
            "quotient_equals_expected": bool(_primitive_part(quo) == B6_expected),
            "remainder_is_zero": bool(rem.as_expr() == 0),
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
    assert rem.as_expr() == 0, "Q5 does not divide 93*N + 4*A7*P4 over Z"
    assert _primitive_part(quo) == B6_expected, "B6 quotient mismatch"
    assert disc_B6 == disc_factor_target, "B6 discriminant does not match target factorization"
    assert mod_B6_97.degrees == [6] and mod_B6_97.exponents == [1], "B6 mod 97 not irreducible degree 6"
    assert 2 in mod_B6_59.exponents, "B6 mod 59 does not show a repeated factor"
    assert repeated_linear_roots == [23], "Unexpected repeated linear root mod 59 (expected 23)"


if __name__ == "__main__":
    main()

