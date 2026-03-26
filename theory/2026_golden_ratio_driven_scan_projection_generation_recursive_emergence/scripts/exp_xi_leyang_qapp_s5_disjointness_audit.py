#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit Q_app(y) S5 certificate and disjointness from Q5(y).

This script checks fingerprints used in the xi section:
  - mod-11 irreducibility for a 5-cycle witness,
  - mod-109 repeated factor pattern for a transposition witness,
  - quadratic resolvent mismatch via discriminant squarefree kernels (=> disjointness).

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


def _squarefree_kernel_signed(n: int) -> int:
    """Return signed squarefree kernel of an integer n."""
    sign = -1 if n < 0 else 1
    n_abs = abs(n)
    sf = 1
    for p, e in sp.factorint(n_abs).items():
        if e % 2 == 1:
            sf *= int(p)
    return sign * int(sf)


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Q_app S5 and disjointness from Q5.")
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(paper_root() / "artifacts" / "export" / "xi_leyang_qapp_s5_disjointness_audit.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    y = sp.Symbol("y")

    Q_app = 168 * y**5 + 1260 * y**4 - 422 * y**3 - 183 * y**2 - 639 * y - 76
    Q5 = 4096 * y**5 + 5376 * y**4 - 464 * y**3 - 2749 * y**2 - 723 * y + 80

    Qapp_poly = sp.Poly(Q_app, y, domain=sp.ZZ)
    Q5_poly = sp.Poly(Q5, y, domain=sp.ZZ)

    disc_Qapp = int(sp.discriminant(Qapp_poly, y))
    disc_Q5 = int(sp.discriminant(Q5_poly, y))

    disc_Qapp_factors = sp.factorint(abs(disc_Qapp))
    disc_Q5_factors = sp.factorint(abs(disc_Q5))

    mod_Qapp_11 = _factor_degrees_mod(Qapp_poly, 11)
    mod_Qapp_109 = _factor_degrees_mod(Qapp_poly, 109)

    out: Dict[str, object] = {
        "Q_app": {
            "poly": str(sp.expand(Q_app)),
            "disc": int(disc_Qapp),
            "disc_factorint_abs": {int(k): int(v) for k, v in disc_Qapp_factors.items()},
            "disc_squarefree_kernel_signed": int(_squarefree_kernel_signed(disc_Qapp)),
            "mod11": asdict(mod_Qapp_11),
            "mod109": asdict(mod_Qapp_109),
        },
        "Q5": {
            "poly": str(sp.expand(Q5)),
            "disc": int(disc_Q5),
            "disc_squarefree_kernel_signed": int(_squarefree_kernel_signed(disc_Q5)),
        },
        "disjointness_quadratic_kernels": {
            "equal": bool(_squarefree_kernel_signed(disc_Qapp) == _squarefree_kernel_signed(disc_Q5)),
        },
        "meta": {
            "script": Path(__file__).name,
            "scripts_dir": str(scripts_dir()),
        },
    }

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Hard assertions for pipeline gating (S5 certificate style)
    assert mod_Qapp_11.degrees == [5] and mod_Qapp_11.exponents == [1], "Q_app mod 11 not irreducible degree 5"
    assert 2 in mod_Qapp_109.exponents, "Q_app mod 109 does not show a repeated factor"
    assert (disc_Qapp != 0) and (disc_Q5 != 0), "Discriminants should be nonzero"
    assert (109 in disc_Qapp_factors) and (disc_Qapp_factors[109] % 2 == 1), "Disc(Q_app) should have odd 109-adic valuation"
    assert 109 not in disc_Q5_factors, "Disc(Q5) unexpectedly contains 109"


if __name__ == "__main__":
    main()

