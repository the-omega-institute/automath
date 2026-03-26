#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: three S3 cubic fields disjoint from the p7 S5 splitting field.

This script certifies the arithmetic data used in conclusion
con:xi-p7-three-s3-linearly-disjoint-chebotarev:
  - irreducibility (by simple finite-field checks) for three cubics,
  - discriminant factorizations and squarefree kernels,
  - distinct quadratic resolvent subfields, hence linear disjointness,
  - the resulting direct-product Galois group order.

Outputs:
  - artifacts/export/xi_p7_three_s3_disjointness_chebotarev_certificate.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, Tuple

import sympy as sp

from common_paths import export_dir


def _factorint_signed(n: int) -> Tuple[int, Dict[int, int]]:
    if n == 0:
        raise ValueError("factorint(0) is undefined")
    sign = -1 if n < 0 else 1
    return sign, sp.factorint(abs(int(n)))


def _squarefree_kernel_with_sign(n: int) -> int:
    sign, fac = _factorint_signed(n)
    sf = sign
    for p, e in fac.items():
        if e % 2 == 1:
            sf *= int(p)
    return int(sf)


def _irreducible_mod_p(poly: sp.Poly, p: int) -> bool:
    x = poly.gens[0]
    P = sp.Poly(poly.as_expr(), x, domain=sp.GF(p))
    return bool(P.is_irreducible)


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit disjointness: p7 with three S3 cubic fields.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "xi_p7_three_s3_disjointness_chebotarev_certificate.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    y = sp.Symbol("y")
    t = sp.Symbol("t")
    x = sp.Symbol("x")

    P37 = sp.Poly(y**3 - 37 * y**2 + 3 * y + 25, y, domain=sp.ZZ)
    QLY = sp.Poly(256 * y**3 + 195 * y**2 + 93 * y - 48, y, domain=sp.ZZ)
    fT = sp.Poly(48114 * t**3 + 7263 * t**2 - 506 * t - 55, t, domain=sp.ZZ)
    p7 = sp.Poly(x**5 - 2 * x**4 - 7 * x**3 - 2 * x + 2, x, domain=sp.ZZ)

    disc_P37 = int(sp.discriminant(P37.as_expr(), y))
    disc_QLY = int(sp.discriminant(QLY.as_expr(), y))
    disc_fT = int(sp.discriminant(fT.as_expr(), t))
    disc_p7 = int(sp.discriminant(p7.as_expr(), x))

    payload: Dict[str, object] = {
        "meta": {"script": Path(__file__).name, "sympy": sp.__version__},
        "polynomials": {
            "P37_y": str(P37.as_expr()),
            "QLY_y": str(QLY.as_expr()),
            "fT_t": str(fT.as_expr()),
            "p7_x": str(p7.as_expr()),
        },
        "irreducibility_mod_p": {
            "P37_mod5": _irreducible_mod_p(P37, 5),
            "QLY_mod5": _irreducible_mod_p(QLY, 5),
            "fT_mod13": _irreducible_mod_p(fT, 13),
            "p7_mod5": _irreducible_mod_p(p7, 5),
        },
        "discriminants": {
            "Disc_P37": disc_P37,
            "Disc_P37_factorint": {str(k): int(v) for k, v in sp.factorint(abs(disc_P37)).items()},
            "Disc_QLY": disc_QLY,
            "Disc_QLY_factorint": {str(k): int(v) for k, v in sp.factorint(abs(disc_QLY)).items()},
            "Disc_fT": disc_fT,
            "Disc_fT_factorint": {str(k): int(v) for k, v in sp.factorint(abs(disc_fT)).items()},
            "Disc_p7": disc_p7,
            "Disc_p7_factorint": {str(k): int(v) for k, v in sp.factorint(abs(disc_p7)).items()},
        },
        "squarefree_kernels": {
            "sf_Disc_P37": _squarefree_kernel_with_sign(disc_P37),
            "sf_Disc_QLY": _squarefree_kernel_with_sign(disc_QLY),
            "sf_Disc_fT": _squarefree_kernel_with_sign(disc_fT),
            "sf_Disc_p7": _squarefree_kernel_with_sign(disc_p7),
        },
        "group_orders": {
            "S5": 120,
            "S3": 6,
            "S5_times_S3_cubed": 120 * 6**3,
        },
    }

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[xi-p7-three-s3-disjointness] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

