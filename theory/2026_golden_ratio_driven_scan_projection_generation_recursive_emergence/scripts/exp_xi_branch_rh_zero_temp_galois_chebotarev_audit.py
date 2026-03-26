#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the cubic/quartic/quintic arithmetic data used in the xi conclusions.

This script certifies the explicit arithmetic fingerprints for:
  - the branch cubic Delta(u) = 4 u^3 + 25 u^2 + 88 u + 8,
  - the RH-threshold quintic Q_RH(u) = u^5 + 4 u^4 + 3 u^3 - 96 u^2 - 42 u - 14,
  - the zero-temperature quartic R(y) = y^4 - 6 y^3 + 9 y^2 - y - 1.

It records discriminants, signed squarefree kernels, and finite-field factorization
patterns that witness the cycle types used in the Galois-group proofs.

Output:
  - artifacts/export/xi_branch_rh_zero_temp_galois_chebotarev_audit.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir


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
    sign = -1 if n < 0 else 1
    sf = 1
    for p, e in sp.factorint(abs(n)).items():
        if e % 2 == 1:
            sf *= int(p)
    return sign * sf


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit arithmetic data for the branch cubic, RH quintic, and zero-temperature quartic."
    )
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(export_dir() / "xi_branch_rh_zero_temp_galois_chebotarev_audit.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    u = sp.Symbol("u")
    y = sp.Symbol("y")

    delta_poly = sp.Poly(4 * u**3 + 25 * u**2 + 88 * u + 8, u, domain=sp.ZZ)
    qrh_poly = sp.Poly(u**5 + 4 * u**4 + 3 * u**3 - 96 * u**2 - 42 * u - 14, u, domain=sp.ZZ)
    r_poly = sp.Poly(y**4 - 6 * y**3 + 9 * y**2 - y - 1, y, domain=sp.ZZ)

    disc_delta = int(sp.discriminant(delta_poly.as_expr(), u))
    disc_qrh = int(sp.discriminant(qrh_poly.as_expr(), u))
    disc_r = int(sp.discriminant(r_poly.as_expr(), y))

    mod_r_3 = _factor_degrees_mod(r_poly, 3)
    mod_r_11 = _factor_degrees_mod(r_poly, 11)
    mod_qrh_5 = _factor_degrees_mod(qrh_poly, 5)
    mod_qrh_17 = _factor_degrees_mod(qrh_poly, 17)

    density_all_irreducible = sp.Rational(2, 6) * sp.Rational(6, 24) * sp.Rational(24, 120)
    density_all_split = sp.Rational(1, 6) * sp.Rational(1, 24) * sp.Rational(1, 120)
    density_cubic_irred_quartic_31_quintic_irred = (
        sp.Rational(2, 6) * sp.Rational(8, 24) * sp.Rational(24, 120)
    )

    out: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "sympy": sp.__version__,
        },
        "polynomials": {
            "Delta_u": str(sp.expand(delta_poly.as_expr())),
            "Q_RH_u": str(sp.expand(qrh_poly.as_expr())),
            "R_y": str(sp.expand(r_poly.as_expr())),
        },
        "discriminants": {
            "Delta": {
                "value": disc_delta,
                "factorint_abs": {int(k): int(v) for k, v in sp.factorint(abs(disc_delta)).items()},
                "squarefree_kernel_signed": _squarefree_kernel_signed(disc_delta),
            },
            "Q_RH": {
                "value": disc_qrh,
                "factorint_abs": {int(k): int(v) for k, v in sp.factorint(abs(disc_qrh)).items()},
                "squarefree_kernel_signed": _squarefree_kernel_signed(disc_qrh),
            },
            "R": {
                "value": disc_r,
                "factorint_abs": {int(k): int(v) for k, v in sp.factorint(abs(disc_r)).items()},
                "squarefree_kernel_signed": _squarefree_kernel_signed(disc_r),
            },
        },
        "finite_field_factorizations": {
            "R_mod_3": asdict(mod_r_3),
            "R_mod_11": asdict(mod_r_11),
            "Q_RH_mod_5": asdict(mod_qrh_5),
            "Q_RH_mod_17": asdict(mod_qrh_17),
        },
        "quadratic_resolvent_fields": {
            "Delta": f"Q(sqrt({_squarefree_kernel_signed(disc_delta)}))",
            "R": f"Q(sqrt({_squarefree_kernel_signed(disc_r)}))",
            "Q_RH": f"Q(sqrt({_squarefree_kernel_signed(disc_qrh)}))",
        },
        "density_checks": {
            "all_three_irreducible": {
                "rational": str(density_all_irreducible),
                "numerator": int(sp.numer(density_all_irreducible)),
                "denominator": int(sp.denom(density_all_irreducible)),
            },
            "all_three_split": {
                "rational": str(density_all_split),
                "numerator": int(sp.numer(density_all_split)),
                "denominator": int(sp.denom(density_all_split)),
            },
            "cubic_irred_quartic_31_quintic_irred": {
                "rational": str(density_cubic_irred_quartic_31_quintic_irred),
                "numerator": int(sp.numer(density_cubic_irred_quartic_31_quintic_irred)),
                "denominator": int(sp.denom(density_cubic_irred_quartic_31_quintic_irred)),
            },
        },
    }

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    assert disc_delta == -(2**5) * (5**3) * (11**3), "Unexpected discriminant for Delta(u)"
    assert disc_r == 2777, "Unexpected discriminant for R(y)"
    assert disc_qrh == (2**6) * (3**2) * 7 * 743 * (1693**2), "Unexpected discriminant for Q_RH(u)"

    assert _squarefree_kernel_signed(disc_delta) == -110, "Unexpected quadratic resolvent for Delta(u)"
    assert _squarefree_kernel_signed(disc_r) == 2777, "Unexpected quadratic resolvent for R(y)"
    assert _squarefree_kernel_signed(disc_qrh) == 5201, "Unexpected quadratic resolvent for Q_RH(u)"

    assert mod_r_3.degrees == [4] and mod_r_3.exponents == [1], "R(y) mod 3 should be irreducible"
    assert mod_r_11.degrees == [1, 3] and mod_r_11.exponents == [1, 1], "R(y) mod 11 should have type (3+1)"
    assert mod_qrh_5.degrees == [5] and mod_qrh_5.exponents == [1], "Q_RH(u) mod 5 should be irreducible"
    assert mod_qrh_17.degrees == [1, 1, 3] and mod_qrh_17.exponents == [1, 1, 1], (
        "Q_RH(u) mod 17 should have type (3+1+1)"
    )

    assert density_all_irreducible == sp.Rational(1, 60), "Unexpected irreducible joint density"
    assert density_all_split == sp.Rational(1, 17280), "Unexpected split joint density"
    assert density_cubic_irred_quartic_31_quintic_irred == sp.Rational(1, 45), "Unexpected mixed joint density"

    print(f"[xi-branch-rh-zero-temp-galois] wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()
