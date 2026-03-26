#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit algebraic identities for the S4 -> S3 resolvent chain with
Lee--Yang discriminant, Cardano--Kummer normalization, and branch accounting.

This script verifies symbolic identities that underlie:
  - quartic model F(lambda,y),
  - cubic resolvent R(z,y),
  - discriminant factorization Disc_z(R) = -y(y-1)P(y),
  - Tschirnhaus depression and Cardano parameters,
  - Kummer generator expression after adjoining sqrt(-3),
  - six-point branch pattern and genus values from Riemann--Hurwitz.

It also performs finite rational specializations y=y0 and checks
the Galois group types of F(lambda,y0) and R(z,y0) via SymPy.

Output:
  - artifacts/export/fold_zm_s4_v4_fixedfield_s3_chain_audit.json
"""

from __future__ import annotations

import json
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List

import sympy as sp
from sympy.polys.numberfields import galois_group

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _is_square_rational_integer(n: int) -> bool:
    if n < 0:
        return False
    r = int(sp.integer_nthroot(n, 2)[0])
    return r * r == n


@dataclass(frozen=True)
class SpecializationRow:
    y0: int
    quartic_degree: int
    quartic_galois_order: int
    quartic_galois_is_alt: bool
    quartic_discriminant: int
    cubic_degree: int
    cubic_galois_order: int
    cubic_galois_is_alt: bool
    cubic_discriminant: int
    cubic_discriminant_is_square: bool
    branch_value: bool


def main() -> None:
    lam, y, z, u, t, xi = sp.symbols("lam y z u t xi")
    sqrt_m3 = sp.sqrt(-3)

    F = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)
    P = 256 * y**3 + 411 * y**2 + 165 * y + 32
    R = z**3 + (1 + 2 * y) * z**2 - (1 + 4 * y + 4 * y**2) * z - (1 + 5 * y + 13 * y**2 + 8 * y**3)

    disc_R = sp.expand(sp.discriminant(R, z))
    delta_expected = sp.expand(-y * (y - 1) * P)
    disc_identity_ok = sp.expand(disc_R - delta_expected) == 0

    delta_poly = sp.Poly(delta_expected, y, domain=sp.QQ)
    delta_gcd = sp.gcd(delta_poly, sp.Poly(sp.diff(delta_expected, y), y, domain=sp.QQ))
    finite_branch_simple = delta_gcd.degree() == 0
    finite_branch_count = int(delta_poly.degree())
    total_branch_count = finite_branch_count + 1  # + infinity

    # Tschirnhaus: z = t - (1+2y)/3
    depressed = sp.expand(R.subs(z, t - (1 + 2 * y) / 3))
    depressed_poly = sp.Poly(depressed, t, domain=sp.QQ.frac_field(y))
    t2_coeff = sp.expand(depressed_poly.coeff_monomial(t**2))
    p_expr = sp.expand(depressed_poly.coeff_monomial(t))
    q_expr = sp.expand(depressed_poly.coeff_monomial(1))
    p_expected = sp.expand(-sp.Rational(4, 3) * (2 * y + 1) ** 2)
    q_expected = sp.expand(-(128 * y**3 + 219 * y**2 + 69 * y + 16) / 27)

    depression_ok = (t2_coeff == 0) and (sp.expand(p_expr - p_expected) == 0) and (sp.expand(q_expr - q_expected) == 0)

    # Cardano radicand relation
    cardano_base = sp.expand((q_expected / 2) ** 2 + (p_expected / 3) ** 3 - y * (y - 1) * P / 108)
    cardano_base_ok = cardano_base == 0
    cardano_u = sp.expand((q_expected / 2) ** 2 + (p_expected / 3) ** 3 + u**2 / 108)
    cardano_u_ok = sp.expand(cardano_u.subs(u**2, -y * (y - 1) * P)) == 0

    # Kummer data over Q(sqrt(-3))(H_LY)
    num_q = 128 * y**3 + 219 * y**2 + 69 * y + 16
    theta_plus = num_q / 54 + u / (6 * sqrt_m3)
    theta_minus = num_q / 54 - u / (6 * sqrt_m3)

    theta_sum_ok = sp.expand(theta_plus + theta_minus + q_expected) == 0
    theta_prod_expr = sp.expand(theta_plus * theta_minus - (-p_expected / 3) ** 3)
    theta_prod_ok = sp.expand(theta_prod_expr.subs(u**2, -y * (y - 1) * P)) == 0

    # Cardano reconstruction z = xi + 4(2y+1)^2/(9xi) - (1+2y)/3 with xi^3 = theta_plus.
    z_cardano = xi + 4 * (2 * y + 1) ** 2 / (9 * xi) - (1 + 2 * y) / 3
    R_cardano = sp.together(sp.expand(R.subs(z, z_cardano)))
    numer_cardano = sp.expand(R_cardano.as_numer_denom()[0])

    rel_poly = sp.Poly(xi**3 - theta_plus, xi, domain="EX")
    numer_poly = sp.Poly(numer_cardano, xi, domain="EX")
    rem = sp.rem(numer_poly, rel_poly)
    rem_expr = sp.expand(rem.as_expr())
    rem_reduced = sp.expand(rem_expr.subs(u**2, -y * (y - 1) * P))
    cardano_reconstruction_ok = rem_reduced == 0

    # Genus checks from Riemann--Hurwitz:
    #   2g(X)-2 = d*(2g(Y)-2) + sum(e_P-1).
    # E_res -> P^1: d=3, total ramification = 6.
    g_E_res = int((3 * (-2) + 6 + 2) // 2)  # 2g-2 = -6+6 = 0 -> g=1
    # C_S3 -> P^1: d=6, six branch values, each with three points of e=2 => total ramification 18.
    g_C_S3 = int((6 * (-2) + 18 + 2) // 2)  # 2g-2 = -12+18 = 6 -> g=4
    # H_LY: hyperelliptic y(y-1)P(y) degree 5 => genus 2.
    g_H_LY = 2
    # Etale degree-3 cover C_S3 -> H_LY.
    g_C_from_etale = int(3 * (g_H_LY - 1) + 1)

    # Rational specializations for finite evidence of group type.
    sample_y = [2, 3, 5, 7]
    rows: List[SpecializationRow] = []
    all_specializations_ok = True
    for y0 in sample_y:
        F0 = sp.Poly(sp.expand(F.subs(y, y0)), lam, domain=sp.QQ)
        R0 = sp.Poly(sp.expand(R.subs(y, y0)), z, domain=sp.QQ)
        disc_F0 = int(sp.discriminant(F0, lam))
        disc_R0 = int(sp.discriminant(R0, z))
        G4, alt4 = galois_group(F0)
        G3, alt3 = galois_group(R0)
        branch_value = disc_R0 == 0
        disc_R0_square = _is_square_rational_integer(abs(disc_R0))
        row = SpecializationRow(
            y0=int(y0),
            quartic_degree=int(F0.degree()),
            quartic_galois_order=int(G4.order()),
            quartic_galois_is_alt=bool(alt4),
            quartic_discriminant=int(disc_F0),
            cubic_degree=int(R0.degree()),
            cubic_galois_order=int(G3.order()),
            cubic_galois_is_alt=bool(alt3),
            cubic_discriminant=int(disc_R0),
            cubic_discriminant_is_square=bool(disc_R0_square),
            branch_value=bool(branch_value),
        )
        rows.append(row)

        row_ok = (
            row.quartic_degree == 4
            and row.cubic_degree == 3
            and row.quartic_galois_order == 24
            and row.cubic_galois_order == 6
            and (not row.branch_value)
            and (not row.cubic_discriminant_is_square)
        )
        all_specializations_ok = all_specializations_ok and row_ok

    checks = {
        "disc_identity_ok": bool(disc_identity_ok),
        "finite_branch_simple": bool(finite_branch_simple),
        "finite_branch_count_is_5": bool(finite_branch_count == 5),
        "total_branch_count_is_6": bool(total_branch_count == 6),
        "depression_ok": bool(depression_ok),
        "cardano_base_ok": bool(cardano_base_ok),
        "cardano_u_ok": bool(cardano_u_ok),
        "theta_sum_ok": bool(theta_sum_ok),
        "theta_prod_ok": bool(theta_prod_ok),
        "cardano_reconstruction_ok": bool(cardano_reconstruction_ok),
        "genus_E_res_is_1": bool(g_E_res == 1),
        "genus_C_S3_is_4_from_branch_profile": bool(g_C_S3 == 4),
        "genus_C_S3_is_4_from_etale_formula": bool(g_C_from_etale == 4),
        "specializations_ok": bool(all_specializations_ok),
    }
    ok = all(checks.values())

    payload: Dict[str, object] = {
        "ok": bool(ok),
        "polynomials": {
            "F_lambda_y": str(sp.expand(F)),
            "R_z_y": str(sp.expand(R)),
            "P_y": str(sp.expand(P)),
        },
        "symbolic_checks": checks,
        "symbolic_data": {
            "disc_R": str(disc_R),
            "disc_expected": str(delta_expected),
            "depressed_cubic": str(depressed),
            "p": str(p_expr),
            "q": str(q_expr),
            "theta_plus": str(theta_plus),
            "theta_minus": str(theta_minus),
            "cardano_remainder_after_reduction": str(rem_reduced),
        },
        "branch_profile": {
            "finite_branch_count": int(finite_branch_count),
            "total_branch_count_with_infinity": int(total_branch_count),
            "g_H_LY": int(g_H_LY),
            "g_E_res_from_RH": int(g_E_res),
            "g_C_S3_from_RH": int(g_C_S3),
            "g_C_S3_from_etale_degree3": int(g_C_from_etale),
        },
        "specializations": [asdict(r) for r in rows],
    }

    out_path = export_dir() / "fold_zm_s4_v4_fixedfield_s3_chain_audit.json"
    _write_json(out_path, payload)
    print(f"[fold-zm-s4-v4-fixedfield-s3-chain] ok={ok} wrote={out_path}", flush=True)

    if not ok:
        raise RuntimeError("S4/V4 resolvent chain audit failed; inspect JSON payload.")


if __name__ == "__main__":
    main()

