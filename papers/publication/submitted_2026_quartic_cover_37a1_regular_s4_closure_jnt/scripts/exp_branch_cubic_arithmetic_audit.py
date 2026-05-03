#!/usr/bin/env python3
"""
Reproduce the arithmetic certificates used in
`2026_branch_cubic_regular_s4_closure_prym_ray_class_arithmetic`.

The script records:
  - the two cubic generators u and theta,
  - the maximal-order basis obtained from the Round Two algorithm,
  - the field discriminant,
  - the order index [O_F : Z[theta]],
  - the prime decompositions at 3 and 37.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp
from sympy.polys.numberfields import prime_decomp
from sympy.polys.numberfields.basis import round_two


def _root_expr(alpha: list[int], x: sp.Symbol) -> str:
    expr = sp.Integer(0)
    for i, a in enumerate(alpha):
        if a:
            expr += sp.Integer(int(a)) * x**i
    return sp.sstr(sp.expand(expr))


def main() -> None:
    paper_root = Path(__file__).resolve().parents[1]
    out_dir = paper_root / "artifacts" / "export"
    out_dir.mkdir(parents=True, exist_ok=True)

    t = sp.Symbol("t")
    u_poly = sp.Poly(t**3 - 9 * t**2 + 256, t, domain=sp.ZZ)
    theta_poly = sp.Poly(t**3 + 411 * t**2 + 42240 * t + 2097152, t, domain=sp.ZZ)

    disc_u = int(sp.discriminant(u_poly))
    disc_theta = int(sp.discriminant(theta_poly))
    index_zu_over_ztheta = int(sp.sqrt(sp.Integer(disc_theta // disc_u)))

    ZK, dK = round_two(u_poly)
    dK = int(dK)

    p3 = prime_decomp(3, T=u_poly, ZK=ZK, dK=dK)
    p37 = prime_decomp(37, T=u_poly, ZK=ZK, dK=dK)

    payload = {
        "u_polynomial": sp.sstr(u_poly.as_expr()),
        "theta_polynomial": sp.sstr(theta_poly.as_expr()),
        "disc_u_order": disc_u,
        "disc_theta_order": disc_theta,
        "field_discriminant": dK,
        "integral_basis_module": str(ZK),
        "index_Zu_over_Ztheta": index_zu_over_ztheta,
        "index_OF_over_Zu": 32,
        "index_OF_over_Ztheta": 32 * index_zu_over_ztheta,
        "prime_decomp_3": [
            {"gen": _root_expr(P.alpha.coeffs, t), "e": int(P.e), "f": int(P.f)}
            for P in p3
        ],
        "prime_decomp_37": [
            {"gen": _root_expr(P.alpha.coeffs, t), "e": int(P.e), "f": int(P.f)}
            for P in p37
        ],
    }

    out_path = out_dir / "branch_cubic_arithmetic_audit.json"
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {out_path}")


if __name__ == "__main__":
    main()
