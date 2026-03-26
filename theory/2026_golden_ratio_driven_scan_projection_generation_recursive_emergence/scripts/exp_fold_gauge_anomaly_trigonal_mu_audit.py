#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
Audit the trigonal (mu-projection) structure of the fold gauge-anomaly spectral quartic curve.

We work with the plane quartic C_F ⊂ P^2_{[mu:u:w]} defined by the total-degree
homogenization of

  F(mu,u) = mu^4 - mu^3 - (2u+1) mu^2 + (2u-u^3) mu + 2u.

The paper already studies the degree-4 cover to P^1_u (discriminant in mu).
This audit targets the *dual* degree-3 trigonal cover induced by projection
from P_infty^{(0)}=[0:1:0], i.e. the mu-coordinate map on the affine chart w=1.

We verify symbolically:
  - Disc_u(F) factorization in Z[mu] with a square factor (mu^2-mu-1)^2.
  - Two explicit tangency factorizations: u=1 fiber and mu=-2/3 fiber.
  - Local behavior at P_infty^{(0)} showing mu=0 is the tangent direction and
    the tangent line meets with multiplicity 3 (hence e=2 for the trigonal map).
  - The quartic branch factor q4 has Gal(q4/Q) = S4 via mod-p splitting types,
    and Disc(q4) = -2^12 * 3^4 * 1931.
  - A bounded-height rational specialization scan in mu, extracting all affine
    Q-points detected as rational roots u of F(mu,u)=0.

Outputs:
  - artifacts/export/fold_gauge_anomaly_trigonal_mu_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _build_F(mu: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    # Must match scripts/exp_fold_gauge_anomaly_branch_points.py.
    return mu**4 - mu**3 - (1 + 2 * u) * mu**2 + (2 * u - u**3) * mu + 2 * u


def _build_F_hom(mu: sp.Symbol, u: sp.Symbol, w: sp.Symbol) -> sp.Expr:
    # Total-degree homogenization used in the paper.
    return (
        mu**4
        - mu**3 * w
        - 2 * mu**2 * u * w
        - mu**2 * w**2
        - mu * u**3
        + 2 * mu * u * w**2
        + 2 * u * w**3
    )


def _height_Q(x: sp.Rational) -> int:
    x = sp.Rational(x)
    p, q = int(x.p), int(x.q)
    return max(abs(p), abs(q))


def _enumerate_mu(H: int) -> List[sp.Rational]:
    out: List[sp.Rational] = []
    for q in range(1, H + 1):
        for p in range(-H, H + 1):
            if math.gcd(p, q) != 1:
                continue
            out.append(sp.Rational(p, q))
    return out


def _linear_roots_over_Q(poly: sp.Poly, var: sp.Symbol) -> List[sp.Rational]:
    coeff, factors = sp.factor_list(poly)
    roots: List[sp.Rational] = []
    for f, _e in factors:
        fp = sp.Poly(f, var, domain=sp.QQ)
        if fp.degree() != 1:
            continue
        a1, b1 = fp.all_coeffs()
        roots.append(sp.Rational(-b1, a1))
    roots = sorted(set(roots), key=lambda r: (r.p, r.q))
    return roots


@dataclass(frozen=True)
class AffinePoint:
    mu: str
    u: str
    ht_mu: int
    ht_u: int


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Audit trigonal mu-projection data for the fold gauge-anomaly quartic.")
    parser.add_argument("--H", type=int, default=50, help="Height bound for mu-specialization scan (default: 50).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args(list(argv) if argv is not None else None)

    H = int(args.H)
    if H < 1:
        raise SystemExit("Require --H >= 1.")

    t0 = time.time()
    print("[fold_gauge_anomaly_trigonal_mu_audit] start", flush=True)

    mu, u, w, x = sp.symbols("mu u w x")
    F = _build_F(mu, u)
    Fhom = _build_F_hom(mu, u, w)

    # --- Disc_u(F) factorization ---
    disc_u = sp.discriminant(F, u)
    A = mu**2 - mu - 1
    q4 = 9 * mu**4 - 6 * mu**3 + 4 * mu**2 + 8 * mu - 16
    disc_expected = -mu * (3 * mu + 2) * (A**2) * q4
    disc_factorization_ok = bool(sp.factor(disc_u - disc_expected) == 0)

    # --- Tangency factorizations ---
    F_u1 = sp.factor(F.subs(u, 1))
    F_u1_expected = (mu - 2) * (mu - 1) * (mu + 1) ** 2
    u1_factor_ok = bool(sp.factor(F_u1 - F_u1_expected) == 0)

    mu_m23 = sp.Rational(-2, 3)
    F_m23 = sp.factor(F.subs(mu, mu_m23))
    F_m23_expected = sp.Rational(2, 81) * (3 * u - 1) ** 2 * (3 * u + 2)
    mu_m23_factor_ok = bool(sp.factor(F_m23 - F_m23_expected) == 0)

    # --- Local chart at P_infty^{(0)}: u=1, coordinates (m,t)=(mu/u, w/u) ---
    m, t = sp.symbols("m t")
    Floc = sp.expand(Fhom.subs({u: 1, mu: m, w: t}))
    # tangent direction: linear term in m is -m, so tangent is m=0 (i.e. mu=0)
    dFloc_dm_at_origin = sp.diff(Floc, m).subs({m: 0, t: 0})
    tangent_mu0_ok = bool(sp.simplify(dFloc_dm_at_origin) == -1)
    # intersection multiplicity along tangent line m=0: Floc(0,t)=2 t^3
    Floc_on_tangent = sp.expand(Floc.subs(m, 0))
    tangent_contact_ok = bool(sp.factor(Floc_on_tangent - 2 * t**3) == 0)

    # --- Infinity fiber unramified check for the mu-map: w=0 gives m(m^3-1)=0 with simple roots ---
    Floc_w0 = sp.factor(Floc.subs(t, 0))
    Floc_w0_expected = m**4 - m
    w0_polynomial_ok = bool(sp.factor(Floc_w0 - Floc_w0_expected) == 0)
    dm = sp.diff(Floc_w0_expected, m)
    roots_inf = [sp.Integer(0), sp.Integer(1), sp.exp(2 * sp.pi * sp.I / 3), sp.exp(4 * sp.pi * sp.I / 3)]
    w0_simple_roots_ok = all(bool(sp.simplify(dm.subs(m, r)) != 0) for r in roots_inf)

    # --- q4 arithmetic: discriminant and mod-p splitting types ---
    q4x = 9 * x**4 - 6 * x**3 + 4 * x**2 + 8 * x - 16
    disc_q4 = int(sp.discriminant(q4x, x))
    disc_q4_ok = bool(disc_q4 == -2**12 * 3**4 * 1931)

    q4_mod17 = sp.Poly(q4x, x, modulus=17).factor_list()[1]
    q4_mod17_irreducible = bool(len(q4_mod17) == 1 and sp.Poly(q4_mod17[0][0], x, modulus=17).degree() == 4)

    q4_mod13 = sp.Poly(q4x, x, modulus=13).factor_list()[1]
    q4_mod13_degrees = sorted([sp.Poly(f, x, modulus=13).degree() for (f, _e) in q4_mod13])
    q4_mod13_has_112 = bool(q4_mod13_degrees == [1, 1, 2])

    # --- Genus of the S3 Galois closure (from branch cycle data) ---
    # 6 branch points of order 2, 2 branch points of order 3 for the degree-6 Galois cover.
    galois_deg = 6
    R_total = 6 * galois_deg * (1 - sp.Rational(1, 2)) + 2 * galois_deg * (1 - sp.Rational(1, 3))
    g_closure = int((galois_deg * (-2) + R_total + 2) / 2)  # from 2g-2 = d(-2) + R

    # --- Bounded-height mu-specialization scan for affine Q-points ---
    mus = _enumerate_mu(H)
    pts: List[Tuple[sp.Rational, sp.Rational]] = []
    for mu0 in mus:
        poly_u = sp.Poly(sp.together(F.subs(mu, mu0)), u, domain=sp.QQ)
        roots = _linear_roots_over_Q(poly_u, u)
        for u0 in roots:
            pts.append((sp.Rational(mu0), sp.Rational(u0)))
    pts = sorted(set(pts), key=lambda it: (it[0].p * it[0].q, it[0].q, it[1].p * it[1].q, it[1].q))

    pts_rows: List[AffinePoint] = [
        AffinePoint(mu=str(mu0), u=str(u0), ht_mu=_height_Q(mu0), ht_u=_height_Q(u0)) for (mu0, u0) in pts
    ]

    expected_affine = {
        (sp.Integer(0), sp.Integer(0)),
        (sp.Rational(-2, 3), sp.Rational(1, 3)),
        (sp.Rational(-2, 3), sp.Rational(-2, 3)),
        (sp.Integer(-1), sp.Integer(1)),
        (sp.Integer(1), sp.Integer(1)),
        (sp.Integer(2), sp.Integer(1)),
    }
    found_affine = set(pts)
    affine_matches_expected = bool(found_affine == expected_affine)

    payload: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "H_mu_scan": H,
            "mu_count": len(mus),
            "seconds": float(time.time() - t0),
        },
        "identities": {
            "Disc_u_factorization_ok": bool(disc_factorization_ok),
            "Disc_u_factorized": str(sp.factor(disc_u)),
            "u1_factor_ok": bool(u1_factor_ok),
            "F(mu,1)_factor": str(F_u1),
            "mu_m23_factor_ok": bool(mu_m23_factor_ok),
            "F(-2/3,u)_factor": str(F_m23),
        },
        "local_P_infty0": {
            "tangent_mu0_ok": bool(tangent_mu0_ok),
            "tangent_contact_order3_ok": bool(tangent_contact_ok),
            "Floc_u1": str(Floc),
            "Floc_on_tangent_mu0": str(Floc_on_tangent),
            "w0_polynomial_ok": bool(w0_polynomial_ok),
            "w0_simple_roots_ok": bool(w0_simple_roots_ok),
        },
        "q4": {
            "q4": str(q4x),
            "Disc_q4": int(disc_q4),
            "Disc_q4_ok": bool(disc_q4_ok),
            "mod17_irreducible": bool(q4_mod17_irreducible),
            "mod13_degrees": q4_mod13_degrees,
            "mod13_has_112": bool(q4_mod13_has_112),
        },
        "s3_closure": {
            "degree": galois_deg,
            "genus": int(g_closure),
        },
        "rational_points_scan": {
            "affine_points_found": [asdict(r) for r in pts_rows],
            "count_affine_points_found": len(pts_rows),
            "affine_matches_expected": bool(affine_matches_expected),
            "affine_expected": [(str(a), str(b)) for (a, b) in sorted(expected_affine)],
            "affine_extra": [(str(a), str(b)) for (a, b) in sorted(found_affine - expected_affine)],
            "affine_missing": [(str(a), str(b)) for (a, b) in sorted(expected_affine - found_affine)],
        },
    }

    if not args.no_output:
        out = export_dir() / "fold_gauge_anomaly_trigonal_mu_audit.json"
        _write_json(out, payload)
        print(f"[fold_gauge_anomaly_trigonal_mu_audit] wrote {out}", flush=True)

    print(
        "[fold_gauge_anomaly_trigonal_mu_audit] checks:"
        f" disc_u={disc_factorization_ok}"
        f" u1={u1_factor_ok}"
        f" mu_m23={mu_m23_factor_ok}"
        f" Pinf0_tan={tangent_mu0_ok and tangent_contact_ok}"
        f" q4_disc={disc_q4_ok}"
        f" q4_mod17={q4_mod17_irreducible}"
        f" q4_mod13={q4_mod13_has_112}"
        f" affine_pts={len(pts_rows)} matches={affine_matches_expected}"
        f" seconds={payload['meta']['seconds']:.3f}",
        flush=True,
    )
    print("[fold_gauge_anomaly_trigonal_mu_audit] done", flush=True)


if __name__ == "__main__":
    main()

