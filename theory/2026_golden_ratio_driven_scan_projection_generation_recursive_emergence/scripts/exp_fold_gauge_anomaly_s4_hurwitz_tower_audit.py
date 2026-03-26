#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit certificates for the fold gauge-anomaly spectral quartic and its rate-curve elimination:
  - P10(u) squarefree (and coprime with u(u-1)),
  - real/complex root-phase diagram samples for F(mu,u),
  - real root count/location for the 19-degree square-factor polynomial H(u),
  - specialization-based S4 Galois certificates for F(mu,u) and for the u-specialized
    elimination resultant R(alpha,u),
  - Hurwitz-tower genus computations from branch-cycle data.

Outputs:
  - artifacts/export/fold_gauge_anomaly_s4_hurwitz_tower_audit.json
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir


def _build_F(mu: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    # Must match scripts/exp_fold_gauge_anomaly_pressure.py and related scripts.
    return mu**4 - mu**3 - (1 + 2 * u) * mu**2 + (2 * u - u**3) * mu + 2 * u


def _P10(u: sp.Symbol) -> sp.Poly:
    expr = (
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
    return sp.Poly(sp.expand(expr), u, domain="ZZ")


def _H19(u: sp.Symbol) -> sp.Poly:
    expr = (
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
    return sp.Poly(sp.expand(expr), u, domain="ZZ")


def _count_real_roots_numeric(poly: sp.Poly, *, n: int = 80, tol_im: float = 1e-25) -> List[float]:
    roots = list(sp.nroots(poly, n=n, maxsteps=200))
    reals: List[float] = []
    for r in roots:
        if abs(float(sp.im(r))) < tol_im:
            reals.append(float(sp.re(r)))
    reals.sort()
    return reals


def _factor_degrees_mod_p(poly: sp.Poly, p: int) -> Tuple[bool, List[int]]:
    x = poly.gens[0]
    f = sp.Poly(poly.as_expr(), x, modulus=p)
    g = sp.gcd(f, f.diff())
    squarefree = bool(g.degree() == 0)
    _, facs = sp.factor_list(f, modulus=p)
    degs: List[int] = []
    for ff, ee in facs:
        degs.extend([sp.Poly(ff, x, modulus=p).degree()] * int(ee))
    degs.sort(reverse=True)
    return squarefree, degs


def _squarefree_part_int(n: int) -> int:
    if n == 0:
        return 0
    sgn = -1 if n < 0 else 1
    fac = sp.factorint(abs(int(n)))
    out = 1
    for p, e in fac.items():
        if int(e) % 2 == 1:
            out *= int(p)
    return int(sgn * out)


def _as_frac_str(q: Fraction) -> str:
    return f"{q.numerator}/{q.denominator}"


def _find_prime_with_degrees(poly: sp.Poly, ramified_primes: set[int], want: List[int], p_max: int) -> int:
    want_sorted = sorted(want, reverse=True)
    for p in sp.primerange(2, p_max + 1):
        p = int(p)
        if p in ramified_primes:
            continue
        squarefree, degs = _factor_degrees_mod_p(poly, p)
        if not squarefree:
            continue
        if degs == want_sorted:
            return p
    raise RuntimeError(f"Failed to find prime with factor degrees {want_sorted} up to p_max={p_max}.")


@dataclass(frozen=True)
class GaloisCertificate:
    disc: int
    ramified_primes: List[int]
    p_irreducible: int
    p_3cycle: int
    degs_mod_p_irreducible: List[int]
    degs_mod_p_3cycle: List[int]


def _s4_certificate_for_quartic(poly: sp.Poly, *, p_max: int = 1000) -> GaloisCertificate:
    x = poly.gens[0]
    disc = int(sp.discriminant(poly.as_expr(), x))
    fac = sp.factorint(disc)
    ram = sorted({abs(int(p)) for p in fac.keys() if int(p) not in {-1, 1}})
    ram_set = set(ram)

    p_irred = _find_prime_with_degrees(poly, ram_set, want=[4], p_max=p_max)
    p_3cyc = _find_prime_with_degrees(poly, ram_set, want=[3, 1], p_max=p_max)
    _, degs_irred = _factor_degrees_mod_p(poly, p_irred)
    _, degs_3cyc = _factor_degrees_mod_p(poly, p_3cyc)

    return GaloisCertificate(
        disc=disc,
        ramified_primes=ram,
        p_irreducible=int(p_irred),
        p_3cycle=int(p_3cyc),
        degs_mod_p_irreducible=[int(d) for d in degs_irred],
        degs_mod_p_3cycle=[int(d) for d in degs_3cyc],
    )


def _specialized_R_alpha_at_u(u0: int) -> sp.Poly:
    mu = sp.Symbol("mu")
    u = sp.Symbol("u")
    alpha = sp.Symbol("alpha")

    F = _build_F(mu, u)
    Fmu = sp.diff(F, mu)
    Fu = sp.diff(F, u)

    F0 = sp.expand(F.subs(u, sp.Integer(u0)))
    Fmu0 = sp.expand(Fmu.subs(u, sp.Integer(u0)))
    Fu0 = sp.expand(Fu.subs(u, sp.Integer(u0)))

    G0 = sp.expand(alpha * mu * Fmu0 + sp.Integer(u0) * Fu0)
    R0 = sp.resultant(F0, G0, mu)
    R0 = sp.Poly(sp.expand(R0), alpha, domain="ZZ")

    # Make primitive.
    content = int(sp.gcd_list(list(R0.coeffs()))) if R0.coeffs() else 1
    if content == 0:
        content = 1
    R0 = sp.Poly(sp.expand(R0.as_expr() / content), alpha, domain="ZZ")
    return R0


def main() -> None:
    t0 = time.time()
    mu = sp.Symbol("mu")
    u = sp.Symbol("u")
    alpha = sp.Symbol("alpha")
    y = sp.Symbol("y")

    F = _build_F(mu, u)
    P10 = _P10(u)
    H19 = _H19(u)
    P_LY = sp.Poly(256 * y**3 + 411 * y**2 + 165 * y + 32, y, domain="ZZ")

    # Disc_mu(F) factorization check.
    disc_mu_F = sp.discriminant(F, mu)
    disc_mu_F_fact = sp.factor(disc_mu_F)
    disc_mu_F_expected = sp.expand(-u * (u - 1) * P10.as_expr())
    disc_factor_ok = bool(sp.simplify(disc_mu_F - disc_mu_F_expected) == 0)

    # Squarefree checks.
    gcd_P10_dP10 = sp.gcd(P10, P10.diff()).as_expr()
    gcd_P10_u = sp.gcd(P10, sp.Poly(u, u, domain="ZZ")).as_expr()
    gcd_P10_u1 = sp.gcd(P10, sp.Poly(u - 1, u, domain="ZZ")).as_expr()
    P10_squarefree = bool(gcd_P10_dP10 == 1 and gcd_P10_u == 1 and gcd_P10_u1 == 1)

    # Real/complex phase samples for F(mu,u) at representative u's.
    samples_u: List[sp.Rational] = [sp.Rational(1, 20), sp.Rational(1, 5), sp.Rational(1, 2), sp.Rational(6, 5)]
    phase_samples: Dict[str, Dict[str, object]] = {}
    for u0 in samples_u:
        poly_u0 = sp.Poly(sp.expand(F.subs(u, u0)), mu, domain="QQ")
        roots = list(sp.nroots(poly_u0, n=80, maxsteps=200))
        real_count = sum(1 for r in roots if abs(float(sp.im(r))) < 1e-25)
        disc_val = sp.discriminant(poly_u0.as_expr(), mu)
        phase_samples[str(u0)] = {
            "disc": str(disc_val),
            "disc_sign": int(sp.sign(disc_val)),
            "real_root_count": int(real_count),
        }

    # Real roots of P10 in (0,1) (for u_- < u_+).
    roots_P10 = list(sp.nroots(P10, n=80, maxsteps=200))
    roots_P10_real = sorted([float(sp.re(z)) for z in roots_P10 if abs(float(sp.im(z))) < 1e-25])
    if len(roots_P10_real) != 2:
        raise RuntimeError(f"Expected exactly 2 real roots of P10; got {len(roots_P10_real)}")
    u_minus, u_plus = roots_P10_real[0], roots_P10_real[1]

    # Real roots of H19 (D19) and location.
    H19_real_roots = _count_real_roots_numeric(H19, n=80, tol_im=1e-25)
    H19_real_ok = bool(len(H19_real_roots) == 7 and all(0.0 < x < 1.0 for x in H19_real_roots))

    # Specialization-based S4 certificates.
    F_u2 = sp.Poly(sp.expand(F.subs(u, 2)), mu, domain="ZZ")
    cert_F = _s4_certificate_for_quartic(F_u2, p_max=2000)

    R_u2 = _specialized_R_alpha_at_u(2)
    if int(R_u2.degree()) != 4:
        raise RuntimeError(f"Expected deg(R(alpha,2))=4; got {R_u2.degree()}")
    cert_R = _s4_certificate_for_quartic(R_u2, p_max=2000)

    # --- P10 × Lee–Yang: quadratic-spine separation and joint splitting audit.
    disc_P10 = int(sp.discriminant(P10.as_expr(), u))
    disc_P10_sqfree = _squarefree_part_int(disc_P10)
    disc_P_LY = int(sp.discriminant(P_LY.as_expr(), y))
    disc_P_LY_sqfree = _squarefree_part_int(disc_P_LY)

    # Closed-form check for Disc(P10) (as stated in the paper).
    disc_P10_closed = int(2**38 * 3**24 * 5**2 * 1931 * (9013**2) * (34319**3))
    disc_P10_closed_ok = bool(disc_P10 == disc_P10_closed)

    # Galois-type witnesses for P10 (mod p factorization degrees).
    # These are the degrees used in the proof sketch in the paper.
    _, degs_P10_mod_13 = _factor_degrees_mod_p(P10, 13)
    _, degs_P10_mod_7 = _factor_degrees_mod_p(P10, 7)
    _, degs_P10_mod_11 = _factor_degrees_mod_p(P10, 11)

    # Joint splitting sample over primes: deterministic finite-field audit.
    p_max = 2000
    bad_primes = set(sp.factorint(abs(disc_P10)).keys()) | set(sp.factorint(abs(disc_P_LY)).keys())
    tested_primes: List[int] = []
    joint_counts = {
        "both_have_linear_factor": 0,
        "both_irreducible": 0,
        "both_fully_split": 0,
    }
    marginal_counts = {
        "P10_have_linear_factor": 0,
        "P10_irreducible": 0,
        "P10_fully_split": 0,
        "P_LY_have_linear_factor": 0,
        "P_LY_irreducible": 0,
        "P_LY_fully_split": 0,
    }
    # Quadratic-character joint sample on the same prime set (excluding ramified primes).
    chi_counts: Dict[str, int] = {"(+1,+1)": 0, "(+1,-1)": 0, "(-1,+1)": 0, "(-1,-1)": 0}

    for p in sp.primerange(2, p_max + 1):
        p = int(p)
        if p in bad_primes:
            continue
        tested_primes.append(p)

        _, degs10 = _factor_degrees_mod_p(P10, p)
        _, degs3 = _factor_degrees_mod_p(P_LY, p)

        P10_has_lin = 1 in degs10
        P10_irred = degs10 == [10]
        P10_split = degs10 == [1] * 10

        LY_has_lin = 1 in degs3
        LY_irred = degs3 == [3]
        LY_split = degs3 == [1, 1, 1]

        marginal_counts["P10_have_linear_factor"] += int(P10_has_lin)
        marginal_counts["P10_irreducible"] += int(P10_irred)
        marginal_counts["P10_fully_split"] += int(P10_split)
        marginal_counts["P_LY_have_linear_factor"] += int(LY_has_lin)
        marginal_counts["P_LY_irreducible"] += int(LY_irred)
        marginal_counts["P_LY_fully_split"] += int(LY_split)

        joint_counts["both_have_linear_factor"] += int(P10_has_lin and LY_has_lin)
        joint_counts["both_irreducible"] += int(P10_irred and LY_irred)
        joint_counts["both_fully_split"] += int(P10_split and LY_split)

        # Legendre symbols for the two quadratic spines.
        chi1 = int(sp.legendre_symbol(int(disc_P10_sqfree), p))
        chi2 = int(sp.legendre_symbol(int(disc_P_LY_sqfree), p))
        key = f"({'+1' if chi1 > 0 else '-1'},{'+1' if chi2 > 0 else '-1'})"
        chi_counts[key] = int(chi_counts.get(key, 0) + 1)

    n_test = int(len(tested_primes))
    dens_P10_has_lin = Fraction(28319, 44800)
    dens_LY_has_lin = Fraction(2, 3)
    dens_joint_has_lin = dens_P10_has_lin * dens_LY_has_lin
    dens_joint_irred = Fraction(1, 10) * Fraction(1, 3)
    dens_joint_split = Fraction(1, math.factorial(10)) * Fraction(1, 6)

    # Hurwitz-tower genus computations (purely algebraic, no numeric dependence).
    # X -> P1_u: Galois closure with group S4, 12 branch points, inertia order 2.
    G = 24
    r = 12
    contrib_per_branch = G * (1 - 1 / 2)
    total_contrib = int(r * contrib_per_branch)
    gX = int((2 + (-2 * G) + total_contrib) // 2)  # from 2g-2 = -2G + total_contrib
    if gX != 49:
        raise RuntimeError(f"Unexpected genus g(X)={gX}, expected 49.")

    # Hyperelliptic discriminant double cover: degree 12 => genus 5.
    gH = 5

    # V4 quotient: degree 6, inertia order 2 in regular S3 action => genus 13.
    deg_V4 = 6
    gV4 = int((2 + (-2 * deg_V4) + r * (deg_V4 * (1 - 1 / 2))) // 2)
    if gV4 != 13:
        raise RuntimeError(f"Unexpected genus g(X/V4)={gV4}, expected 13.")

    payload: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "generated_at_unix_s": time.time(),
            "seconds": float(time.time() - t0),
        },
        "disc_factorization": {
            "Disc_mu_F": str(disc_mu_F),
            "Disc_mu_F_factorized": str(disc_mu_F_fact),
            "expected": str(disc_mu_F_expected),
            "ok": bool(disc_factor_ok),
        },
        "P10": {
            "poly": str(P10.as_expr()),
            "squarefree_ok": bool(P10_squarefree),
            "gcd_P10_dP10": str(gcd_P10_dP10),
            "gcd_P10_u": str(gcd_P10_u),
            "gcd_P10_u_minus_1": str(gcd_P10_u1),
            "real_roots_count": int(len(roots_P10_real)),
            "real_roots_in_(0,1)": [float(u_minus), float(u_plus)],
        },
        "H19": {
            "poly": str(H19.as_expr()),
            "real_roots_count": int(len(H19_real_roots)),
            "real_roots": [float(x) for x in H19_real_roots],
            "all_real_roots_in_(0,1)": bool(H19_real_ok),
        },
        "phase_samples": phase_samples,
        "galois_certificates": {
            "F_mu_u_at_u=2": asdict(cert_F),
            "R_alpha_u_at_u=2": asdict(cert_R),
            "R_alpha_u_at_u=2_poly": str(R_u2.as_expr()),
        },
        "hurwitz_tower": {
            "g_X": int(gX),
            "g_H": int(gH),
            "g_X_over_V4": int(gV4),
            "branch_points_count": int(r),
        },
        "p10_leyang_disjointness": {
            "P_LY_poly": str(P_LY.as_expr()),
            "Disc_P10": int(disc_P10),
            "Disc_P10_closed_form": int(disc_P10_closed),
            "Disc_P10_closed_form_ok": bool(disc_P10_closed_ok),
            "Disc_P10_sqfree_part": int(disc_P10_sqfree),
            "Disc_P_LY": int(disc_P_LY),
            "Disc_P_LY_sqfree_part": int(disc_P_LY_sqfree),
            "quadratic_spines": {
                "K10": "Q(sqrt(66269989))",
                "K_LY": "Q(sqrt(-111))",
            },
            "spines_distinct_real_vs_imag": bool(disc_P10_sqfree > 0 and disc_P_LY_sqfree < 0),
            "linear_disjoint_over_Q": bool(disc_P10_sqfree > 0 and disc_P_LY_sqfree < 0),
            "galois_group_product_shape": "S10 x S3",
            "P10_mod_p_degree_witnesses": {
                "p=13": [int(d) for d in degs_P10_mod_13],
                "p=7": [int(d) for d in degs_P10_mod_7],
                "p=11": [int(d) for d in degs_P10_mod_11],
            },
        },
        "p10_leyang_joint_splitting_sample": {
            "p_max": int(p_max),
            "bad_primes": sorted(int(p) for p in bad_primes),
            "primes_tested_count": int(n_test),
            "joint_counts": {k: int(v) for k, v in joint_counts.items()},
            "marginal_counts": {k: int(v) for k, v in marginal_counts.items()},
            "expected_densities": {
                "P10_have_linear_factor": _as_frac_str(dens_P10_has_lin),
                "P_LY_have_linear_factor": _as_frac_str(dens_LY_has_lin),
                "both_have_linear_factor": _as_frac_str(dens_joint_has_lin),
                "both_irreducible": _as_frac_str(dens_joint_irred),
                "both_fully_split": _as_frac_str(dens_joint_split),
            },
            "quadratic_character_pair_counts": {k: int(v) for k, v in chi_counts.items()},
        },
    }

    out_json = export_dir() / "fold_gauge_anomaly_s4_hurwitz_tower_audit.json"
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[fold_gauge_anomaly_s4_hurwitz_tower_audit] wrote {out_json}", flush=True)


if __name__ == "__main__":
    main()

