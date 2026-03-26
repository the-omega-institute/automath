#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Auditable arithmetic certificates for the real-input-40 arity-charge spectral factor P_7.

This script supports Appendix results in:
  sections/appendix/sync_kernel/real_input/app__real-input-40-arity-charge-spectral-curve.tex

We verify, by explicit finite-field and discriminant computations:
  (A) A specialization witness Gal(P_7(Lambda,q)/Q(q)) = S7 via q0=2.
  (B) The hyperelliptic model Y^2=f(Lambda) derived from treating P_7 as a quadratic in q.
  (C) Gal(f/Q) = S10 via a (7,2,1) Frobenius cycle and a transposition inertia witness at 929.
  (D) The discriminant identity Disc_Lambda(P_7) = -4 q D(q) with deg D=17 and Gal(D/Q)=S17.

All outputs are English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir


def _P7(L: sp.Symbol, q: sp.Symbol) -> sp.Expr:
    return sp.expand(
        q * (1 - q)
        + q * (4 * q - 3) * L
        + (-4 * q**2 - q + 1) * L**2
        + (6 * q**2 - 3 * q - 1) * L**3
        + 6 * q * L**4
        + (1 - 5 * q) * L**5
        - 2 * L**6
        + L**7
    )


def _factor_degrees_mod(expr: sp.Expr, var: sp.Symbol, p: int) -> List[int]:
    P = sp.Poly(expr, var, domain=sp.GF(p))
    _, facs = sp.factor_list(P, modulus=p)
    degs: List[int] = []
    for f, e in facs:
        degs.extend([int(f.degree())] * int(e))
    return sorted(degs, reverse=True)


def _gcd_degree_mod(expr: sp.Expr, var: sp.Symbol, p: int) -> int:
    P = sp.Poly(expr, var, domain=sp.GF(p))
    dP = P.diff(var)
    g = P.gcd(dP)
    return int(g.degree())


def _v_p(n: int, p: int) -> int:
    n = int(n)
    p = int(p)
    if p <= 1:
        raise ValueError("p must be a prime >= 2")
    n = abs(n)
    v = 0
    while n != 0 and n % p == 0:
        n //= p
        v += 1
    return v


@dataclass(frozen=True)
class CheckResult:
    ok: bool
    details: Dict[str, object]


def _check_p7_s7_witness() -> CheckResult:
    L, q = sp.symbols("Lambda q")
    P7 = _P7(L, q)
    P7_q2 = sp.Poly(P7.subs(q, 2), L, domain=sp.ZZ)
    expr_q2 = sp.expand(P7_q2.as_expr())

    degs_mod23 = _factor_degrees_mod(expr_q2, L, 23)
    fac_mod5 = sp.factor(expr_q2, modulus=5)
    disc_q2 = int(sp.discriminant(P7_q2, L))
    disc_fac = sp.factorint(disc_q2)
    v5 = _v_p(disc_q2, 5)
    gcd_deg_mod5 = _gcd_degree_mod(expr_q2, L, 5)

    ok = (degs_mod23 == [7]) and (v5 == 1) and (gcd_deg_mod5 == 1)
    return CheckResult(
        ok=ok,
        details={
            "P7_q2": str(expr_q2),
            "factor_degrees_mod_23": degs_mod23,
            "factor_mod_5": str(fac_mod5),
            "disc_q2": str(disc_q2),
            "disc_q2_factorint": {str(k): int(v) for k, v in disc_fac.items()},
            "v_5_disc_q2": v5,
            "gcd_degree_mod_5": gcd_deg_mod5,
        },
    )


def _ABC_from_P7_quadratic_in_q() -> Tuple[sp.Expr, sp.Expr, sp.Expr]:
    L, q = sp.symbols("Lambda q")
    P7 = _P7(L, q)
    Pq = sp.Poly(P7, q, domain=sp.ZZ[L])
    A = sp.expand(Pq.coeffs()[0]) if Pq.degree() == 2 else None  # type: ignore[assignment]
    # SymPy returns coeffs in descending order.
    # For degree 2: coeffs() = [A(L), B(L), C(L)].
    coeffs = Pq.all_coeffs()
    if len(coeffs) != 3:
        raise RuntimeError("Unexpected q-degree for P7; expected quadratic in q.")
    A, B, C = map(sp.expand, coeffs)
    return A, B, C


def _check_hyperelliptic_model() -> CheckResult:
    L = sp.Symbol("Lambda")
    A = 6 * L**3 - 4 * L**2 + 4 * L - 1
    B = -5 * L**5 + 6 * L**4 - 3 * L**3 - L**2 - 3 * L + 1
    C = L**7 - 2 * L**6 + L**5 - L**3 + L**2
    f = sp.expand(B**2 - 4 * A * C)

    f_expected = sp.expand(
        L**10
        + 4 * L**9
        - 6 * L**8
        + 26 * L**7
        + 27 * L**6
        - 76 * L**5
        + 63 * L**4
        - 20 * L**3
        + 11 * L**2
        - 6 * L
        + 1
    )

    # Cross-check A,B,C agree with collecting P7 in q.
    A2, B2, C2 = _ABC_from_P7_quadratic_in_q()
    abc_ok = sp.expand(A - A2) == 0 and sp.expand(B - B2) == 0 and sp.expand(C - C2) == 0

    disc_f = int(sp.discriminant(sp.Poly(f, L, domain=sp.ZZ), L))
    disc_fac = sp.factorint(disc_f)

    ok = (sp.expand(f - f_expected) == 0) and abc_ok and (disc_f != 0)
    return CheckResult(
        ok=ok,
        details={
            "A": str(A),
            "B": str(B),
            "C": str(C),
            "ABC_matches_collecting_P7": bool(abc_ok),
            "f": str(f),
            "f_matches_expected": bool(sp.expand(f - f_expected) == 0),
            "disc_f": str(disc_f),
            "disc_f_factorint": {str(k): int(v) for k, v in disc_fac.items()},
        },
    )


def _check_f_s10_certificate() -> CheckResult:
    L = sp.Symbol("Lambda")
    f = sp.expand(
        L**10
        + 4 * L**9
        - 6 * L**8
        + 26 * L**7
        + 27 * L**6
        - 76 * L**5
        + 63 * L**4
        - 20 * L**3
        + 11 * L**2
        - 6 * L
        + 1
    )
    degs_mod19 = _factor_degrees_mod(f, L, 19)
    degs_mod101 = _factor_degrees_mod(f, L, 101)

    disc_f = int(sp.discriminant(sp.Poly(f, L, domain=sp.ZZ), L))
    v929 = _v_p(disc_f, 929)
    gcd_deg_mod929 = _gcd_degree_mod(f, L, 929)

    ok = (degs_mod19 == [10]) and (degs_mod101 == [7, 2, 1]) and (v929 == 1) and (gcd_deg_mod929 == 1)
    return CheckResult(
        ok=ok,
        details={
            "factor_degrees_mod_19": degs_mod19,
            "factor_degrees_mod_101": degs_mod101,
            "v_929_disc_f": v929,
            "gcd_degree_mod_929": gcd_deg_mod929,
        },
    )


def _check_discriminant_D_s17_certificate() -> CheckResult:
    L, q = sp.symbols("Lambda q")
    P7 = _P7(L, q)
    disc_L = sp.discriminant(sp.Poly(P7, L, domain=sp.ZZ[q]), L)
    disc_L = sp.expand(disc_L)

    # Candidate D from explicit coefficients (degree 17).
    D = sp.expand(
        673920 * q**17
        - 8807616 * q**16
        - 19218432 * q**15
        + 103232785 * q**14
        + 148072644 * q**13
        - 579792342 * q**12
        - 358011996 * q**11
        + 1846795172 * q**10
        - 434645304 * q**9
        - 2676443029 * q**8
        + 3188769377 * q**7
        - 1494031454 * q**6
        + 306917977 * q**5
        - 22426584 * q**4
        - 1368265 * q**3
        + 281543 * q**2
        - 8113 * q
        - 283
    )

    disc_id_ok = sp.factor(disc_L + 4 * q * D) == 0

    degs_mod157 = _factor_degrees_mod(D, q, 157)
    degs_mod29 = _factor_degrees_mod(D, q, 29)
    disc_D = int(sp.discriminant(sp.Poly(D, q, domain=sp.ZZ), q))
    v929 = _v_p(disc_D, 929)
    gcd_deg_mod929 = _gcd_degree_mod(D, q, 929)

    ok = disc_id_ok and (degs_mod157 == [17]) and (degs_mod29 == [14, 3]) and (v929 == 1) and (gcd_deg_mod929 == 1)
    return CheckResult(
        ok=ok,
        details={
            "Disc_Lambda_P7": str(disc_L),
            "disc_identity_ok": bool(disc_id_ok),
            "D": str(D),
            "factor_degrees_mod_157": degs_mod157,
            "factor_degrees_mod_29": degs_mod29,
            "v_929_disc_D": v929,
            "gcd_degree_mod_929": gcd_deg_mod929,
        },
    )


def _check_projective_infty_tacnode_and_infty_fiber() -> CheckResult:
    x, t = sp.symbols("x t")
    L, q = sp.symbols("Lambda q")
    P7 = _P7(L, q)

    H = sp.expand(x**7 * t**2 * P7.subs({L: 1 / x, q: 1 / t}))

    # Weighted initial form at (x,t)=(0,0) with w(x)=1, w(t)=2.
    poly_xt = sp.Poly(H, x, t, domain=sp.ZZ)
    min_w = None
    init = 0
    for (ex, et), coeff in poly_xt.terms():
        w = int(ex) + 2 * int(et)
        if min_w is None or w < min_w:
            min_w = w
            init = 0
        if w == min_w:
            init += coeff * x ** int(ex) * t ** int(et)
    init = sp.expand(init)

    init_fac = sp.factor(init)

    H_t = sp.diff(H, t)
    H_t0 = sp.Poly(sp.expand(H_t.subs(t, 0)), x, domain=sp.ZZ)
    H0 = sp.Poly(sp.expand(H.subs(t, 0)), x, domain=sp.ZZ)

    # Identify the cubic factor governing the three finite-Lambda points over q=∞.
    cubic = sp.Poly(x**3 - 4 * x**2 + 4 * x - 6, x, domain=sp.ZZ)
    # Check H(x,0) equals -x^4 * cubic.
    infty_fiber_ok = sp.expand(H0.as_expr() + x**4 * cubic.as_expr()) == 0
    # Check those three points are not critical for the projection (Ht != 0 there): gcd(cubic, Ht(x,0))=1.
    gcd_ok = sp.gcd(cubic, H_t0).degree() == 0

    ok = (sp.expand(init - (t**2 - 5 * t * x**2 + 6 * x**4)) == 0) and infty_fiber_ok and gcd_ok
    return CheckResult(
        ok=ok,
        details={
            "H": str(H),
            "weighted_initial_form_wx1_wt2": str(init),
            "weighted_initial_form_factor": str(init_fac),
            "H_x0_t0": str(H0.as_expr()),
            "infty_fiber_factor_cubic": str(cubic.as_expr()),
            "infty_fiber_factorization_ok": bool(infty_fiber_ok),
            "Ht_x_t0": str(H_t0.as_expr()),
            "gcd_cubic_Ht0_is_1": bool(gcd_ok),
        },
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit arithmetic certificates for P7 spectral curve and Galois phenomena.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_real_input_40_p7_spectral_curve_galois_audit.json"),
    )
    args = parser.parse_args()

    p7_s7 = _check_p7_s7_witness()
    hyp = _check_hyperelliptic_model()
    f_s10 = _check_f_s10_certificate()
    disc_s17 = _check_discriminant_D_s17_certificate()
    infty = _check_projective_infty_tacnode_and_infty_fiber()

    out = {
        "schema_version": 1,
        "checks": {
            "P7_specialization_S7_witness_q0_eq_2": asdict(p7_s7),
            "hyperelliptic_model_Y2_eq_f": asdict(hyp),
            "f_galois_S10_certificate": asdict(f_s10),
            "DiscLambda_P7_identity_and_D_galois_S17_certificate": asdict(disc_s17),
            "projective_infty_tacnode_and_infty_fiber_certificate": asdict(infty),
        },
        "overall_ok": bool(p7_s7.ok and hyp.ok and f_s10.ok and disc_s17.ok and infty.ok),
    }

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[p7-spectral-curve-galois-audit] wrote {jout}", flush=True)
    print(f"[p7-spectral-curve-galois-audit] overall_ok={out['overall_ok']}", flush=True)


if __name__ == "__main__":
    main()

