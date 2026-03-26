#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the Lee–Yang branch elimination image in the spectral variable lambda.

This script is English-only by repository convention.

We verify, over Q[lambda]:
  - The exact factorization
      Res_y(Pi(lambda,y), P_LY(y))
        = (16 lambda^3 - 9 lambda^2 + 1)^2
          * (256 lambda^6 - 480 lambda^5 + 201 lambda^4 + 750 lambda^3
             - 921 lambda^2 - 78 lambda + 704),
    where Pi(lambda,y)=lambda^4-lambda^3-(2y+1)lambda^2+lambda+y(y+1)
    and P_LY(y)=256y^3+411y^2+165y+32.

We also verify the refined double-root branch rigidity on the Lee–Yang locus:
  - In the quotient ring Q[y,lambda]/(P_LY(y)), the system Pi=0 and dPi/dlambda=0
    implies the linear relation
        279 lambda + 512 y^2 + 518 y + 5 = 0,
    and the Lee–Yang cubic factor 16 lambda^3 - 9 lambda^2 + 1 reduces to 0.
  - On the full ramification (double-root) locus Disc_lambda(Pi)=0 (i.e. y in {0,1} union roots of P_LY),
    Groebner elimination for the ideal (Pi, dPi/dlambda) yields a global linear eliminant:
        2232 lambda + 16384 y^4 + 8128 y^3 - 14525 y^2 - 5523 y - 2232 = 0.
    Reducing this eliminant modulo P_LY(y) recovers the Lee–Yang branch relation above (up to a scalar factor).
  - Under the elliptic weight convention y = lambda^2 + Y - 1/2 (so Y = y - lambda^2 + 1/2),
    the ramification point over the Lee–Yang cubic field K=Q(y) admits the closed coordinates
        lambda = -(512 y^2 + 518 y + 5)/279,
        Y      =  (512 y^2 + 1262 y + 377)/558,
    and satisfies the ramification equation 4 lambda Y + 3 lambda^2 - 1 = 0.
  - The same Y-coordinate admits the equivalent "ramification-symmetric" closed form
        Y = ((512 y^2 + 518 y + 5)^2 - 25947) / (372 (512 y^2 + 518 y + 5))
    in K (i.e. modulo P_LY(y)).
  - The specialized spectral quartic Pi(lambda,y0) at any Lee–Yang branch value y0 (P_LY(y0)=0)
    factors in K[lambda] as a perfect square times a residual quadratic, with explicit coefficients.
  - A hidden square identity holds in K:
        ((-512 y^2 + 226 y + 367)/93)^2 = 64 y^2 + 64 y + 25.

Outputs:
  - artifacts/export/fold_zm_elliptic_leyang_resy_spectral_decomposition_audit.json
  - sections/generated/eq_fold_zm_elliptic_leyang_resy_spectral_decomposition_audit.tex
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _clear_denominators_linear_in_lam(poly: sp.Poly, lam: sp.Symbol, y: sp.Symbol) -> Tuple[int, sp.Expr]:
    """Given poly(lam,y) with deg_lam==1 over QQ, clear denominators to ZZ and return (content, prim)."""
    if poly.degree(lam) != 1:
        raise ValueError("expected a polynomial linear in lam")
    # Determine a common denominator for all rational coefficients.
    lcm = 1
    for c in poly.coeffs():
        lcm = (lcm * int(sp.denom(c))) // sp.igcd(lcm, int(sp.denom(c)))
    prim = sp.expand(lcm * poly.as_expr())
    P = sp.Poly(prim, lam, y, domain=sp.ZZ)  # coefficients now integral
    content, prim_poly = P.primitive()
    return int(content), prim_poly.as_expr()


@dataclass(frozen=True)
class Payload:
    resultant_ok: bool
    resultant_degree: int
    groebner_linear_ok: bool
    groebner_linear_prim: str
    global_eliminant_y_ok: bool
    global_linear_ok: bool
    global_linear_prim: str
    global_linear_mod_ply_ok: bool
    cubic_reduces_ok: bool
    branch_Y_formula_ok: bool
    branch_Y_alt_formula_ok: bool
    branch_ramification_ok: bool
    branch_curve_eq_ok: bool
    spectral_quartic_factorization_ok: bool
    spectral_quartic_multiplicity2_ok: bool
    hidden_square_ok: bool


def _is_zero_mod_univariate(expr: sp.Expr, *, y: sp.Symbol, modulus: sp.Expr) -> bool:
    """Return True iff expr == 0 in QQ[y]/(modulus)."""
    num = sp.together(expr).as_numer_denom()[0]
    P = sp.Poly(modulus, y, domain=sp.QQ)
    rem = sp.Poly(sp.expand(num), y, domain=sp.QQ).rem(P)
    return bool(rem.is_zero)


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Res_y(Pi,P_LY) factorization and the Lee–Yang double-root branch.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-elliptic-leyang-resy] start", flush=True)

    lam, y = sp.symbols("lam y")
    Pi = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)
    dPi = sp.diff(Pi, lam)
    P_LY = 256 * y**3 + 411 * y**2 + 165 * y + 32

    # --- Global double-root eliminants (Pi, dPi) ---
    # Expect:
    #   - y-eliminant: y(y-1)P_LY(y) (up to unit in QQ)
    #   - linear-in-lam eliminant: 2232 lam + 16384 y^4 + 8128 y^3 - 14525 y^2 - 5523 y - 2232
    G0 = sp.groebner([Pi, dPi], [lam, y], order="lex", domain=sp.QQ)
    global_eliminant_y_ok = False
    global_linear_ok = False
    global_linear_prim = ""
    global_linear_mod_ply_ok = False

    expected_y = sp.factor(y * (y - 1) * P_LY)
    for g in G0.polys:
        Pg = sp.Poly(g, lam, y, domain=sp.QQ)
        if Pg.degree(lam) == 0 and Pg.degree(y) > 0:
            # Compare primitive parts up to sign.
            Pz = sp.Poly(Pg.as_expr(), y, domain=sp.QQ)
            _c1, prim1 = Pz.primitive()
            Pexp = sp.Poly(expected_y, y, domain=sp.QQ)
            _c2, prim2 = Pexp.primitive()
            global_eliminant_y_ok = bool(sp.factor(prim1.as_expr() - prim2.as_expr()) == 0) or bool(
                sp.factor(prim1.as_expr() + prim2.as_expr()) == 0
            )
            break

    target_global = (
        2232 * lam
        + 16384 * y**4
        + 8128 * y**3
        - 14525 * y**2
        - 5523 * y
        - 2232
    )
    for g in G0.polys:
        Pg = sp.Poly(g, lam, y, domain=sp.QQ)
        if Pg.degree(lam) == 1:
            _content, prim = _clear_denominators_linear_in_lam(Pg, lam, y)
            primP = sp.Poly(prim, lam, y, domain=sp.ZZ)
            if primP.LC() < 0:
                prim = -prim
            global_linear_prim = sp.sstr(sp.expand(prim))
            global_linear_ok = bool(sp.factor(sp.expand(prim - target_global)) == 0)

            # Reduction modulo P_LY(y) should match 8*(279 lam + 512 y^2 + 518 y + 5).
            const_part = sp.expand(prim.subs({lam: 0}))
            rem = sp.Poly(const_part, y, domain=sp.ZZ).rem(sp.Poly(P_LY, y, domain=sp.ZZ)).as_expr()
            global_linear_mod_ply_ok = bool(
                sp.factor(sp.expand(rem - 8 * (512 * y**2 + 518 * y + 5))) == 0
            )
            break

    # --- Resultant factorization ---
    Res = sp.factor(sp.resultant(Pi, P_LY, y))
    cubic = 16 * lam**3 - 9 * lam**2 + 1
    sextic = 256 * lam**6 - 480 * lam**5 + 201 * lam**4 + 750 * lam**3 - 921 * lam**2 - 78 * lam + 704
    expected = sp.factor(cubic**2 * sextic)
    resultant_ok = bool(sp.factor(Res - expected) == 0)
    resultant_degree = int(sp.Poly(Res, lam, domain=sp.ZZ).degree())

    # --- Groebner elimination on the Lee–Yang locus ---
    G = sp.groebner([Pi, dPi, P_LY], [lam, y], order="lex", domain=sp.QQ)
    # Expect a basis containing a linear-in-lam eliminant and the cubic relation P_LY(y)=0.
    groebner_linear_ok = False
    groebner_linear_prim = ""
    for g in G.polys:
        Pg = sp.Poly(g, lam, y, domain=sp.QQ)
        if Pg.degree(lam) == 1:
            _content, prim = _clear_denominators_linear_in_lam(Pg, lam, y)
            # Normalize sign to match the paper statement with positive leading coefficient in lam.
            primP = sp.Poly(prim, lam, y, domain=sp.ZZ)
            if primP.LC() < 0:
                prim = -prim
            groebner_linear_prim = sp.sstr(sp.expand(prim))
            target = 279 * lam + 512 * y**2 + 518 * y + 5
            groebner_linear_ok = bool(sp.factor(sp.expand(prim - target)) == 0)
            break

    # The cubic factor should reduce to zero modulo the ideal (Pi, dPi, P_LY).
    rem = G.reduce(cubic)[1]
    cubic_reduces_ok = bool(sp.simplify(rem) == 0)

    # --- Closed coordinate formulas on the Lee–Yang cubic field K=Q(y)/(P_LY) ---
    lam_branch = -sp.Rational(1, 279) * (512 * y**2 + 518 * y + 5)
    Y_branch = sp.simplify(y - lam_branch**2 + sp.Rational(1, 2))
    Y_target = sp.Rational(1, 558) * (512 * y**2 + 1262 * y + 377)
    branch_Y_formula_ok = _is_zero_mod_univariate(Y_branch - Y_target, y=y, modulus=P_LY)

    A = 512 * y**2 + 518 * y + 5
    Y_alt = sp.Rational(1, 372) * (A**2 - 25947) / A
    branch_Y_alt_formula_ok = _is_zero_mod_univariate(Y_branch - Y_alt, y=y, modulus=P_LY)

    branch_ramification_ok = _is_zero_mod_univariate(
        4 * lam_branch * Y_branch + 3 * lam_branch**2 - 1, y=y, modulus=P_LY
    )
    branch_curve_eq_ok = _is_zero_mod_univariate(
        Y_branch**2 - (lam_branch**3 - lam_branch + sp.Rational(1, 4)), y=y, modulus=P_LY
    )

    # --- Exact double-root factorization of the specialized spectral quartic on the Lee–Yang locus ---
    Q2_target = (
        lam**2
        - sp.Rational(1, 279) * (1024 * y**2 + 1036 * y + 289) * lam
        + sp.Rational(1, 279) * (256 * y**2 - 578 * y - 416)
    )

    # In K[lam], Pi(lam,y) = (lam - lam_branch)^2 * Q2_target(lam) (mod P_LY(y)).
    diff_fac = sp.expand(Pi - (lam - lam_branch) ** 2 * Q2_target)
    spectral_quartic_factorization_ok = True
    poly_diff = sp.Poly(diff_fac, lam, domain="EX")
    for c in poly_diff.all_coeffs():
        if not _is_zero_mod_univariate(c, y=y, modulus=P_LY):
            spectral_quartic_factorization_ok = False
            break

    # Confirm multiplicity is exactly 2 (the residual quadratic does not vanish at the branch root).
    Q2_at_branch = sp.simplify(Q2_target.subs({lam: lam_branch}))
    spectral_quartic_multiplicity2_ok = not _is_zero_mod_univariate(Q2_at_branch, y=y, modulus=P_LY)

    s = sp.Rational(1, 93) * (-512 * y**2 + 226 * y + 367)
    hidden_square_ok = _is_zero_mod_univariate(s**2 - (64 * y**2 + 64 * y + 25), y=y, modulus=P_LY)

    payload = Payload(
        resultant_ok=resultant_ok,
        resultant_degree=resultant_degree,
        groebner_linear_ok=groebner_linear_ok,
        groebner_linear_prim=groebner_linear_prim,
        global_eliminant_y_ok=global_eliminant_y_ok,
        global_linear_ok=global_linear_ok,
        global_linear_prim=global_linear_prim,
        global_linear_mod_ply_ok=global_linear_mod_ply_ok,
        cubic_reduces_ok=cubic_reduces_ok,
        branch_Y_formula_ok=branch_Y_formula_ok,
        branch_Y_alt_formula_ok=branch_Y_alt_formula_ok,
        branch_ramification_ok=branch_ramification_ok,
        branch_curve_eq_ok=branch_curve_eq_ok,
        spectral_quartic_factorization_ok=spectral_quartic_factorization_ok,
        spectral_quartic_multiplicity2_ok=spectral_quartic_multiplicity2_ok,
        hidden_square_ok=hidden_square_ok,
    )

    if not args.no_output:
        out_json = export_dir() / "fold_zm_elliptic_leyang_resy_spectral_decomposition_audit.json"
        _write_json(out_json, asdict(payload))

        tex_lines = [
            "% Auto-generated by scripts/exp_fold_zm_elliptic_leyang_resy_spectral_decomposition_audit.py",
            "\\[",
            "2232\\lambda+16384y^{4}+8128y^{3}-14525y^{2}-5523y-2232=0\\quad(\\mathrm{mod}\\ \\Pi,\\partial_{\\lambda}\\Pi).",
            "\\]",
            "\\[",
            "\\mathrm{Res}_{y}\\bigl(\\Pi(\\lambda,y),P_{\\mathrm{LY}}(y)\\bigr)",
            "=(16\\lambda^{3}-9\\lambda^{2}+1)^{2}"
            "\\bigl(256\\lambda^{6}-480\\lambda^{5}+201\\lambda^{4}+750\\lambda^{3}-921\\lambda^{2}-78\\lambda+704\\bigr).",
            "\\]",
            "\\[",
            "279\\lambda+512y^{2}+518y+5=0\\quad(\\mathrm{mod}\\ P_{\\mathrm{LY}}(y)).",
            "\\]",
            "\\[",
            "Y=\\frac{512y^{2}+1262y+377}{558}\\quad(\\mathrm{mod}\\ P_{\\mathrm{LY}}(y)).",
            "\\]",
            "\\[",
            "\\Pi(\\lambda,y)=\\left(\\lambda+\\frac{512y^{2}+518y+5}{279}\\right)^{2}"
            "\\left(\\lambda^{2}-\\frac{1024y^{2}+1036y+289}{279}\\,\\lambda+\\frac{256y^{2}-578y-416}{279}\\right)"
            "\\quad(\\mathrm{mod}\\ P_{\\mathrm{LY}}(y)).",
            "\\]",
            "\\[",
            "\\left(\\frac{-512y^{2}+226y+367}{93}\\right)^{2}=64y^{2}+64y+25\\quad(\\mathrm{mod}\\ P_{\\mathrm{LY}}(y)).",
            "\\]",
            "",
        ]
        out_tex = generated_dir() / "eq_fold_zm_elliptic_leyang_resy_spectral_decomposition_audit.tex"
        _write_text(out_tex, "\n".join(tex_lines))

        print(f"[fold-zm-elliptic-leyang-resy] wrote {out_json}", flush=True)
        print(f"[fold-zm-elliptic-leyang-resy] wrote {out_tex}", flush=True)

    dt = time.time() - t0
    print(
        "[fold-zm-elliptic-leyang-resy] checks:"
        f" res={resultant_ok} deg={resultant_degree}"
        f" globY={global_eliminant_y_ok} globLin={global_linear_ok} globMod={global_linear_mod_ply_ok}"
        f" lin={groebner_linear_ok} cubic_red={cubic_reduces_ok}"
        f" Y={branch_Y_formula_ok} Yalt={branch_Y_alt_formula_ok}"
        f" ram={branch_ramification_ok} curve={branch_curve_eq_ok}"
        f" fac={spectral_quartic_factorization_ok} mult2={spectral_quartic_multiplicity2_ok} sq={hidden_square_ok}"
        f" seconds={dt:.3f}",
        flush=True,
    )
    print("[fold-zm-elliptic-leyang-resy] done", flush=True)


if __name__ == "__main__":
    main()

