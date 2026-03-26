#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit real-root bifurcation and y->+infty Puiseux asymptotics for the Fold Z_m
quartic spectral polynomial Pi(lambda,y).

This script is English-only by repository convention.

We verify (with SymPy):
  - The only real finite branch values of the y-projection are {y_LY, 0, 1},
    where y_LY is the unique real root of the Lee–Yang cubic P_LY(y).
  - Hence the number of real roots of Pi(lambda,y)=0 is constant on the four
    real intervals (-inf,y_LY), (y_LY,0), (0,1), (1,inf). We fix the count by a
    Sturm count at one rational sample point in each interval.
  - The unique real root lambda_LY of the associated cubic
      g(lambda)=16 lambda^3 - 9 lambda^2 + 1
    admits a Cardano radical expression with the exact depressed-cubic
    discriminant Delta = 37 / 2^16, forcing sqrt(37) to appear.
  - The two positive real branches for y>1 admit a Puiseux jet at infinity with
    fractional powers y^{±1/4}; we derive the coefficients by solving the
    coefficient-matching system in the t=y^{-1/4} chart and numerically check.

Outputs:
  - artifacts/export/fold_zm_pi_real_bifurcation_asymptotics_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _real_roots_count_sturm(poly_expr: sp.Expr, var: sp.Symbol) -> int:
    P = sp.Poly(sp.expand(poly_expr), var, domain=sp.QQ)
    return int(P.count_roots())  # distinct real roots (Sturm)


def _leyang_real_root(dps: int = 80) -> sp.Float:
    y = sp.Symbol("y")
    P_LY = 256 * y**3 + 411 * y**2 + 165 * y + 32
    roots = sp.Poly(P_LY, y).nroots(n=dps)
    realish: List[sp.Float] = []
    for r in roots:
        if abs(sp.im(r)) < sp.Float(10) ** (-(dps // 2)):
            realish.append(sp.re(r))
    if len(realish) != 1:
        raise RuntimeError(f"Expected exactly one real root of P_LY, got {len(realish)}.")
    return sp.N(realish[0], dps)


def _lambda_leyang_real_root(dps: int = 80) -> sp.Float:
    lam = sp.Symbol("lam")
    g = 16 * lam**3 - 9 * lam**2 + 1
    roots = sp.Poly(g, lam).nroots(n=dps)
    realish: List[sp.Float] = []
    for r in roots:
        if abs(sp.im(r)) < sp.Float(10) ** (-(dps // 2)):
            realish.append(sp.re(r))
    if len(realish) != 1:
        raise RuntimeError(f"Expected exactly one real root of g, got {len(realish)}.")
    return sp.N(realish[0], dps)


def _lambda_leyang_cardano(dps: int = 80) -> Tuple[sp.Float, sp.Expr, sp.Expr]:
    """
    Return (lambda_LY_numeric, A, B) where
      lambda_LY = (3 + A + B) / 16,
      A = real_cuberoot(-101 + 16*sqrt(37)),
      B = real_cuberoot(-101 - 16*sqrt(37)).
    """
    A = sp.real_root(-101 + 16 * sp.sqrt(37), 3)
    B = sp.real_root(-101 - 16 * sp.sqrt(37), 3)
    lam_expr = (sp.Integer(3) + A + B) / sp.Integer(16)
    return sp.N(lam_expr, dps), A, B


def _factor_mod(expr: sp.Expr, var: sp.Symbol, p: int) -> str:
    Pp = sp.Poly(expr, var, modulus=p)
    return str(sp.factor(Pp.as_expr(), modulus=p))


def _puiseux_coeffs_at_infty() -> Dict[str, Dict[str, str]]:
    """
    Solve for coefficients in
      y=t^{-4}, lambda=t^{-2}+c1 t^{-1}+c0+c_{-1} t + c_{-2} t^2 + c_{-3} t^3 + O(t^4).
    Returns coefficients for the two branches (sign of c1).
    """
    t = sp.Symbol("t")
    lam_sym = sp.Symbol("lam")
    y_sym = sp.Symbol("y")

    Pi = lam_sym**4 - lam_sym**3 - (2 * y_sym + 1) * lam_sym**2 + lam_sym + y_sym * (y_sym + 1)

    y_t = t ** (-4)

    c1, c0, c_1 = sp.symbols("c1 c0 c_1")
    c2, c3 = sp.symbols("c2 c3")

    # First stage: solve for (c1,c0,c_1) from low-order coefficients.
    lam_ansatz_1 = t**(-2) + c1 * t**(-1) + c0 + c_1 * t
    expr1 = sp.expand(Pi.subs({lam_sym: lam_ansatz_1, y_sym: y_t}) * t**8)
    poly1 = sp.Poly(expr1, t)
    eqs1 = [sp.Eq(poly1.coeff_monomial(t**k), 0) for k in range(0, 5)]
    sols1 = sp.solve(eqs1, [c1, c0, c_1], dict=True)
    if len(sols1) != 2:
        raise RuntimeError(f"Expected two Puiseux sign branches at infinity, got {len(sols1)}.")

    out: Dict[str, Dict[str, str]] = {}

    for sol in sols1:
        c1v = sp.Rational(sol[c1])
        c0v = sp.Rational(sol[c0])
        c_1v = sp.Rational(sol[c_1])

        # Second stage: solve for (c2,c3) from the next two dependent coefficients.
        lam_ansatz_2 = t**(-2) + c1v * t**(-1) + c0v + c_1v * t + c2 * t**2 + c3 * t**3
        expr2 = sp.expand(Pi.subs({lam_sym: lam_ansatz_2, y_sym: y_t}) * t**8)
        poly2 = sp.Poly(expr2, t)

        coeffs2 = {k: sp.simplify(poly2.coeff_monomial(t**k)) for k in range(0, 9)}
        dep = [k for k, v in coeffs2.items() if v.has(c2) or v.has(c3)]
        dep.sort()
        if len(dep) < 2:
            raise RuntimeError("Unexpected: insufficient dependent coefficients for (c2,c3).")
        eqs2 = [sp.Eq(coeffs2[dep[0]], 0), sp.Eq(coeffs2[dep[1]], 0)]
        sol2 = sp.solve(eqs2, [c2, c3], dict=True)
        if len(sol2) != 1:
            raise RuntimeError(f"Expected unique (c2,c3) solution, got {len(sol2)}.")

        c2v = sp.Rational(sol2[0][c2])
        c3v = sp.Rational(sol2[0][c3])

        tag = "plus" if c1v > 0 else "minus"
        out[tag] = {
            "c1": str(c1v),
            "c0": str(c0v),
            "c_-1": str(c_1v),
            "c_-2": str(c2v),
            "c_-3": str(c3v),
        }

    return out


def _eval_asymptotic(y: float, sign: int) -> float:
    # sign=+1 for the '+' branch; sign=-1 for the '-' branch (coefficient of y^{1/4})
    return (
        y ** 0.5
        + sign * 0.5 * y ** 0.25
        + 0.25
        + sign * (7 / 64) * y ** (-0.25)
        + (37 / 128) * y ** (-0.5)
        - sign * (729 / 4096) * y ** (-0.75)
    )


def _positive_real_roots_numeric(y0: sp.Rational, dps: int = 80) -> Tuple[float, float]:
    lam = sp.Symbol("lam")
    y = sp.Symbol("y")
    Pi = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)
    poly = sp.Poly(sp.expand(Pi.subs(y, y0)), lam, domain=sp.QQ)
    roots = poly.nroots(n=dps)
    rr: List[float] = []
    for r in roots:
        if abs(sp.im(r)) < sp.Float(10) ** (-(dps // 2)):
            rv = float(sp.re(r))
            if rv > 0:
                rr.append(rv)
    rr.sort()
    if len(rr) != 2:
        raise RuntimeError(f"Expected two positive real roots at y={y0}, got {len(rr)} ({rr}).")
    return rr[0], rr[1]


@dataclass(frozen=True)
class Payload:
    y_LY: str
    lambda_LY: str
    lambda_LY_cardano: str
    lambda_LY_cardano_abs_err: str
    y_LY_from_lambda_cardano: str
    y_LY_from_lambda_cardano_abs_err: str
    depressed_cubic_discriminant: str
    depressed_cubic_discriminant_is_37_over_2_16: bool
    P_LY_mod_3: str
    P_LY_mod_31: str
    P_LY_mod_37: str
    sample_real_root_counts: Dict[str, int]
    puiseux_infty_coeffs: Dict[str, Dict[str, str]]
    asymptotic_numeric_check_y: float
    asymptotic_numeric_check_errors: Dict[str, float]


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit real-root bifurcation and y->+infty Puiseux asymptotics for Pi(lambda,y)."
    )
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    parser.add_argument(
        "--out",
        default=str(export_dir() / "fold_zm_pi_real_bifurcation_asymptotics_audit.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-pi-real-bifurcation-asymptotics] start", flush=True)

    lam, y = sp.symbols("lam y")
    Pi = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)
    P_LY = 256 * y**3 + 411 * y**2 + 165 * y + 32

    y_LY = _leyang_real_root(dps=100)
    lam_LY = _lambda_leyang_real_root(dps=120)

    lam_cardano_num, A_expr, B_expr = _lambda_leyang_cardano(dps=120)
    lam_cardano_err = sp.N(abs(lam_cardano_num - lam_LY), 60)

    y_from_lam = (4 * lam**3 - 3 * lam**2 - 2 * lam + 1) / (4 * lam)
    y_cardano = sp.N(y_from_lam.subs(lam, lam_cardano_num), 120)
    y_cardano_err = sp.N(abs(y_cardano - y_LY), 60)

    # Exact Cardano discriminant for the depressed cubic obtained by lambda=t+3/16.
    Delta = sp.Rational(101, 4096) ** 2 + sp.Rational(-9, 256) ** 3
    Delta_simpl = sp.simplify(Delta)
    Delta_target = sp.Rational(37, 2**16)

    # Sample points in the four real intervals.
    samples = {
        "(-inf,y_LY)": sp.Rational(-2, 1),
        "(y_LY,0)": sp.Rational(-1, 2),
        "(0,1)": sp.Rational(1, 2),
        "(1,inf)": sp.Rational(2, 1),
    }
    counts: Dict[str, int] = {}
    for k, y0 in samples.items():
        counts[k] = _real_roots_count_sturm(Pi.subs(y, y0), lam)

    # Puiseux coefficients at infinity and numeric check at y=10000.
    puiseux = _puiseux_coeffs_at_infty()
    y_check = 10000.0
    r_small, r_large = _positive_real_roots_numeric(sp.Rational(10000, 1), dps=120)
    approx_minus = _eval_asymptotic(y_check, sign=-1)
    approx_plus = _eval_asymptotic(y_check, sign=+1)
    errors = {
        "lambda_minus_abs_err": abs(r_small - approx_minus),
        "lambda_plus_abs_err": abs(r_large - approx_plus),
    }

    payload = Payload(
        y_LY=str(y_LY),
        lambda_LY=str(sp.N(lam_LY, 80)),
        lambda_LY_cardano=str(sp.N(lam_cardano_num, 80)),
        lambda_LY_cardano_abs_err=str(lam_cardano_err),
        y_LY_from_lambda_cardano=str(sp.N(y_cardano, 80)),
        y_LY_from_lambda_cardano_abs_err=str(y_cardano_err),
        depressed_cubic_discriminant=str(Delta_simpl),
        depressed_cubic_discriminant_is_37_over_2_16=bool(Delta_simpl == Delta_target),
        P_LY_mod_3=_factor_mod(P_LY, y, 3),
        P_LY_mod_31=_factor_mod(P_LY, y, 31),
        P_LY_mod_37=_factor_mod(P_LY, y, 37),
        sample_real_root_counts=counts,
        puiseux_infty_coeffs=puiseux,
        asymptotic_numeric_check_y=y_check,
        asymptotic_numeric_check_errors=errors,
    )

    if not args.no_output:
        _write_json(Path(args.out), asdict(payload))

    dt = time.time() - t0
    print(f"[fold-zm-pi-real-bifurcation-asymptotics] done elapsed_s={dt:.3f}", flush=True)


if __name__ == "__main__":
    main()

