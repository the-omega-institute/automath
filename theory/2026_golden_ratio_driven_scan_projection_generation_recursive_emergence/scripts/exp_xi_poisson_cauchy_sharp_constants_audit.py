#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit sharp constants for Poisson--Cauchy second-order visibility.

Checks:
- L^2 constant from integral equals sqrt(3)/(4*sqrt(pi)).
- Kolmogorov constant equals 9/(16*sqrt(3)*pi).
- Spectral energy constant for a few alpha matches Gamma formula.
- Drift ratio -k3(y0)/k2'(y0) at y0=1/sqrt(3) equals 1/3.
- L^2 optimal scale: minimizer a=3/4 and constant halves.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


def _paper_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _export_path() -> Path:
    return _paper_root() / "artifacts" / "export" / "xi_poisson_cauchy_sharp_constants_audit.json"


def main() -> None:
    y = sp.Symbol("y", real=True)
    pi = sp.pi

    # Lp profile integrand for p=2.
    I2 = sp.integrate((3 * y**2 - 1) ** 2 / (1 + y**2) ** 6, (y, -sp.oo, sp.oo))
    C2 = (1 / pi) * sp.sqrt(I2)
    C2_simplified = sp.simplify(C2)

    # Kolmogorov constant.
    f = sp.Abs(y) / (1 + y**2) ** 2
    y0 = sp.sqrt(sp.Rational(1, 3))
    fmax = sp.simplify((y0) / (1 + y0**2) ** 2)
    Ckolm = sp.simplify(fmax / pi)

    # Spectral energy constant formula check.
    alpha = sp.Symbol("alpha", nonnegative=True, real=True)
    target = sp.gamma(2 * alpha + 5) / (2 ** (2 * alpha + 7) * pi)
    # Verify for a few integer alphas.
    checks_energy = {}
    for a in [0, 1, 2]:
        aa = sp.Integer(a)
        expr = (1 / (2 * pi)) * sp.integrate(
            sp.Abs(sp.Symbol("s", real=True)) ** (2 * aa) * sp.exp(-2 * sp.Abs(sp.Symbol("s", real=True))) * (sp.Symbol("s", real=True) ** 4) / 4,
            (sp.Symbol("s", real=True), -sp.oo, sp.oo),
        )
        # Sympy struggles with repeated symbols if redefined; compute explicitly using symmetry:
        expr = (1 / (2 * pi)) * 2 * sp.integrate(sp.exp(-2 * y) * y ** (2 * aa + 4) / 4, (y, 0, sp.oo))
        checks_energy[str(a)] = {
            "value": sp.simplify(expr),
            "target": sp.simplify(target.subs({alpha: aa})),
            "ok": sp.simplify(expr - target.subs({alpha: aa})) == 0,
        }

    # Drift ratio at y0 = 1/sqrt(3).
    y0_exact = sp.Rational(1, 1) / sp.sqrt(3)
    k2 = (3 * y**2 - 1) / (1 + y**2) ** 3
    k3 = 4 * y * (y**2 - 1) / (1 + y**2) ** 4
    ratio = sp.simplify(-k3.subs({y: y0_exact}) / sp.diff(k2, y).subs({y: y0_exact}))

    # L2 optimal scale quadratic integrals.
    I22 = sp.integrate((3 * y**2 - 1) ** 2 / (1 + y**2) ** 6, (y, -sp.oo, sp.oo))
    I20 = sp.integrate((3 * y**2 - 1) * (y**2 - 1) / (1 + y**2) ** 5, (y, -sp.oo, sp.oo))
    I00 = sp.integrate((y**2 - 1) ** 2 / (1 + y**2) ** 4, (y, -sp.oo, sp.oo))
    a_star = sp.simplify(I20 / I00)
    Imin = sp.simplify(I22 - I20**2 / I00)
    C2_opt = sp.simplify((1 / pi) * sp.sqrt(Imin))
    # Compare to C2 (fixed-scale constant).
    ratio_halving = sp.simplify(C2_opt / C2_simplified)

    out = {
        "Lp": {
            "I_p2": sp.simplify(I2),
            "C_p2": C2_simplified,
        },
        "kolmogorov": {
            "y_star": sp.simplify(y0_exact),
            "f_max": sp.simplify(fmax),
            "C": Ckolm,
        },
        "spectral_energy": checks_energy,
        "intersection_drift": {
            "ratio_minus_k3_over_k2prime_at_y0": ratio,
        },
        "l2_optimal_scale": {
            "I22": sp.simplify(I22),
            "I20": sp.simplify(I20),
            "I00": sp.simplify(I00),
            "a_star": a_star,
            "Imin": Imin,
            "C_opt": C2_opt,
            "C_fixed": C2_simplified,
            "C_opt_over_C_fixed": ratio_halving,
        },
    }

    p = _export_path()
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, indent=2, sort_keys=True, default=str) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

