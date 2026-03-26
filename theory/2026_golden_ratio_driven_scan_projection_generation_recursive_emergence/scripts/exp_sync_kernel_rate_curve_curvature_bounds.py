#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Compute reproducible curvature bounds for the rate curve.

We use the sextic pressure equation F(lambda,u)=0 of the weighted sync-kernel
and the implicit-derivative formulas in the appendix to evaluate P''(theta)
on a theta-grid. This yields numerical lower/upper bounds for P''(theta)
and thus bounds for I''(alpha)=1/P''(theta(alpha)).

This is a data certificate (reproducible, parameter-free) for strict convexity
in the energy direction: P''(theta)>0 on a wide real range.

Outputs:
  - artifacts/export/sync_kernel_rate_curve_curvature_bounds.json
  - sections/generated/tab_sync_kernel_rate_curve_curvature_bounds.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import mpmath as mp
import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class CurvatureBounds:
    mp_dps: int
    theta_min: float
    theta_max: float
    theta_step: float
    n_points: int
    min_P2: str
    theta_at_min_P2: float
    max_P2: str
    theta_at_max_P2: float
    min_I2: str
    theta_at_min_I2: float
    max_I2: str
    theta_at_max_I2: float


def _build_F(lam: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    # Must match appendix `sections/appendix/sync_kernel/weighted/cor__sync-kernel-weighted-unit-root-finite.tex` (app:pressure-analytic).
    return (
        lam**6
        - (1 + u) * lam**5
        - 5 * u * lam**4
        + 3 * u * (1 + u) * lam**3
        - u * (u**2 - 3 * u + 1) * lam**2
        + u * (u**3 - 3 * u**2 - 3 * u + 1) * lam
        + u**2 * (u**2 + u + 1)
    )


def _perron_root_from_u(u: mp.mpf, f_F, f_Fl) -> mp.mpf:
    """
    Solve F(lam,u)=0 for the Perron root lam>0.

    We use Newton (mp.findroot) with an asymptotic initial guess; this is much
    more stable than global polyroot solvers for extreme u.
    """
    u = mp.mpf(u)
    if u <= 0:
        raise ValueError("u must be positive")

    if u < 1:
        # low-temperature expansion from appendix
        g1 = mp.mpf("1") + 3 * u + 2 * u**2
    else:
        # high-temperature expansion from self-duality
        g1 = u + mp.mpf("3") + 2 / u
    g2 = g1 * mp.mpf("1.05")

    def f(x):
        return mp.mpf(f_F(x, u))

    def df(x):
        return mp.mpf(f_Fl(x, u))

    try:
        lam = mp.findroot(f, g1, df=df, tol=mp.mpf("1e-40"), maxsteps=80)
        if lam > 0:
            return mp.mpf(lam)
    except Exception:
        pass

    # Secant fallback (two initial guesses).
    lam = mp.findroot(f, (g1, g2), tol=mp.mpf("1e-40"), maxsteps=200)
    lam = mp.mpf(lam)
    if lam <= 0:
        raise RuntimeError(f"Non-positive root found for u={u}: {lam}")
    return lam


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute curvature bounds for P''(theta).")
    parser.add_argument("--mp-dps", type=int, default=80)
    parser.add_argument("--theta-min", type=float, default=-12.0)
    parser.add_argument("--theta-max", type=float, default=12.0)
    parser.add_argument("--theta-step", type=float, default=0.1)
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_rate_curve_curvature_bounds.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_rate_curve_curvature_bounds.tex"),
    )
    args = parser.parse_args()

    mp.mp.dps = int(args.mp_dps)
    theta_min = float(args.theta_min)
    theta_max = float(args.theta_max)
    theta_step = float(args.theta_step)

    # Symbolic derivatives for F to evaluate Fu, Fl, etc.
    lam_s = sp.Symbol("lam")
    u_s = sp.Symbol("u")
    F = _build_F(lam_s, u_s)
    Fl = sp.diff(F, lam_s)
    Fu = sp.diff(F, u_s)
    Fuu = sp.diff(Fu, u_s)
    Ful = sp.diff(Fu, lam_s)
    Fll = sp.diff(Fl, lam_s)

    f_Fl = sp.lambdify((lam_s, u_s), Fl, "mpmath")
    f_F = sp.lambdify((lam_s, u_s), F, "mpmath")
    f_Fu = sp.lambdify((lam_s, u_s), Fu, "mpmath")
    f_Fuu = sp.lambdify((lam_s, u_s), Fuu, "mpmath")
    f_Ful = sp.lambdify((lam_s, u_s), Ful, "mpmath")
    f_Fll = sp.lambdify((lam_s, u_s), Fll, "mpmath")

    t0 = time.time()
    thetas: List[float] = []
    P2_vals: List[mp.mpf] = []

    n_points = int(mp.floor((theta_max - theta_min) / theta_step)) + 1
    last_report = time.time()
    for i in range(n_points):
        th = theta_min + i * theta_step
        u = mp.e ** mp.mpf(str(th))
        lam = _perron_root_from_u(u, f_F, f_Fl)

        Flv = mp.mpf(f_Fl(lam, u))
        Fuv = mp.mpf(f_Fu(lam, u))
        Fuuv = mp.mpf(f_Fuu(lam, u))
        Fulv = mp.mpf(f_Ful(lam, u))
        Fllv = mp.mpf(f_Fll(lam, u))

        lam_u = -Fuv / Flv
        lam_uu = -(Fuuv + 2 * Fulv * lam_u + Fllv * lam_u**2) / Flv
        # Appendix formula:
        P2 = (u * lam_u) / lam + u**2 * (lam_uu / lam - (lam_u / lam) ** 2)

        thetas.append(float(th))
        P2_vals.append(P2)

        # heartbeat every ~20s
        now = time.time()
        if now - last_report > 20:
            print(f"[curv] i={i}/{n_points} theta={th:.3f} P2={mp.nstr(P2, 12)}", flush=True)
            last_report = now

    # min/max of P''
    i_min = min(range(n_points), key=lambda j: P2_vals[j])
    i_max = max(range(n_points), key=lambda j: P2_vals[j])
    min_P2 = P2_vals[i_min]
    max_P2 = P2_vals[i_max]

    # bounds for I'' = 1/P''
    I2_vals = [mp.mpf("1") / v for v in P2_vals]
    j_minI = min(range(n_points), key=lambda j: I2_vals[j])
    j_maxI = max(range(n_points), key=lambda j: I2_vals[j])
    min_I2 = I2_vals[j_minI]
    max_I2 = I2_vals[j_maxI]

    summary = CurvatureBounds(
        mp_dps=int(args.mp_dps),
        theta_min=theta_min,
        theta_max=theta_max,
        theta_step=theta_step,
        n_points=n_points,
        min_P2=mp.nstr(min_P2, 30),
        theta_at_min_P2=thetas[i_min],
        max_P2=mp.nstr(max_P2, 30),
        theta_at_max_P2=thetas[i_max],
        min_I2=mp.nstr(min_I2, 30),
        theta_at_min_I2=thetas[j_minI],
        max_I2=mp.nstr(max_I2, 30),
        theta_at_max_I2=thetas[j_maxI],
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(summary), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[curv] wrote {jout}", flush=True)

    # TeX table
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Curvature bounds for the energy direction. "
        "We evaluate $P''(\\theta)$ on a real $\\theta$-grid using the sextic equation "
        "$F(\\lambda,u)=0$ and implicit derivatives, then report extrema over the grid. "
        "This gives a reproducible data certificate for strict convexity of $I$ via "
        "$I''(\\alpha(\\theta))=1/P''(\\theta)$.}"
    )
    lines.append("\\label{tab:sync_kernel_rate_curve_curvature_bounds}")
    lines.append("\\begin{tabular}{l l}")
    lines.append("\\toprule")
    lines.append(f"$\\theta$ grid & $[{theta_min:.1f},{theta_max:.1f}]$ step ${theta_step:.3g}$ ($N={n_points}$)\\\\")
    lines.append(f"$P''_{{\\min}}$ & ${summary.min_P2}$ at $\\theta={summary.theta_at_min_P2:.3f}$\\\\")
    lines.append(f"$P''_{{\\max}}$ & ${summary.max_P2}$ at $\\theta={summary.theta_at_max_P2:.3f}$\\\\")
    lines.append(f"$I''_{{\\min}}$ & ${summary.min_I2}$ at $\\theta={summary.theta_at_min_I2:.3f}$\\\\")
    lines.append(f"$I''_{{\\max}}$ & ${summary.max_I2}$ at $\\theta={summary.theta_at_max_I2:.3f}$\\\\")
    lines.append(f"mp.dps & ${summary.mp_dps}$\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")

    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[curv] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

