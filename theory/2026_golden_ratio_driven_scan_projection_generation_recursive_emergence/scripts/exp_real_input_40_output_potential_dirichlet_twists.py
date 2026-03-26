#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Dirichlet / root-of-unity twists for the output potential (real-input 40-state kernel).

We use the explicit low-degree determinant from the appendix:
  Delta(z,u) = det(I - z M(u))
            = (1 - u z^2) * F(z,u),
where F(z,u) is an 8th-degree polynomial in z with coefficients in Z[u].

For a modulus m>=2 and character j=1..m-1, define u = exp(2π i j / m).
Then the twisted spectral radius is:
  rho_{m,j} := rho(M(u)) = 1 / min{|z| : Delta(z,u)=0}.

We export:
  - worst twist rho_m := max_{1<=j<=m-1} rho_{m,j},
  - exponent theta_m := log(rho_m) / log(lambda), where lambda = rho(M(1)) = phi^2,
  - cumulant-based small-angle prediction using P''(0), P^{(4)}(0).

Outputs:
  - artifacts/export/real_input_40_output_potential_dirichlet_twists.json
  - sections/generated/tab_real_input_40_output_potential_dirichlet_twists.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import mpmath as mp
import sympy as sp

from common_paths import export_dir, generated_dir


def _delta_poly_sympy() -> sp.Expr:
    """Return the exact symbolic polynomial Delta(z,u) from the appendix."""
    z, u = sp.symbols("z u")
    F = (
        sp.Integer(1)
        - z
        - 6 * u * z**2
        + 2 * u * z**3
        + (9 * u**2 - u) * z**4
        + (u - 3 * u**2) * z**5
        - (u**3 + 2 * u**2) * z**6
        + (4 * u**3 - 3 * u**2) * z**7
        + (u**3 - u**4) * z**8
    )
    return sp.expand((1 - u * z**2) * F)


@dataclass(frozen=True)
class Row:
    m: int
    j_worst: int
    rho_worst: str
    rho_over_lambda: str
    theta_worst: str
    # Also report j=1 mode (typically worst) for transparency.
    rho_j1: str
    theta_j1: str
    # cumulant prediction for j=1: log(rho/lambda) ≈ -k2/2 t^2 + k4/24 t^4
    pred_rho_over_lambda_j1: str


def _fmt(x: mp.mpf | mp.mpc, nd: int = 16) -> str:
    if isinstance(x, mp.mpc):
        return f"{mp.nstr(x.real, nd)}{('+' if x.imag >= 0 else '')}{mp.nstr(x.imag, nd)}j"
    return mp.nstr(x, nd)


def main() -> None:
    parser = argparse.ArgumentParser(description="Dirichlet twists for output potential (real input 40-state).")
    parser.add_argument("--m-list", type=str, default="2,3,4,5,6,10,20", help="Comma-separated moduli.")
    parser.add_argument("--dps", type=int, default=80, help="mpmath decimal precision.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_output_potential_dirichlet_twists.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_output_potential_dirichlet_twists.tex"),
    )
    args = parser.parse_args()

    mp.mp.dps = int(args.dps)

    ms = [int(s.strip()) for s in args.m_list.split(",") if s.strip()]
    if any(m < 2 for m in ms):
        raise ValueError("All m must be >= 2.")

    sqrt5 = mp.sqrt(5)
    lam = (3 + sqrt5) / 2  # phi^2
    loglam = mp.log(lam)

    # Closed-form cumulants from tab_real_input_40_output_potential_cumulants_closed.tex:
    k2 = mp.mpf(1791) / 200 - (mp.mpf(3983) / 1000) * sqrt5
    k4 = mp.mpf(1354428303) / 100000 - (mp.mpf(605718497) / 100000) * sqrt5

    rows: List[Row] = []
    details: Dict[str, object] = {
        "lambda": str(lam),
        "k2": str(k2),
        "k4": str(k4),
        "rows": [],
    }

    z, u_sym = sp.symbols("z u")
    Delta_sym = _delta_poly_sympy()

    for m in ms:
        # Compute all j modes; pick worst by rho.
        best_rho = mp.mpf("0")
        best_j = 1

        rho_j1 = None
        theta_j1 = None

        for j in range(1, m):
            # Root of unity in exact symbolic form; then numerically approximate at high precision.
            u0 = sp.exp(2 * sp.pi * sp.I * sp.Rational(j, m))
            poly_z = sp.Poly(Delta_sym.subs(u_sym, u0), z)
            # nroots precision is in digits; we match mpmath dps.
            roots_sp = poly_z.nroots(n=mp.mp.dps, maxsteps=200)
            roots_mp = []
            for r in roots_sp:
                re = sp.N(sp.re(r), mp.mp.dps)
                im = sp.N(sp.im(r), mp.mp.dps)
                roots_mp.append(mp.mpc(mp.mpf(str(re)), mp.mpf(str(im))))
            z_star = min(roots_mp, key=lambda zz: abs(zz))
            rho = 1 / abs(z_star)
            # Comparison bound: since |M(u)|<=M(1) entrywise, we must have rho<=lambda.
            if rho > lam * (mp.mpf("1.0") + mp.mpf("1e-12")):
                raise RuntimeError(f"rho>lambda at m={m}, j={j}: rho={rho}, lambda={lam}")
            if j == 1:
                rho_j1 = rho
                theta_j1 = mp.log(rho) / loglam
            if rho > best_rho:
                best_rho = rho
                best_j = j

        assert rho_j1 is not None and theta_j1 is not None

        rho_over = best_rho / lam
        theta = mp.log(best_rho) / loglam

        # cumulant prediction for j=1
        t = 2 * mp.pi / m
        log_pred = -(k2 / 2) * (t**2) + (k4 / 24) * (t**4)
        pred_over = mp.e ** log_pred

        row = Row(
            m=m,
            j_worst=int(best_j),
            rho_worst=_fmt(best_rho, 18),
            rho_over_lambda=_fmt(rho_over, 18),
            theta_worst=_fmt(theta, 18),
            rho_j1=_fmt(rho_j1, 18),
            theta_j1=_fmt(theta_j1, 18),
            pred_rho_over_lambda_j1=_fmt(pred_over, 18),
        )
        rows.append(row)
        details["rows"].append(asdict(row))
        print(f"[dirichlet-twists] m={m} done (j_worst={best_j})", flush=True)

    # Write JSON.
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(details, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[dirichlet-twists] wrote {jout}", flush=True)

    # Write LaTeX table.
    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Dirichlet/root-of-unity twists for the output potential of the real-input 40-state kernel. "
        "For $u=\\omega_m^j=e^{2\\pi i j/m}$ we define $\\rho_{m,j}=1/\\min\\{|z|: \\Delta(z,\\omega_m^j)=0\\}$ "
        "and report the worst mode $\\rho_m=\\max_{1\\le j\\le m-1}\\rho_{m,j}$. "
        "We also include the small-angle cumulant prediction for the $j=1$ mode using $\\kappa_2=P''(0)$ and $\\kappa_4=P^{(4)}(0)$.}"
    )
    lines.append("\\label{tab:real_input_40_output_potential_dirichlet_twists}")
    lines.append("\\begin{tabular}{r r r r r}")
    lines.append("\\toprule")
    lines.append("$m$ & $j_{\\mathrm{worst}}$ & $\\rho_m/\\lambda$ & $\\theta_m$ & pred. $\\rho_{m,1}/\\lambda$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.m} & {r.j_worst} & ${r.rho_over_lambda}$ & ${r.theta_worst}$ & ${r.pred_rho_over_lambda_j1}$\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[dirichlet-twists] wrote {tout}", flush=True)
    print("[dirichlet-twists] done", flush=True)


if __name__ == "__main__":
    main()

