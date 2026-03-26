#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Near-1 pole (diffusive) predictions from pressure derivatives.

We focus on the collision cocycle:
  varphi_2 = 1_{d=2}.

For the real-input 40-state kernel, the paper gives (closed form in Q(sqrt(5))):
  lambda = rho(M) = phi^2
  mu2    = d/dtheta P(0,0,theta)|_{0} = E[varphi_2] = (3 - sqrt(5)) / 10
  sigma2^2 = d^2/dtheta^2 P(0,0,theta)|_{0} = Var_infty(varphi_2) = (6*sqrt(5) - 5) / 125

For the smallest nontrivial root-of-unity twist t_m = 2π/m, the near-1 pole location
in the s-plane is predicted by:
  s_m = P_2(i t_m) / log(lambda)
     ≈ 1 + i (mu2/log(lambda)) t_m - (sigma2^2/(2 log(lambda))) t_m^2.

This script writes a small LaTeX table for quick numerical cross-checks.

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import Iterable, List, Tuple

from common_paths import generated_dir


def _fmt(x: float, nd: int = 6) -> str:
    return f"{x:.{nd}f}"


def compute_constants() -> Tuple[float, float, float, float, float, float]:
    sqrt5 = math.sqrt(5.0)
    phi = (1.0 + sqrt5) / 2.0
    lam = phi * phi
    log_lam = math.log(lam)

    mu2 = (3.0 - sqrt5) / 10.0
    sigma2 = (6.0 * sqrt5 - 5.0) / 125.0
    kappa = 0.5 * sigma2

    c = (2.0 * (math.pi**2) * sigma2) / log_lam
    d = (2.0 * math.pi * mu2) / log_lam
    parabola = (kappa * log_lam) / (mu2 * mu2)
    return lam, log_lam, mu2, sigma2, c, d, parabola


def rows(ms: Iterable[int], c: float, d: float) -> List[Tuple[int, float, float]]:
    out: List[Tuple[int, float, float]] = []
    for m in ms:
        re_s = 1.0 - c / (m * m)
        im_s = d / float(m)
        out.append((int(m), re_s, im_s))
    return out


def write_tex(path: Path, ms: List[int]) -> None:
    lam, log_lam, mu2, sigma2, c, d, parabola = compute_constants()
    tab = rows(ms, c=c, d=d)

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Near-1 pole diffusive prediction for the collision twist "
        "($\\varphi_2=\\mathbf{1}_{\\{d=2\\}}$) of the real-input 40-state kernel. "
        "Constants are computed from $\\mu_2=P_2'(0)$, $\\sigma_2^2=P_2''(0)$, and "
        "$\\lambda=\\varphi^2$.}"
    )
    lines.append("\\label{tab:real_input_40_collision_near1_pole_predictions}")
    lines.append("\\begin{tabular}{r r r}")
    lines.append("\\toprule")
    lines.append("$m$ & pred. $\\Re(s_m)$ & pred. $\\Im(s_m)$\\\\")
    lines.append("\\midrule")
    for m, re_s, im_s in tab:
        lines.append(f"{m} & {_fmt(re_s, 6)} & {_fmt(im_s, 6)}\\\\")
    lines.append("\\midrule")
    lines.append(
        "$c$ & \\multicolumn{2}{l}{"
        + _fmt(c, 6)
        + "}\\\\"
    )
    lines.append(
        "$d$ & \\multicolumn{2}{l}{"
        + _fmt(d, 6)
        + "}\\\\"
    )
    lines.append(
        "$\\mu_2$ & \\multicolumn{2}{l}{"
        + _fmt(mu2, 10)
        + "}\\\\"
    )
    lines.append(
        "$\\sigma_2^2$ & \\multicolumn{2}{l}{"
        + _fmt(sigma2, 10)
        + "}\\\\"
    )
    lines.append(
        "$\\log\\lambda$ & \\multicolumn{2}{l}{"
        + _fmt(log_lam, 10)
        + "}\\\\"
    )
    lines.append(
        "$\\frac{\\sigma_2^2\\log\\lambda}{2\\mu_2^2}$ & \\multicolumn{2}{l}{"
        + _fmt(parabola, 6)
        + "}\\\\"
    )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")

    print("Wrote:", str(path))
    print("lambda =", lam)
    print("mu2    =", mu2)
    print("sigma2 =", sigma2)
    print("c      =", c)
    print("d      =", d)
    print("parabola coeff =", parabola)


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate near-1 pole prediction table (real-input 40).")
    parser.add_argument(
        "--ms",
        type=str,
        default="5,7,10,20,50",
        help="Comma-separated moduli m (default: 5,7,10,20,50).",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_collision_near1_pole_predictions.tex"),
    )
    args = parser.parse_args()

    ms = [int(x.strip()) for x in str(args.ms).split(",") if x.strip()]
    if not ms:
        raise SystemExit("Empty --ms list.")

    write_tex(Path(str(args.tex_out)), ms=ms)


if __name__ == "__main__":
    main()

