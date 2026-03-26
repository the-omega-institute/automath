#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Export the cubic cosine polynomial for Xi on the critical line (weighted sync-kernel).

For the weighted sync-kernel we have an explicit completed determinant:
  \\hatΔ(w,S) in Z[w,S] with completion variables
    u = r^2,  w = z r = z sqrt(u),  S = r + r^{-1}.

On the self-dual Dirichlet slice (L=3):
  z(s)=3^{-s},  u(s)=3^{2s-1}
the completion variable w is constant:
  w = z(s) * sqrt(u(s)) = 3^{-1/2},
and the trace coordinate is
  S(s) = sqrt(u(s)) + 1/sqrt(u(s)) = 3^{s-1/2} + 3^{1/2-s}.

Hence on the critical line s=1/2+it we get
  S = 2 cos(t log 3),
and Xi becomes a real cosine-polynomial. For this kernel it collapses to a cubic.

Outputs (default):
  - artifacts/export/sync_kernel_xi_cubic_criterion.json
  - sections/generated/eq_sync_kernel_xi_cubic_cos_polynomial.tex
  - sections/generated/tab_sync_kernel_xi_cubic_roots.tex

All stdout output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir, generated_dir


def hat_delta_weighted_sync_kernel(*, w: sp.Symbol, S: sp.Symbol) -> sp.Expr:
    """
    Completed determinant for the weighted sync-kernel (explicit closed form):
      \\hatΔ(w,S)=1 - S w - 5 w^2 + 3 S w^3 + (5 - S^2) w^4 + (S^3 - 6 S) w^5 + (S^2 - 1) w^6.
    """
    return sp.expand(
        1
        - S * w
        - 5 * w**2
        + 3 * S * w**3
        + (5 - S**2) * w**4
        + (S**3 - 6 * S) * w**5
        + (S**2 - 1) * w**6
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="Export cubic cosine polynomial for sync-kernel Xi (L=3).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_xi_cubic_criterion.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-eq-out",
        type=str,
        default=str(generated_dir() / "eq_sync_kernel_xi_cubic_cos_polynomial.tex"),
        help="Output LaTeX equation snippet path.",
    )
    parser.add_argument(
        "--tex-tab-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_xi_cubic_roots.tex"),
        help="Output LaTeX table snippet path.",
    )
    parser.add_argument(
        "--tex-shift-out",
        type=str,
        default=str(generated_dir() / "eq_sync_kernel_xi_off_critical_shift.tex"),
        help="Output LaTeX snippet for off-critical shift constants.",
    )
    parser.add_argument("--dps", type=int, default=80, help="Digits for numerical roots/values.")
    args = parser.parse_args()

    w, S = sp.symbols("w S")
    hat = hat_delta_weighted_sync_kernel(w=w, S=S)

    print("[xi-cubic] building cubic collapse at w=3^{-1/2} ...", flush=True)
    w0 = 1 / sp.sqrt(3)
    P_scaled = sp.simplify(27 * hat.subs({w: w0}))
    P_scaled = sp.expand(P_scaled)

    # Numeric roots of the cubic polynomial in S (scaling does not matter for root locations).
    roots = sp.nroots(P_scaled, n=int(args.dps))  # type: ignore[arg-type]
    roots_sorted = sorted(roots, key=lambda z: (float(sp.re(z)), float(abs(sp.im(z)))))  # type: ignore[arg-type]

    rows: List[Dict[str, object]] = []
    off_critical: List[Dict[str, object]] = []
    for r in roots_sorted:
        re = float(sp.re(r))
        im = float(sp.im(r))
        is_real = abs(im) <= 1e-30
        in_interval = bool(is_real and (-2.0 - 1e-12 <= re <= 2.0 + 1e-12))
        row: Dict[str, object] = {
            "S": str(r),
            "re": re,
            "im": im,
            "is_real": is_real,
            "in_minus2_2": in_interval,
        }
        if is_real and (re > 2.0 + 1e-12 or re < -2.0 - 1e-12):
            # Solve y + 1/y = S for y, pick y>1 to define the off-critical shift.
            disc = re * re - 4.0
            y = (re + math.sqrt(disc)) / 2.0 if re > 0 else (re - math.sqrt(disc)) / 2.0
            if y < 0:
                # Fallback: use absolute value (log|y| determines the real shift).
                y = abs(y)
            sigma = math.log(y) / math.log(3.0)
            off_critical.append(
                {
                    "S": re,
                    "y_gt_1": y,
                    "sigma": sigma,
                    "re_lines": [0.5 - sigma, 0.5 + sigma],
                    "im_step": 2.0 * math.pi / math.log(3.0),
                }
            )
        rows.append(row)

    payload: Dict[str, object] = {
        "hatDelta_ws": sp.srepr(hat),
        "P_scaled_S": sp.srepr(P_scaled),
        "P_scaled_S_latex": sp.latex(P_scaled),
        "roots": rows,
        "off_critical": off_critical,
    }

    # Write JSON.
    json_out = Path(args.json_out)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[xi-cubic] wrote {json_out}", flush=True)

    # Write LaTeX equation snippet.
    eq_out = Path(args.tex_eq_out)
    eq_out.parent.mkdir(parents=True, exist_ok=True)
    lines_eq: List[str] = []
    lines_eq.append("% Auto-generated; do not edit by hand.")
    lines_eq.append("\\begin{equation}\\label{eq:sync-kernel-xi-cubic-cos}")
    lines_eq.append("\\boxed{")
    lines_eq.append(
        "27\\,\\Xi_{\\Delta,3}\\!\\left(\\tfrac12+it\\right)"
        f"={sp.latex(P_scaled)}"
        + ",\\qquad S:=2\\cos(t\\log 3)."
    )
    lines_eq.append("}")
    lines_eq.append("\\end{equation}")
    eq_out.write_text("\n".join(lines_eq) + "\n", encoding="utf-8")
    print(f"[xi-cubic] wrote {eq_out}", flush=True)

    # Write LaTeX table snippet for the roots.
    tab_out = Path(args.tex_tab_out)
    tab_out.parent.mkdir(parents=True, exist_ok=True)
    lines_tab: List[str] = []
    lines_tab.append("\\begin{table}[H]")
    lines_tab.append("\\centering")
    lines_tab.append("\\scriptsize")
    lines_tab.append("\\setlength{\\tabcolsep}{6pt}")
    lines_tab.append(
        "\\caption{Roots of the cubic completion slice polynomial $P(S)=\\widehat\\Delta(3^{-1/2},S)$ "
        "(reported from $27\\,P(S)$; scaling does not affect root locations).}"
    )
    lines_tab.append("\\label{tab:sync_kernel_xi_cubic_roots}")
    lines_tab.append("\\begin{tabular}{r r r}")
    lines_tab.append("\\toprule")
    lines_tab.append("$i$ & $S_i$ & $S_i\\in[-2,2]$?\\\\")
    lines_tab.append("\\midrule")
    for i, rr in enumerate(rows, start=1):
        val = rr["re"] if rr["is_real"] else rr["S"]
        val_str = f"{float(val):.15f}" if isinstance(val, (int, float)) else str(val)
        ok = "yes" if rr["in_minus2_2"] else "no"
        lines_tab.append(f"{i} & {val_str} & {ok}\\\\")
    lines_tab.append("\\bottomrule")
    lines_tab.append("\\end{tabular}")
    lines_tab.append("\\end{table}")
    tab_out.write_text("\n".join(lines_tab) + "\n", encoding="utf-8")
    print(f"[xi-cubic] wrote {tab_out}", flush=True)

    # Write LaTeX snippet for the off-critical shift constants (if any).
    shift_out = Path(args.tex_shift_out)
    shift_out.parent.mkdir(parents=True, exist_ok=True)
    lines_shift: List[str] = []
    lines_shift.append("% Auto-generated; do not edit by hand.")
    lines_shift.append("\\begin{equation}\\label{eq:sync-kernel-xi-offcritical-shift}")
    if off_critical:
        oc = off_critical[0]
        S0 = float(oc["S"])
        sigma0 = float(oc["sigma"])
        im_step = float(oc["im_step"])
        lines_shift.append("\\boxed{")
        lines_shift.append(
            f"S_0\\approx {S0:.15f},\\qquad"
            f"\\sigma_0\\approx {sigma0:.15f},\\qquad"
            f"\\Delta_t:=\\frac{{2\\pi}}{{\\log 3}}\\approx {im_step:.15f}."
        )
        lines_shift.append("}")
    else:
        lines_shift.append("\\boxed{\\text{No off-critical roots detected for }P(S).}")
    lines_shift.append("\\end{equation}")
    shift_out.write_text("\n".join(lines_shift) + "\n", encoding="utf-8")
    print(f"[xi-cubic] wrote {shift_out}", flush=True)

    print("[xi-cubic] done", flush=True)


if __name__ == "__main__":
    main()

