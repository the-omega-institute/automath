#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Master-curve (scaling collapse) experiment for pure collision twists in ((3,3,p)).

We consider the real-input 40-state kernel and the 3D twisting family with:
  (j1,j2) fixed at (0,0) and third axis = N2 mod p (collision trigger cocycle xi = 1_{d=2}).

For each odd prime p and each k=1..k_max we evaluate:
  theta_k = 2π k / p,
  rho_k   = rho( M(1,1,exp(i*theta_k)) ),
  gap_k   = 1 - rho_k / lambda.

We also compute derivatives of the real-tilt pressure along xi:
  P(t) = log rho( M(1,1,exp(t)) ),
and estimate:
  sigma2 = P''(0),  kappa4 = P^{(4)}(0).

Analytic continuation predicts the small-angle master curve:
  log(rho(theta)/lambda) = - sigma2 * theta^2 / 2 + kappa4 * theta^4 / 24 + O(theta^6),
hence a universal scaling collapse at small theta after normalization by sigma2.

Outputs:
  - artifacts/export/arity_335_n2_master_curve.json
  - sections/generated/tab_real_input_40_arity_335_n2_master_curve.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from exp_sync_kernel_real_input_40_arity_3d import (
    build_kernel_edges,
    build_kernel_map,
    build_real_input_states,
    build_weighted_matrix_numeric,
    spectral_radius,
)


def _parse_int_list_csv(s: str) -> List[int]:
    out: List[int] = []
    for chunk in (x.strip() for x in s.split(",")):
        if not chunk:
            continue
        out.append(int(chunk))
    return out


def _pressure_real_tilt(t: float, *, states, kernel_map) -> float:
    # Real tilt on xi: u = exp(t).
    u = math.exp(t)
    M = build_weighted_matrix_numeric(1.0 + 0.0j, 1.0 + 0.0j, complex(u, 0.0), states, kernel_map, third_axis="N2")
    return math.log(spectral_radius(M))


def _central_second(f, h: float) -> float:
    return (f(h) - 2.0 * f(0.0) + f(-h)) / (h * h)


def _central_fourth(f, h: float) -> float:
    # 4th derivative via 5-point symmetric stencil:
    # f''''(0) ≈ (f(-2h) - 4 f(-h) + 6 f(0) - 4 f(h) + f(2h)) / h^4
    return (f(-2.0 * h) - 4.0 * f(-h) + 6.0 * f(0.0) - 4.0 * f(h) + f(2.0 * h)) / (h**4)


def _P2_closed() -> float:
    # Closed form from the pure-collision cubic pressure branch:
    #   P''(0) = (6*sqrt(5) - 5) / 125.
    s5 = 5.0**0.5
    return float((6.0 * s5 - 5.0) / 125.0)


def _P4_closed() -> float:
    # Closed form from the pure-collision cubic pressure branch:
    #   P^{(4)}(0) = (7 + 24*sqrt(5)) / 3125.
    s5 = 5.0**0.5
    return float((7.0 + 24.0 * s5) / 3125.0)



@dataclass(frozen=True)
class Point:
    p: int
    k: int
    theta: float
    rho: float
    rho_ratio: float
    gap: float
    rho_ratio_pred: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Master-curve experiment for ((3,3,p)) pure collision twists.")
    parser.add_argument("--p-list", type=str, default="17,19,23,29,31", help="Comma-separated odd primes p.")
    parser.add_argument("--k-max", type=int, default=1, help="Compute k=1..k_max (keep small for small-angle regime).")
    parser.add_argument("--diff-h", type=float, default=1e-2, help="Step for pressure derivatives P''(0), P''''(0).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "arity_335_n2_master_curve.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_arity_335_n2_master_curve.tex"),
    )
    args = parser.parse_args()

    p_list = _parse_int_list_csv(str(args.p_list))
    if not p_list:
        raise SystemExit("empty p-list")
    k_max = int(args.k_max)
    if k_max < 1:
        raise SystemExit("require k_max >= 1")

    phi = (1.0 + 5.0**0.5) / 2.0
    lam = phi * phi

    prog = Progress("master-curve", every_seconds=20.0)
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()

    # IMPORTANT:
    # A naive 5-point stencil for the 4th derivative is numerically unstable in float64
    # at very small h (catastrophic cancellation + division by h^4). Since this paper
    # has a closed-form expression for the pure-collision pressure derivatives, we
    # use the closed forms for the prediction table, and keep finite-difference values
    # (with user-chosen h) only as an audit trail.
    h = float(args.diff_h)
    f = lambda t: _pressure_real_tilt(t, states=states, kernel_map=kernel_map)
    P2_fd = _central_second(f, h)
    P4_fd = _central_fourth(f, h)

    sigma2 = _P2_closed()
    P4 = _P4_closed()
    kappa_inf = sigma2 / 2.0

    points: List[Point] = []
    for p in p_list:
        if p < 3 or p % 2 == 0:
            raise SystemExit(f"require odd p>=3, got {p}")
        omega = np.exp(2j * math.pi / float(p))
        for k in range(1, k_max + 1):
            theta = 2.0 * math.pi * float(k) / float(p)
            u = omega**k
            M = build_weighted_matrix_numeric(1.0 + 0.0j, 1.0 + 0.0j, u, states, kernel_map, third_axis="N2")
            rho = spectral_radius(M)
            rho_ratio = rho / lam
            gap = 1.0 - rho_ratio
            # Prediction from Taylor on log rho_ratio:
            log_pred = -(sigma2 * theta * theta) / 2.0 + (P4 * (theta**4)) / 24.0
            rho_ratio_pred = math.exp(log_pred)
            points.append(
                Point(
                    p=int(p),
                    k=int(k),
                    theta=float(theta),
                    rho=float(rho),
                    rho_ratio=float(rho_ratio),
                    gap=float(gap),
                    rho_ratio_pred=float(rho_ratio_pred),
                )
            )
        prog.tick(f"p={p} done")

    payload: Dict[str, object] = {
        "p_list": p_list,
        "k_max": k_max,
        "lambda": lam,
        "diff_h": h,
        "pressure_P2": sigma2,
        "pressure_P4": P4,
        "pressure_P2_fd": float(P2_fd),
        "pressure_P4_fd": float(P4_fd),
        "pressure_P2_fd_abs_err": float(abs(P2_fd - sigma2)),
        "pressure_P4_fd_abs_err": float(abs(P4_fd - P4)),
        "kappa_inf": kappa_inf,
        "points": [p.__dict__ for p in points],
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[master-curve] wrote {jout}", flush=True)

    # LaTeX table.
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Small-angle master-curve check for pure collision twists in $((3,3,p))$. "
        "We list $\\rho(\\theta)/\\lambda$ at discrete angles $\\theta=2\\pi k/p$ (with $(j_1,j_2)=(0,0)$) "
        "and compare to the Taylor prediction (valid for small $\\theta$) derived from the real-tilt pressure derivatives "
        "$\\log(\\rho(\\theta)/\\lambda)\\approx -\\sigma^2\\theta^2/2+P^{(4)}(0)\\theta^4/24$.}"
    )
    lines.append("\\label{tab:real_input_40_arity_335_n2_master_curve}")
    lines.append("\\begin{tabular}{r r r r r}")
    lines.append("\\toprule")
    lines.append("$p$ & $k$ & $\\rho(\\theta)/\\lambda$ & pred & abs err\\\\")
    lines.append("\\midrule")
    for pt in points:
        err = abs(pt.rho_ratio - pt.rho_ratio_pred)
        lines.append(
            f"{pt.p} & {pt.k} & {pt.rho_ratio:.12f} & {pt.rho_ratio_pred:.12f} & {err:.3e}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tex = Path(args.tex_out)
    tex.parent.mkdir(parents=True, exist_ok=True)
    tex.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[master-curve] wrote {tex}", flush=True)


if __name__ == "__main__":
    main()

