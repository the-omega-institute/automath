#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Kernel Newman threshold experiment for the real-input 40-state kernel.

We fix the 3D twisting family used elsewhere in the paper and focus on the
"pure collision" third axis (xi = 1_{d=2}). Following the manuscript's
zero-temperature convention u = exp(-beta) with beta >= 0, for each odd prime p
we consider characters u = exp(-beta) * omega_p^k with k != 0 and define:

  lambda1(beta) := rho( M(1,1,exp(-beta)) )
  Lambda_p(beta) := max_{1 <= k <= (p-1)/2} rho( M(1,1, exp(-beta) * omega_p^k) )

The kernel Newman threshold for modulus p is then the smallest t where:

  Lambda_p(beta) <= sqrt(lambda1(beta)).

This is a finite-modulus proxy for the definition in the manuscript:
  beta_* := inf { beta : Lambda(e^{-beta}) <= lambda1(e^{-beta})^{1/2} }.

Outputs:
  - artifacts/export/real_input_40_kernel_newman_threshold.json
  - sections/generated/tab_real_input_40_kernel_newman_threshold.tex

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


def _f_ratio_for_p(
    *,
    p: int,
    beta: float,
    states,
    kernel_map,
) -> Tuple[float, float, float]:
    """Return (lambda1, Lambda_p, ratio) at inverse-temperature beta.

    ratio := Lambda_p / sqrt(lambda1).
    """
    if p < 3 or p % 2 == 0:
        raise ValueError("p must be an odd prime >= 3")

    u0 = complex(math.exp(-beta), 0.0)
    M0 = build_weighted_matrix_numeric(1.0 + 0.0j, 1.0 + 0.0j, u0, states, kernel_map, third_axis="N2")
    lam1 = spectral_radius(M0)
    if not (lam1 > 0.0 and math.isfinite(lam1)):
        raise ValueError("invalid lambda1")

    omega = np.exp(2j * math.pi / float(p))
    # Max over nontrivial characters; conjugate symmetry means k and p-k agree in spectral radius.
    lam_tw = 0.0
    for k in range(1, (p - 1) // 2 + 1):
        uk = u0 * (omega**k)
        Mk = build_weighted_matrix_numeric(1.0 + 0.0j, 1.0 + 0.0j, uk, states, kernel_map, third_axis="N2")
        rho_k = spectral_radius(Mk)
        if rho_k > lam_tw:
            lam_tw = rho_k

    ratio = lam_tw / math.sqrt(lam1)
    return float(lam1), float(lam_tw), float(ratio)


def _scan_bracket(
    *,
    p: int,
    beta_values: List[float],
    states,
    kernel_map,
    prog: Progress,
    label: str,
) -> Tuple[bool, int, int, List[Dict[str, float]]]:
    """Scan and return (has_crossing, first_good_idx, best_idx, records).

    best_idx minimizes ratio over the scanned grid.
    """
    records: List[Dict[str, float]] = []
    first_good_idx = -1
    best_idx = 0
    best_ratio = float("inf")
    for i, beta in enumerate(beta_values):
        lam1, Lam, ratio = _f_ratio_for_p(p=p, beta=beta, states=states, kernel_map=kernel_map)
        rec = {"beta": float(beta), "u": float(math.exp(-beta)), "lambda1": lam1, "Lambda_p": Lam, "ratio": ratio}
        records.append(rec)
        if first_good_idx < 0 and ratio <= 1.0:
            first_good_idx = i
        if ratio < best_ratio:
            best_ratio = ratio
            best_idx = i
        prog.tick(f"{label} scan i={i+1}/{len(beta_values)}")
    return (first_good_idx >= 0), first_good_idx, best_idx, records


def _bisect_threshold(
    *,
    p: int,
    beta_lo: float,
    beta_hi: float,
    iters: int,
    states,
    kernel_map,
    prog: Progress,
    label: str,
) -> Tuple[float, float, float]:
    """Bisection on ratio(t)-1, assuming ratio(t_lo) > 1 and ratio(t_hi) <= 1."""
    lo = float(beta_lo)
    hi = float(beta_hi)
    lam1_hi, Lam_hi, ratio_hi = _f_ratio_for_p(p=p, beta=hi, states=states, kernel_map=kernel_map)
    if ratio_hi > 1.0:
        raise ValueError("bisection requires ratio(t_hi) <= 1")
    lam1_lo, Lam_lo, ratio_lo = _f_ratio_for_p(p=p, beta=lo, states=states, kernel_map=kernel_map)
    if ratio_lo <= 1.0:
        return lo, lam1_lo, Lam_lo

    best_t = hi
    best_lam1 = lam1_hi
    best_Lam = Lam_hi
    for j in range(iters):
        mid = 0.5 * (lo + hi)
        lam1, Lam, ratio = _f_ratio_for_p(p=p, beta=mid, states=states, kernel_map=kernel_map)
        if ratio <= 1.0:
            hi = mid
            best_t, best_lam1, best_Lam = mid, lam1, Lam
        else:
            lo = mid
        prog.tick(f"{label} bisect iter={j+1}/{iters}")
    return float(best_t), float(best_lam1), float(best_Lam)


def main() -> None:
    parser = argparse.ArgumentParser(description="Kernel Newman threshold for real-input 40-state kernel (pure collision axis).")
    parser.add_argument("--p-list", type=str, default="5,7,11,13,17,19,23", help="Comma-separated odd primes p.")
    parser.add_argument("--beta-min", type=float, default=0.0, help="Scan minimum beta (u=exp(-beta)).")
    parser.add_argument("--beta-max", type=float, default=8.0, help="Scan maximum beta (u=exp(-beta)).")
    parser.add_argument("--beta-steps", type=int, default=81, help="Coarse scan steps for bracketing.")
    parser.add_argument("--bisect-iters", type=int, default=28, help="Bisection iterations once bracketed.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_kernel_newman_threshold.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_kernel_newman_threshold.tex"),
    )
    args = parser.parse_args()

    p_list = _parse_int_list_csv(str(args.p_list))
    if not p_list:
        raise SystemExit("empty p-list")
    for p in p_list:
        if p < 3 or p % 2 == 0:
            raise SystemExit(f"require odd primes, got p={p}")

    beta_min = float(args.beta_min)
    beta_max = float(args.beta_max)
    if beta_max <= beta_min:
        raise SystemExit("require beta_max > beta_min")
    steps = int(args.beta_steps)
    if steps < 2:
        raise SystemExit("require beta_steps >= 2")

    # Setup kernel.
    prog = Progress("kernel-newman-threshold", every_seconds=20.0)
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()

    beta_values = [beta_min + (beta_max - beta_min) * i / float(steps - 1) for i in range(steps)]

    results: List[Dict[str, object]] = []
    scans: Dict[str, object] = {}
    beta_star_max = None

    for p in p_list:
        label = f"p={p}"
        has_crossing, first_good_idx, best_idx, recs = _scan_bracket(
            p=p,
            beta_values=beta_values,
            states=states,
            kernel_map=kernel_map,
            prog=prog,
            label=label,
        )
        scans[str(p)] = {"records": recs, "first_good_idx": int(first_good_idx), "best_idx": int(best_idx)}

        if not has_crossing:
            best = recs[int(best_idx)]
            results.append(
                {
                    "p": int(p),
                    "beta_star": None,
                    "status": "no_crossing_in_scan",
                    "beta_best": float(best["beta"]),
                    "u_best": float(best["u"]),
                    "lambda1_best": float(best["lambda1"]),
                    "Lambda_p_best": float(best["Lambda_p"]),
                    "ratio_best": float(best["ratio"]),
                }
            )
            continue

        if first_good_idx == 0:
            beta_star = float(beta_values[0])
            lam1, Lam, ratio = _f_ratio_for_p(p=p, beta=beta_star, states=states, kernel_map=kernel_map)
        else:
            beta_hi = float(beta_values[first_good_idx])
            beta_lo = float(beta_values[first_good_idx - 1])
            beta_star, lam1, Lam = _bisect_threshold(
                p=p,
                beta_lo=beta_lo,
                beta_hi=beta_hi,
                iters=int(args.bisect_iters),
                states=states,
                kernel_map=kernel_map,
                prog=prog,
                label=label,
            )
            ratio = float(Lam / math.sqrt(lam1))

        results.append(
            {
                "p": int(p),
                "beta_star": float(beta_star),
                "u_star": float(math.exp(-beta_star)),
                "lambda1": float(lam1),
                "Lambda_p": float(Lam),
                "ratio": float(ratio),
                "status": "ok",
                "beta_best": float(beta_star),
                "u_best": float(math.exp(-beta_star)),
                "lambda1_best": float(lam1),
                "Lambda_p_best": float(Lam),
                "ratio_best": float(ratio),
            }
        )
        if beta_star_max is None or float(beta_star) > float(beta_star_max):
            beta_star_max = float(beta_star)

    payload: Dict[str, object] = {
        "definition": {
            "family": "M(q=1,r=1,u) with third_axis=N2",
            "lambda1(beta)": "rho(M(1,1,exp(-beta)))",
            "Lambda_p(beta)": "max_{k!=0} rho(M(1,1,exp(-beta)*omega_p^k))",
            "criterion": "Lambda_p(beta) <= sqrt(lambda1(beta))",
        },
        "p_list": p_list,
        "scan": {"beta_min": beta_min, "beta_max": beta_max, "beta_steps": steps},
        "bisect_iters": int(args.bisect_iters),
        "beta_star_max_over_p_list": beta_star_max,
        "results": results,
        "scans": scans,
    }

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[kernel-newman-threshold] wrote {jout}", flush=True)

    # LaTeX table.
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Kernel Newman threshold proxy $\\beta_\\ast(p)$ for the real-input 40-state kernel "
        "along the pure-collision axis (third axis $N_2$). For each odd prime $p$ we find the smallest "
        "$\\beta$ such that $\\Lambda_p(\\beta)\\le \\sqrt{\\lambda_1(\\beta)}$, where "
        "$\\lambda_1(\\beta)=\\rho(M(\\exp(-\\beta)))$ and "
        "$\\Lambda_p(\\beta)=\\max_{1\\le k\\le (p-1)/2}\\rho(M(\\exp(-\\beta)\\,\\omega_p^k))$.}"
    )
    lines.append("\\label{tab:real_input_40_kernel_newman_threshold}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$p$ & $\\beta_\\ast(p)$ & $\\beta_{\\min}$ & $\\lambda_1(\\beta_{\\min})$ & $\\Lambda_p(\\beta_{\\min})$ & "
        "$\\min\\,\\Lambda_p/\\sqrt{\\lambda_1}$\\\\"
    )
    lines.append("\\midrule")
    for r in results:
        p = int(r["p"])
        status = str(r.get("status"))
        beta_best = float(r.get("beta_best"))
        lam1_best = float(r.get("lambda1_best"))
        Lam_best = float(r.get("Lambda_p_best"))
        ratio_best = float(r.get("ratio_best"))
        if status == "ok":
            beta_star = float(r["beta_star"])
            lines.append(
                f"{p} & {beta_star:.6f} & {beta_best:.6f} & {lam1_best:.10f} & {Lam_best:.10f} & {ratio_best:.6f}\\\\"
            )
        else:
            # No crossing: beta_* not observed within scan range.
            lines.append(
                f"{p} & $> {beta_max:.3g}$ & {beta_best:.6f} & {lam1_best:.10f} & {Lam_best:.10f} & {ratio_best:.6f}\\\\"
            )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tex = Path(args.tex_out)
    tex.parent.mkdir(parents=True, exist_ok=True)
    tex.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[kernel-newman-threshold] wrote {tex}", flush=True)


if __name__ == "__main__":
    main()

