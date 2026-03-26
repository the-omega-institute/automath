#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Phase–amplitude separation on the unit-circle twist for the weighted sync-kernel.

Let u = exp(i theta). Define r = exp(i theta/2), s = r + r^{-1} = 2 cos(theta/2),
and w = z r. For the completed determinant:
    Delta(z,u) = hatDelta(w,s),
so the smallest pole can be written as z_*(u) = w_*(s)/r where w_*(s) is the root
of hatDelta(w,s)=0 with minimal |w| (empirically real on s in [-2,2]).
Then the Perron root satisfies:
    lambda(u) = 1/z_*(u) = r * (1/w_*(s)),
so lambda(u)/r is (approximately) real: the phase is exactly theta/2.

This script numerically checks:
  - lambda(u) computed from the 10x10 weighted adjacency matrix B(u),
  - the completed prediction r / w_*(s),
  - the reality of lambda(u)/r.

Outputs:
  - artifacts/export/sync_kernel_weighted_phase_amplitude.json
  - sections/generated/tab_sync_kernel_weighted_phase_amplitude.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from exp_sync_kernel_weighted_pressure import STATES, build_edges


def hat_delta_coeffs_w_desc(s: float) -> List[float]:
    """Return coefficients of hatDelta(w,s) in descending powers of w (degree 6)."""
    # hatDelta(w,s) = 1 - s w - 5 w^2 + 3 s w^3 + (5 - s^2) w^4 + (s^3 - 6 s) w^5 + (s^2 - 1) w^6
    c0 = 1.0
    c1 = -float(s)
    c2 = -5.0
    c3 = 3.0 * float(s)
    c4 = 5.0 - float(s) ** 2
    c5 = float(s) ** 3 - 6.0 * float(s)
    c6 = float(s) ** 2 - 1.0
    # descending: w^6..w^0
    return [c6, c5, c4, c3, c2, c1, c0]


def pick_w_star_real_min_abs(s: float) -> float:
    coeffs = hat_delta_coeffs_w_desc(s)
    roots = np.roots(np.array(coeffs, dtype=np.complex128))
    real_roots = [r for r in roots if abs(r.imag) < 1e-10]
    if not real_roots:
        # Fallback: take the root with smallest |w| and return its real part.
        r0 = min(roots, key=lambda z: abs(z))
        return float(r0.real)
    rmin = min(real_roots, key=lambda z: abs(z))
    return float(rmin.real)


def build_B_u(u: complex) -> np.ndarray:
    idx = {s: i for i, s in enumerate(STATES)}
    n = len(STATES)
    B = np.zeros((n, n), dtype=np.complex128)
    for e in build_edges():
        i = idx[e.src]
        j = idx[e.dst]
        B[i, j] += (1.0 + 0.0j) if e.e == 0 else u
    return B


def perron_root_from_matrix(B: np.ndarray) -> complex:
    vals = np.linalg.eigvals(B)
    return max(vals, key=lambda z: abs(z))


@dataclass(frozen=True)
class Row:
    theta: float
    s: float
    w_star: float
    lambda_mat: complex
    lambda_pred: complex
    rel_err: float
    lambda_over_r: complex


def write_table_tex(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Phase--amplitude separation check on the unit-circle twist $u=e^{i\\theta}$ "
        "for the weighted sync-kernel. We compare the Perron root $\\lambda(e^{i\\theta})$ "
        "computed from the matrix with the completed prediction $e^{i\\theta/2}/w_\\star(s)$, "
        "where $s=2\\cos(\\theta/2)$ and $w_\\star(s)$ is the real root of "
        "$\\widehat\\Delta(w,s)=0$ with minimal $|w|$.}"
    )
    lines.append("\\label{tab:sync_kernel_weighted_phase_amplitude}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append("$\\theta$ & $s$ & $w_\\star(s)$ & $|\\lambda|$ & $\\arg\\lambda$ & $\\Im(\\lambda/e^{i\\theta/2})$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lam = r.lambda_mat
        arg = math.atan2(lam.imag, lam.real)
        lines.append(
            f"{r.theta:.6f} & {r.s:.6f} & {r.w_star:.6f} & {abs(lam):.6f} & {arg:.6f} & {r.lambda_over_r.imag:.3e}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Check phase–amplitude separation for weighted sync-kernel.")
    parser.add_argument(
        "--theta-grid",
        type=str,
        default="0,0.523598775598,1.0471975512,1.57079632679,2.09439510239,2.61799387799,3.14159265359",
        help="Comma-separated theta values (radians).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_weighted_phase_amplitude.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_weighted_phase_amplitude.tex"),
    )
    args = parser.parse_args()

    thetas = [float(x) for x in str(args.theta_grid).split(",") if x.strip()]
    prog = Progress("sync-kernel-weighted-phase-amplitude", every_seconds=20.0)

    rows: List[Row] = []
    t0 = time.time()
    for i, theta in enumerate(thetas):
        u = complex(math.cos(theta), math.sin(theta))
        r = complex(math.cos(theta / 2.0), math.sin(theta / 2.0))
        s = 2.0 * math.cos(theta / 2.0)

        w_star = pick_w_star_real_min_abs(s)
        lam_pred = r / w_star

        B = build_B_u(u)
        lam = perron_root_from_matrix(B)
        rel_err = abs(lam - lam_pred) / max(1e-15, abs(lam))
        lam_over_r = lam / r if abs(r) > 0 else complex("nan")

        rows.append(
            Row(
                theta=theta,
                s=s,
                w_star=w_star,
                lambda_mat=lam,
                lambda_pred=lam_pred,
                rel_err=float(rel_err),
                lambda_over_r=lam_over_r,
            )
        )
        prog.tick(f"theta[{i+1}/{len(thetas)}]={theta:.6g} rel_err={rel_err:.3e}")

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "theta_grid": thetas,
        "rows": [
            {
                **asdict(r),
                "lambda_mat": {"re": r.lambda_mat.real, "im": r.lambda_mat.imag},
                "lambda_pred": {"re": r.lambda_pred.real, "im": r.lambda_pred.imag},
                "lambda_over_r": {"re": r.lambda_over_r.real, "im": r.lambda_over_r.imag},
            }
            for r in rows
        ],
        "note": "Small Im(lambda/r) and small rel_err support phase–amplitude separation.",
    }
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[phase-amplitude] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[phase-amplitude] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

