#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Unitary-slice spectral crossing audit for the completed Xi object (weighted sync-kernel).

For a self-dual two-variable determinant
  Delta(z,u)=det(I - z B(u)),   Delta(z,u)=Delta(uz,1/u),
the completed Dirichlet slice (base L>1) is
  Xi_{Delta,L}(s)=Delta(L^{-s}, L^{2s-1}),
and on the critical line s=1/2+it we can parametrize by theta:=2 t log L:
  u = e^{i theta},   z = L^{-1/2} e^{-i theta/2}.
Hence
  Xi(1/2+it) = det(I - U_L(theta)),
  U_L(theta) := L^{-1/2} e^{-i theta/2} B(e^{i theta}).

This script performs a grid audit for the weighted 10-state sync-kernel:
  - checks that det(I-U(theta)) is (numerically) real on the unitary slice,
  - cross-checks det(I-U(theta)) against the completed polynomial form
      hatDelta(w,S) at w=L^{-1/2}, S=2 cos(theta/2),
  - records the minimum distance of Spec(U(theta)) to the eigenvalue 1.

Outputs (default):
  - artifacts/export/sync_kernel_unitary_slice_spectral_crossing.json
  - sections/generated/tab_sync_kernel_unitary_slice_spectral_crossing.tex

All stdout output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from exp_sync_kernel_weighted_pressure import STATES, build_edges


def _build_B0_B1() -> Tuple[np.ndarray, np.ndarray]:
    n = len(STATES)
    idx = {s: i for i, s in enumerate(STATES)}
    B0 = np.zeros((n, n), dtype=np.float64)
    B1 = np.zeros((n, n), dtype=np.float64)
    for edge in build_edges():
        i = idx[edge.src]
        j = idx[edge.dst]
        if edge.e == 0:
            B0[i, j] += 1.0
        else:
            B1[i, j] += 1.0
    return B0, B1


def _hat_delta_weighted_sync_kernel(w: float, S: float) -> float:
    # See exp_sync_kernel_xi_cubic_cos_polynomial.py, hat_delta_weighted_sync_kernel.
    w2 = w * w
    w3 = w2 * w
    w4 = w2 * w2
    w5 = w4 * w
    w6 = w3 * w3
    return (
        1.0
        - S * w
        - 5.0 * w2
        + 3.0 * S * w3
        + (5.0 - S * S) * w4
        + (S * S * S - 6.0 * S) * w5
        + (S * S - 1.0) * w6
    )


@dataclass(frozen=True)
class Stats:
    n_theta: int
    L: float
    theta_min: float
    min_abs_det: float
    theta_min_eig: float
    min_eig_dist_to_1: float
    max_abs_im_det: float
    max_abs_det_minus_completed: float


def write_table_tex(path: Path, st: Stats) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Unitary-slice spectral-crossing audit for the weighted sync-kernel. "
        "We scan $\\theta\\in[0,4\\pi)$ on a uniform grid and evaluate "
        "$\\Xi(\\tfrac12+it)=\\det(I-U_L(\\theta))$ with "
        "$U_L(\\theta)=L^{-1/2}e^{-i\\theta/2}B(e^{i\\theta})$ (here $L=3$). "
        "We report the smallest $|\\det(I-U)|$, the smallest spectral distance "
        "$\\min_{\\lambda\\in\\mathrm{Spec}(U)}|\\lambda-1|$, and two consistency checks: "
        "the maximal imaginary leakage of $\\det(I-U)$ and the maximal deviation from the "
        "completed polynomial form $\\widehat\\Delta(L^{-1/2},2\\cos(\\theta/2))$.}"
    )
    lines.append("\\label{tab:sync_kernel_unitary_slice_spectral_crossing}")
    lines.append("\\begin{tabular}{r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$N_\\theta$ & $\\min|\\det(I-U)|$ & $\\min\\min|\\lambda-1|$ & "
        "$\\max|\\Im\\det|$ & $\\max|\\det-\\widehat\\Delta|$\\\\"
    )
    lines.append("\\midrule")
    lines.append(
        f"{st.n_theta} & {st.min_abs_det:.3e} & {st.min_eig_dist_to_1:.3e} & "
        f"{st.max_abs_im_det:.3e} & {st.max_abs_det_minus_completed:.3e}\\\\"
    )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit unitary-slice spectral crossing for weighted sync-kernel.")
    parser.add_argument("--n-theta", type=int, default=4096, help="Number of theta grid points on [0,4pi).")
    parser.add_argument("--L", type=float, default=3.0, help="Completion base (default: L=3 for sync-kernel).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_unitary_slice_spectral_crossing.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_unitary_slice_spectral_crossing.tex"),
    )
    args = parser.parse_args()

    n_theta = int(args.n_theta)
    if n_theta <= 8:
        raise SystemExit("--n-theta must be > 8")
    L = float(args.L)
    if not (L > 1.0):
        raise SystemExit("--L must be > 1")

    B0, B1 = _build_B0_B1()
    n = int(B0.shape[0])

    # Perron root at u=1 (numeric, for informational output only).
    B1u = B0 + B1
    lam_pf = float(np.max(np.abs(np.linalg.eigvals(B1u))))
    w0 = float(1.0 / math.sqrt(L))

    min_abs_det = float("inf")
    theta_min = 0.0
    min_eig_dist = float("inf")
    theta_min_eig = 0.0
    max_abs_im_det = 0.0
    max_abs_det_minus_completed = 0.0

    I = np.eye(n, dtype=np.complex128)

    for k in range(n_theta):
        theta = (4.0 * math.pi) * (k / n_theta)
        u = complex(math.cos(theta), math.sin(theta))
        z = complex(w0 * math.cos(-theta / 2.0), w0 * math.sin(-theta / 2.0))
        B = (B0 + (u * B1)).astype(np.complex128, copy=False)
        U = z * B

        det_val = complex(np.linalg.det(I - U))
        max_abs_im_det = max(max_abs_im_det, float(abs(det_val.imag)))

        # Completed polynomial consistency: Delta(z,u)=hatDelta(w,S) with w=z*sqrt(u)=L^{-1/2},
        # S=sqrt(u)+1/sqrt(u)=2 cos(theta/2).
        S = 2.0 * math.cos(theta / 2.0)
        det_completed = _hat_delta_weighted_sync_kernel(w=w0, S=S)
        max_abs_det_minus_completed = max(max_abs_det_minus_completed, float(abs(det_val - det_completed)))

        abs_det = float(abs(det_val))
        if abs_det < min_abs_det:
            min_abs_det = abs_det
            theta_min = float(theta)

        eigs = np.linalg.eigvals(U)
        eig_dist = float(np.min(np.abs(eigs - complex(1.0, 0.0))))
        if eig_dist < min_eig_dist:
            min_eig_dist = eig_dist
            theta_min_eig = float(theta)

    st = Stats(
        n_theta=n_theta,
        L=L,
        theta_min=float(theta_min),
        min_abs_det=float(min_abs_det),
        theta_min_eig=float(theta_min_eig),
        min_eig_dist_to_1=float(min_eig_dist),
        max_abs_im_det=float(max_abs_im_det),
        max_abs_det_minus_completed=float(max_abs_det_minus_completed),
    )

    payload: Dict[str, object] = {
        "params": {"n_theta": n_theta, "L": L},
        "kernel": {"dim": n, "lambda_pf_numeric_u_eq_1": lam_pf},
        "stats": asdict(st),
        "notes": {
            "theta_range": "[0, 4*pi)",
            "u(theta)": "exp(i*theta)",
            "z(theta)": "L^{-1/2} * exp(-i*theta/2)",
            "U(theta)": "z(theta) * B(u(theta))",
        },
    }

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[unitary-slice-crossing] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, st)
    print(f"[unitary-slice-crossing] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

