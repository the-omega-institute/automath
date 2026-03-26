#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Local bi-geometry invariants at theta=0 for (P, logM).

We combine two audited exports:
  - sync_kernel_real_input_40.json: pressure_grad, pressure_hessian
  - sync_kernel_real_input_40_logM_theta_taylor.json: grad_logM_0, hess_logM_0

We compute:
  - isobaric drift vector v_perp (Euclidean orthogonal projection)
  - correlations and partial correlations from Sigma and Omega=Sigma^{-1}
  - curvature mismatch spectrum: eig(Sigma^{-1} Hess_logM)
  - dominant generalized eigenmode u_+ and its Euclidean alignment with v_perp

Outputs (default):
  - artifacts/export/real_input_40_local_bigeometry_invariants.json
  - sections/generated/tab_real_input_40_local_bigeometry_invariants.tex

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

from common_paths import export_dir, generated_dir, paper_root


@dataclass(frozen=True)
class Invariants:
    mu: float
    v_perp: List[float]
    v_perp_norm: float
    u_plus_theta2_minus1: List[float]
    cos_vperp_u_plus: float
    corr: List[List[float]]
    partial_corr: List[List[float]]
    eigs_sigma_inv_hlogm: List[float]


def _load_json(rel: str) -> Dict[str, object]:
    p = paper_root() / rel
    return json.loads(p.read_text(encoding="utf-8"))


def compute() -> Invariants:
    pressure = _load_json("artifacts/export/sync_kernel_real_input_40.json")
    logm = _load_json("artifacts/export/sync_kernel_real_input_40_logM_theta_taylor.json")

    # Export uses named entries.
    gPd = pressure["pressure_grad"]
    if not isinstance(gPd, dict):
        raise TypeError("pressure_grad must be a dict in sync_kernel_real_input_40.json")
    # Channel order: (e, -, 2)
    gP = np.array([float(gPd["theta_e"]), float(gPd["theta_neg"]), float(gPd["theta_2"])], dtype=float)

    Sd = pressure["pressure_hessian"]
    if not isinstance(Sd, dict):
        raise TypeError("pressure_hessian must be a dict in sync_kernel_real_input_40.json")
    # Keys: ee, en, e2, nn, n2, 22
    Sigma = np.array(
        [
            [float(Sd["ee"]), float(Sd["en"]), float(Sd["e2"])],
            [float(Sd["en"]), float(Sd["nn"]), float(Sd["n2"])],
            [float(Sd["e2"]), float(Sd["n2"]), float(Sd["22"])],
        ],
        dtype=float,
    )
    gL = np.array(logm["grad_logM_0"], dtype=float)
    HlogM = np.array(logm["hess_logM_0"], dtype=float)

    mu = float((gP @ gL) / (gP @ gP))
    v_perp = gL - mu * gP
    v_perp_norm = float(np.linalg.norm(v_perp))

    # Generalized eigenproblem: H v = mu Sigma v (Sigma SPD, H symmetric).
    # Use symmetric reduction for numerically stable real eigenvectors.
    L = np.linalg.cholesky(Sigma)  # Sigma = L L^T
    Linv = np.linalg.inv(L)
    A = Linv @ HlogM @ Linv.T  # symmetric
    evals, evecs = np.linalg.eigh(A)  # ascending
    order = np.argsort(evals)[::-1]
    evals = evals[order]
    evecs = evecs[:, order]
    # Back-transform eigenvectors to original coordinates: v = L^{-T} y
    V = np.linalg.solve(L.T, evecs)
    v_pos = np.array(V[:, 0], dtype=float)
    # Fix sign / scale: enforce theta_2 component negative and set to -1.
    if v_pos[2] > 0:
        v_pos = -v_pos
    if abs(v_pos[2]) < 1e-15:
        raise ValueError("Unexpected near-zero theta_2 component in dominant eigenvector")
    u_plus = v_pos / (-v_pos[2])
    cos_vu = float((v_perp @ u_plus) / (v_perp_norm * np.linalg.norm(u_plus)))

    D = np.sqrt(np.diag(Sigma))
    corr = (Sigma / np.outer(D, D)).tolist()

    Omega = np.linalg.inv(Sigma)
    Do = np.sqrt(np.diag(Omega))
    partial = (-Omega / np.outer(Do, Do))
    np.fill_diagonal(partial, 1.0)
    partial_corr = partial.tolist()

    eigs_real = [float(x) for x in evals.tolist()]

    return Invariants(
        mu=mu,
        v_perp=[float(x) for x in v_perp.tolist()],
        v_perp_norm=v_perp_norm,
        u_plus_theta2_minus1=[float(x) for x in u_plus.tolist()],
        cos_vperp_u_plus=cos_vu,
        corr=[[float(x) for x in row] for row in corr],
        partial_corr=[[float(x) for x in row] for row in partial_corr],
        eigs_sigma_inv_hlogm=eigs_real,
    )


def _fmt_vec(v: List[float], nd: int = 6) -> str:
    return "(" + ", ".join(f"{x:.{nd}f}" for x in v) + ")"


def _fmt(x: float, nd: int = 6) -> str:
    return f"{x:.{nd}f}"


def write_table_tex(path: Path, inv: Invariants) -> None:
    # Channel order: (e, -, 2)
    rho_e_minus = inv.corr[0][1]
    rho_e_2 = inv.corr[0][2]
    rho_minus_2 = inv.corr[1][2]

    pr_e_minus_given_2 = inv.partial_corr[0][1]
    pr_e_2_given_minus = inv.partial_corr[0][2]
    pr_minus_2_given_e = inv.partial_corr[1][2]

    mu1, mu2, mu3 = inv.eigs_sigma_inv_hlogm

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{8pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.2}")
    lines.append(
        "\\caption{Local bi-geometry invariants at $\\theta=0$ (real-input 40-state kernel). "
        "We combine $\\nabla P(0),\\Sigma=\\nabla^2P(0)$ with $\\nabla\\log\\mathfrak{M}(0)$ "
        "and $\\nabla^2\\log\\mathfrak{M}(0)$ to produce auditable invariants.}"
    )
    lines.append("\\label{tab:real-input-40-local-bigeometry-invariants}")
    lines.append("\\begin{tabular}{@{}l r@{}}")
    lines.append("\\toprule")
    lines.append("Quantity & Value\\\\")
    lines.append("\\midrule")
    lines.append(f"$\\mu$ (projection coefficient) & {_fmt(inv.mu, 7)}\\\\")
    lines.append(f"$v_\\perp$ (Euclidean, isobaric drift) & $({_fmt(inv.v_perp[0],6)},\\ {_fmt(inv.v_perp[1],6)},\\ {_fmt(inv.v_perp[2],6)})$\\\\")
    lines.append(f"$\\|v_\\perp\\|$ & {_fmt(inv.v_perp_norm, 6)}\\\\")
    lines.append(
        f"$u_+$ (scaled $(u_+)_{{\\theta_2}}=-1$) & "
        f"$({_fmt(inv.u_plus_theta2_minus1[0],3)},\\ {_fmt(inv.u_plus_theta2_minus1[1],3)},\\ {_fmt(inv.u_plus_theta2_minus1[2],0)})$\\\\"
    )
    lines.append(f"$\\cos(v_\\perp,u_+)$ (Euclidean) & {_fmt(inv.cos_vperp_u_plus, 6)}\\\\")
    lines.append("\\midrule")
    lines.append(f"$\\rho_{{e,-}}$ & {_fmt(rho_e_minus, 6)}\\\\")
    lines.append(f"$\\rho_{{e,2}}$ & {_fmt(rho_e_2, 6)}\\\\")
    lines.append(f"$\\rho_{{-,2}}$ & {_fmt(rho_minus_2, 6)}\\\\")
    lines.append("\\midrule")
    lines.append(f"$\\rho_{{e,-\\mid 2}}$ & {_fmt(pr_e_minus_given_2, 6)}\\\\")
    lines.append(f"$\\rho_{{e,2\\mid -}}$ & {_fmt(pr_e_2_given_minus, 6)}\\\\")
    lines.append(f"$\\rho_{{-,2\\mid e}}$ & {_fmt(pr_minus_2_given_e, 6)}\\\\")
    lines.append("\\midrule")
    lines.append(f"eigs of $\\Sigma^{{-1}}\\nabla^2\\log\\mathfrak{{M}}(0)$ & $({_fmt(mu1,6)},\\ {_fmt(mu2,6)},\\ {_fmt(mu3,6)})$\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute local bi-geometry invariants at theta=0.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_local_bigeometry_invariants.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_local_bigeometry_invariants.tex"),
        help="Output LaTeX table path.",
    )
    args = parser.parse_args()

    inv = compute()

    payload: Dict[str, object] = {
        "mu": inv.mu,
        "v_perp": inv.v_perp,
        "v_perp_norm": inv.v_perp_norm,
        "u_plus_theta2_minus1": inv.u_plus_theta2_minus1,
        "cos_vperp_u_plus": inv.cos_vperp_u_plus,
        "corr": inv.corr,
        "partial_corr": inv.partial_corr,
        "eigs_sigma_inv_hlogm": inv.eigs_sigma_inv_hlogm,
        "source": {
            "pressure_json": "artifacts/export/sync_kernel_real_input_40.json",
            "logm_json": "artifacts/export/sync_kernel_real_input_40_logM_theta_taylor.json",
        },
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"[local-bigeometry] wrote {jout}", flush=True)

    write_table_tex(Path(args.tex_out), inv)
    print(f"[local-bigeometry] wrote {args.tex_out}", flush=True)


if __name__ == "__main__":
    main()

