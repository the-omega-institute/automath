#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Covariance (pressure Hessian) predicts the worst character direction.

We consider the real-input 40-state kernel with 3 additive one-step cocycles:
  chi = e - 1_{d=2}          (signed arity charge)
  nu  = 1_{dst in Q_-}       (negative-carry zone indicator)
  xi  = 1_{d=2}              (collision trigger count)

Define the positive-weighted matrix (real theta):
  M(theta) has entries exp(theta1*chi + theta2*nu + theta3*xi),
and the pressure:
  P(theta) = log rho(M(theta)).

Then the Hessian Σ := ∇^2 P(0) is the asymptotic covariance matrix of (chi,nu,xi),
and controls small-angle unit-circle twists u = exp(i t):
  Re log( rho(exp(i t)) / lambda ) = - (1/2) t^T Σ t + O(|t|^3).

For a finite modulus triple (m1,m2,m3), character angles are:
  t(j) = (2π j1/m1, 2π j2/m2, 2π j3/m3).
Hence the worst (largest) twisted spectral radius is predicted by minimizing t^T Σ t
over nontrivial indices j != 0.

This script computes Σ by finite differences and compares:
  - predicted worst index (min quadratic form)
  - actual worst index from artifacts/export/sync_kernel_real_input_40_arity_3d.json

Outputs (default):
  - artifacts/export/real_input_40_covariance_worst_character.json
  - sections/generated/tab_real_input_40_covariance_worst_character.tex

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


def _load_json(rel: str) -> dict:
    p = paper_root() / rel
    return json.loads(p.read_text(encoding="utf-8"))


KERNEL_STATES = [
    "000",
    "001",
    "002",
    "010",
    "100",
    "101",
    "0-12",
    "1-12",
    "01-1",
    "11-1",
]


def build_kernel_edges() -> List[Tuple[str, str, int, int]]:
    edges: List[Tuple[str, str, int, int]] = []
    for d in (0, 1, 2):
        edges.append(("000", f"00{d}", d, 0))
    for d in (0, 1, 2):
        edges.append(("100", f"00{d}", d, 1))
    edges += [
        ("001", "010", 0, 0),
        ("001", "100", 1, 0),
        ("001", "101", 2, 0),
        ("002", "11-1", 0, 0),
        ("002", "000", 1, 1),
        ("002", "001", 2, 1),
        ("010", "100", 0, 0),
        ("010", "101", 1, 0),
        ("010", "0-12", 2, 1),
        ("101", "010", 0, 1),
        ("101", "100", 1, 1),
        ("101", "101", 2, 1),
        ("0-12", "01-1", 0, 0),
        ("0-12", "010", 1, 0),
        ("0-12", "100", 2, 0),
        ("1-12", "01-1", 0, 1),
        ("1-12", "010", 1, 1),
        ("1-12", "100", 2, 1),
        ("01-1", "001", 0, 0),
        ("01-1", "002", 1, 0),
        ("01-1", "1-12", 2, 0),
        ("11-1", "001", 0, 1),
        ("11-1", "002", 1, 1),
        ("11-1", "1-12", 2, 1),
    ]
    return edges


def build_real_input_states() -> List[Tuple[str, int, int]]:
    out: List[Tuple[str, int, int]] = []
    for s in KERNEL_STATES:
        for px in (0, 1):
            for py in (0, 1):
                out.append((s, px, py))
    return out


def build_kernel_map(edges: List[Tuple[str, str, int, int]]) -> Dict[Tuple[str, int], Tuple[str, int]]:
    return {(src, d): (dst, e) for (src, dst, d, e) in edges}


def weighted_matrix(theta1: float, theta2: float, theta3: float, *, third_axis: str) -> np.ndarray:
    states = build_real_input_states()
    kernel_map = build_kernel_map(build_kernel_edges())
    idx = {st: i for i, st in enumerate(states)}
    n = len(states)
    M = np.zeros((n, n), dtype=float)
    for s, px, py in states:
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, e = kernel_map[(s, d)]
                chi = e - (1 if d == 2 else 0)
                nu = 1 if "-" in dst_state else 0
                if third_axis == "N2":
                    xi = 1 if d == 2 else 0
                elif third_axis == "Ne":
                    xi = int(e)
                else:
                    raise ValueError(f"invalid third_axis: {third_axis}")
                w = math.exp(theta1 * chi + theta2 * nu + theta3 * xi)
                i = idx[(s, px, py)]
                j = idx[(dst_state, x, y)]
                M[i, j] += w
    return M


def spectral_radius(M: np.ndarray) -> float:
    vals = np.linalg.eigvals(M)
    return float(np.max(np.abs(vals)))


def P(theta: Tuple[float, float, float], third_axis: str) -> float:
    M = weighted_matrix(theta[0], theta[1], theta[2], third_axis=third_axis)
    return math.log(spectral_radius(M))


def hessian_central(third_axis: str, h: float) -> np.ndarray:
    # 3D central finite differences at 0.
    def P1(t1: float, t2: float, t3: float) -> float:
        return P((t1, t2, t3), third_axis=third_axis)

    H = np.zeros((3, 3), dtype=float)
    # diagonal second derivatives
    for i in range(3):
        vec = [0.0, 0.0, 0.0]
        vec[i] = h
        fph = P1(vec[0], vec[1], vec[2])
        f0 = P1(0.0, 0.0, 0.0)
        vec[i] = -h
        fmh = P1(vec[0], vec[1], vec[2])
        H[i, i] = (fph - 2.0 * f0 + fmh) / (h * h)
    # mixed second derivatives
    for i in range(3):
        for j in range(i + 1, 3):
            def f(a: float, b: float) -> float:
                t = [0.0, 0.0, 0.0]
                t[i] = a
                t[j] = b
                return P1(t[0], t[1], t[2])

            val = (f(h, h) - f(h, -h) - f(-h, h) + f(-h, -h)) / (4.0 * h * h)
            H[i, j] = val
            H[j, i] = val
    return H


def parse_triple_key(key: str) -> Tuple[int, int, int]:
    a, b, c = (int(x) for x in key.split("x"))
    return a, b, c


def parse_idx(key: str) -> Tuple[int, int, int]:
    a, b, c = (int(x) for x in key.split(","))
    return a, b, c


def main() -> None:
    parser = argparse.ArgumentParser(description="Covariance predicts worst character (real-input 40).")
    parser.add_argument("--triple", type=str, default="3x3x5", help="Triple key in 3D arity JSON (default: 3x3x5)")
    parser.add_argument("--third-axis", type=str, default="N2", choices=["N2", "Ne"])
    parser.add_argument("--h", type=float, default=1e-4, help="Finite difference step for Hessian.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_covariance_worst_character.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_covariance_worst_character.tex"),
    )
    args = parser.parse_args()

    m1, m2, m3 = parse_triple_key(str(args.triple))
    j3 = _load_json("artifacts/export/sync_kernel_real_input_40_arity_3d.json")
    if "triple_rho" not in j3 or str(args.triple) not in j3["triple_rho"]:
        raise SystemExit(f"Missing triple_rho[{args.triple}] in 3D JSON.")

    # Actual worst (from scanned characters).
    rho_map: Dict[str, float] = j3["triple_rho"][str(args.triple)]
    rho_max = float(j3["triple_rho_max"][str(args.triple)])
    # Collect indices within tiny tolerance of max.
    near = []
    for k, v in rho_map.items():
        if abs(float(v) - rho_max) <= 1e-12:
            near.append(k)
    near = sorted(near)

    # Hessian / covariance matrix.
    Sigma = hessian_central(third_axis=str(args.third_axis), h=float(args.h))
    evals, evecs = np.linalg.eigh(Sigma)
    # Correlations (dimensionless).
    corr_nu_xi = float(Sigma[1, 2] / math.sqrt(Sigma[1, 1] * Sigma[2, 2]))

    # Predicted worst index: minimize t^T Sigma t over nontrivial j.
    best_val = float("inf")
    best_j: Tuple[int, int, int] | None = None
    for j1 in range(m1):
        for j2 in range(m2):
            for j3i in range(m3):
                if j1 == 0 and j2 == 0 and j3i == 0:
                    continue
                t = np.array([2.0 * math.pi * j1 / m1, 2.0 * math.pi * j2 / m2, 2.0 * math.pi * j3i / m3])
                q = float(t @ Sigma @ t)
                if q < best_val:
                    best_val = q
                    best_j = (j1, j2, j3i)

    assert best_j is not None

    payload = {
        "triple": str(args.triple),
        "third_axis": str(args.third_axis),
        "h": float(args.h),
        "rho_max_actual": rho_max,
        "worst_indices_actual": near,
        "Sigma": Sigma.tolist(),
        "Sigma_eigenvalues": [float(x) for x in evals.tolist()],
        "predicted_min_quadratic_form": best_val,
        "predicted_worst_index": list(best_j),
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[cov-worst] wrote {jout}", flush=True)

    # LaTeX table (compact).
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Covariance prediction of the worst character direction. "
        "$\\Sigma=\\nabla^2 P(0)$ is computed by finite differences for the three cocycles "
        "$(\\chi,\\nu,\\xi)$ with $\\xi$ the chosen third axis. "
        "The predicted worst index minimizes $t(j)^\\top\\Sigma t(j)$ with $t(j)=(2\\pi j_1/m_1,2\\pi j_2/m_2,2\\pi j_3/m_3)$.}"
    )
    lines.append("\\label{tab:real_input_40_covariance_worst_character}")
    lines.append("\\begin{tabular}{l l l}")
    lines.append("\\toprule")
    lines.append("triple & predicted worst $j$ & actual worst $j$ (scan)\\\\")
    lines.append("\\midrule")
    pred = f"({best_j[0]},{best_j[1]},{best_j[2]})"
    act = ", ".join(f"({k})" for k in near) if near else "(none)"
    lines.append(f"{args.triple} & {pred} & {act}\\\\")
    lines.append("\\midrule")
    lines.append(
        f"$\\rho_{{\\max}}$ (scan) & \\multicolumn{{2}}{{l}}{{{rho_max:.12f}}}\\\\"
    )
    lines.append(
        f"$\\lambda$ (untwisted) & \\multicolumn{{2}}{{l}}{{3}}\\\\"
    )
    lines.append("\\midrule")
    lines.append(
        "$\\Sigma$ & \\multicolumn{2}{l}{$\\begin{smallmatrix}"
        + f"{Sigma[0,0]:.6g}&{Sigma[0,1]:.6g}&{Sigma[0,2]:.6g}\\\\"
        + f"{Sigma[1,0]:.6g}&{Sigma[1,1]:.6g}&{Sigma[1,2]:.6g}\\\\"
        + f"{Sigma[2,0]:.6g}&{Sigma[2,1]:.6g}&{Sigma[2,2]:.6g}"
        + "\\end{smallmatrix}$}\\\\"
    )
    lines.append(
        f"$\\mathrm{{Corr}}(\\nu,\\xi)$ & \\multicolumn{{2}}{{l}}{{{corr_nu_xi:.6f}}}\\\\"
    )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tex = Path(args.tex_out)
    tex.parent.mkdir(parents=True, exist_ok=True)
    tex.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[cov-worst] wrote {tex}", flush=True)


if __name__ == "__main__":
    main()

