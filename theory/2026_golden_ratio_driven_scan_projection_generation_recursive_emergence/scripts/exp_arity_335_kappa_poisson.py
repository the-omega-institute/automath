#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Compute the near-coboundary quadratic-law constant kappa via a Poisson equation.

Context:
For the real-input 40-state kernel, the slowest twisted ratio for ((3,3,p)) with
third axis N2 mod p is governed by the collision cocycle:
  xi(e) = 1_{d=2}.

In the small-angle regime, we have
  log( rho(theta) / lambda ) = - (sigma_xi^2/2) * theta^2 + O(theta^3),
so the quadratic-law constant is
  kappa_infty = sigma_xi^2 / 2.

This script computes sigma_xi^2 *directly* from the Markov chain induced by the
untwisted PF/Parry structure on the kernel graph, via the variational formula:
  sigma_xi^2 = inf_f E_pi[(xi - mu + f(j)-f(i))^2],
where the minimizer solves the Poisson equation (I - P) f = b under pi-mean 0.

We compare:
  - kappa_poisson = sigma_xi^2 / 2  (exact from linear solve)
  - kappa_var     = P''(0)/2        (finite-difference pressure method)
  - kappa_5_lin/log from the discrete twist ratio rho_{3,3,5}/lambda

Outputs:
  - artifacts/export/arity_335_kappa_poisson.json
  - sections/generated/eq_arity_335_kappa_poisson.tex

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

# Reuse the canonical 40-state kernel construction from the reproducible pipeline.
import exp_sync_kernel_real_input_40_arity_3d as ar3d


def _phi() -> float:
    return (1.0 + 5.0**0.5) / 2.0


def _lam() -> float:
    p = _phi()
    return p * p


@dataclass(frozen=True)
class Edge:
    src: int
    dst: int
    xi: int  # collision cocycle 1_{d=2}


def _build_edges(states: List[Tuple[str, int, int]], kernel_map: Dict[Tuple[str, int], Tuple[str, int]]) -> List[Edge]:
    idx = {st: i for i, st in enumerate(states)}
    edges: List[Edge] = []
    for s, px, py in states:
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, _e = kernel_map[(s, d)]
                src_i = idx[(s, px, py)]
                dst_i = idx[(dst_state, x, y)]
                xi = 1 if d == 2 else 0
                edges.append(Edge(src=src_i, dst=dst_i, xi=xi))
    return edges


def _adjacency_from_edges(n: int, edges: List[Edge]) -> np.ndarray:
    A = np.zeros((n, n), dtype=float)
    for e in edges:
        A[e.src, e.dst] += 1.0
    return A


def _pf_eigenvectors(A: np.ndarray) -> Tuple[float, np.ndarray, np.ndarray]:
    # Right eigenvector
    vals, vecs = np.linalg.eig(A)
    i0 = int(np.argmax(np.real(vals)))
    lam = float(np.real(vals[i0]))
    r = np.real(vecs[:, i0]).astype(float)
    # Left eigenvector
    valsL, vecsL = np.linalg.eig(A.T)
    j0 = int(np.argmax(np.real(valsL)))
    l = np.real(vecsL[:, j0]).astype(float)

    # Fix signs (PF vectors should be nonnegative; eigenvectors are defined up to sign).
    if float(np.sum(r)) < 0.0:
        r = -r
    if float(np.sum(l)) < 0.0:
        l = -l

    # Normalize l^T r = 1
    lr = float(l @ r)
    if lr == 0.0:
        raise RuntimeError("PF normalization failed: l^T r = 0")
    l = l / lr
    return lam, l, r


def _parry_chain(A: np.ndarray, lam: float, l: np.ndarray, r: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    n = A.shape[0]
    P = np.zeros((n, n), dtype=float)
    for i in range(n):
        if r[i] <= 0.0:
            continue
        for j in range(n):
            aij = A[i, j]
            if aij == 0.0:
                continue
            P[i, j] = aij * r[j] / (lam * r[i])
    # Stationary distribution on states
    pi = (l * r).astype(float)
    s = float(np.sum(pi))
    if s <= 0.0:
        raise RuntimeError("Invalid stationary mass")
    pi = pi / s
    return P, pi


def _edge_weight(l: np.ndarray, r: np.ndarray, lam: float, src: int, dst: int) -> float:
    # Parry edge measure for each parallel edge: m(e) = l_src * r_dst / lam, with l^T r = 1.
    return float(l[src] * r[dst] / lam)


def _mu_edge_mean(edges: List[Edge], l: np.ndarray, r: np.ndarray, lam: float) -> float:
    mu = 0.0
    for e in edges:
        mu += _edge_weight(l, r, lam, e.src, e.dst) * float(e.xi)
    return float(mu)


def _solve_poisson(P: np.ndarray, pi: np.ndarray, b: np.ndarray) -> np.ndarray:
    # Solve (I - P) f = b with gauge constraint pi^T f = 0.
    n = P.shape[0]
    I = np.eye(n, dtype=float)
    A = I - P
    # Augment with Lagrange multiplier alpha:
    # [A  pi] [f]   [b]
    # [pi^T 0] [a] = [0]
    M = np.zeros((n + 1, n + 1), dtype=float)
    M[:n, :n] = A
    M[:n, n] = pi
    M[n, :n] = pi
    rhs = np.zeros((n + 1,), dtype=float)
    rhs[:n] = b
    sol = np.linalg.solve(M, rhs)
    f = sol[:n]
    # Numerical sanity: enforce exact gauge (project out mean)
    f = f - float(pi @ f)
    return f


def _sigma2_from_f(edges: List[Edge], l: np.ndarray, r: np.ndarray, lam: float, mu: float, f: np.ndarray) -> float:
    s = 0.0
    for e in edges:
        w = _edge_weight(l, r, lam, e.src, e.dst)
        d = float(e.xi) - mu + float(f[e.dst] - f[e.src])
        s += w * d * d
    return float(s)


def _lambda_of_t(states, kernel_map, t: float) -> float:
    u = math.exp(t)
    M = ar3d.build_weighted_matrix_numeric(
        1.0 + 0.0j,
        1.0 + 0.0j,
        u + 0.0j,
        states,
        kernel_map,
        third_axis="N2",
    )
    # Spectral radius
    vals = np.linalg.eigvals(M)
    return float(np.max(np.abs(vals)))


def write_eq_tex(path: Path, payload: dict) -> None:
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_arity_335_kappa_poisson.py")
    lines.append("\\paragraph{Poisson 方程给出的二次律常数（可复现）}")
    lines.append("对无扭曲 PF/Parry 马尔可夫链解 Poisson 方程 $(I-P)f=b$ 得到有效方差密度 $\\sigma_\\xi^2$，并令 $\\kappa_\\infty:=\\sigma_\\xi^2/2$。数值上：")
    lines.append("$$")
    lines.append(
        rf"\sigma_\xi^2\approx {payload['sigma2_poisson']:.12f},\qquad "
        rf"\kappa_\infty\approx {payload['kappa_poisson']:.12f}."
    )
    lines.append("$$")
    lines.append("与压力二阶导数的差分估计 $\\sigma_\\xi^2\\approx P''(0)$（同一核、同一 cocycle）对照：")
    lines.append("$$")
    lines.append(
        rf"\sigma_\xi^2\_{{\mathrm{{var}}}}\approx {payload['sigma2_pressure_fd']:.12f},\qquad "
        rf"\kappa\_{{\mathrm{{var}}}}\approx {payload['kappa_pressure_fd']:.12f},\qquad "
        rf"|\kappa\_{{\mathrm{{var}}}}-\kappa_\infty|\approx {payload['kappa_abs_diff']:.3e}."
    )
    lines.append("$$")
    lines.append("并以 $p=5$ 的离散角 $\\theta_5=2\\pi/5$ 的最坏扭曲比值 $\\rho_{3,3,5}/\\lambda$ 作小角二次律对照：")
    lines.append("$$")
    lines.append("\\begin{aligned}")
    lines.append(rf"\rho_{{3,3,5}}/\lambda&\approx {payload['rho_ratio_p5']:.12f},\\\\")
    lines.append(
        rf"\kappa\_5^{{(\mathrm{{lin}})}}&:=\frac{{1-\rho/\lambda}}{{\theta_5^2}}\approx {payload['kappa_p5_lin']:.12f},\\\\"
    )
    lines.append(
        rf"\kappa\_5^{{(\mathrm{{log}})}}&:=-\frac{{\log(\rho/\lambda)}}{{\theta_5^2}}\approx {payload['kappa_p5_log']:.12f}."
    )
    lines.append("\\end{aligned}")
    lines.append("$$")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute kappa via Poisson equation for the (3,3,p) collision cocycle.")
    parser.add_argument(
        "--arity-3d-n2-json",
        type=str,
        default=str(export_dir() / "sync_kernel_real_input_40_arity_3d_N2_335.json"),
        help="Input JSON containing rho_{3,3,5}/lambda for N2 third axis.",
    )
    parser.add_argument("--h", type=float, default=1e-3, help="Step for pressure finite-difference.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "arity_335_kappa_poisson.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_arity_335_kappa_poisson.tex"),
    )
    args = parser.parse_args()

    lam_target = _lam()
    states = ar3d.build_real_input_states()
    kernel_map = ar3d.build_kernel_map(ar3d.build_kernel_edges())
    edges = _build_edges(states, kernel_map)
    n = len(states)

    A = _adjacency_from_edges(n, edges)
    lam_pf, lvec, rvec = _pf_eigenvectors(A)
    # Sanity: lam_pf should match phi^2.
    lam_err = abs(lam_pf - lam_target)

    P, pi = _parry_chain(A, lam_pf, lvec, rvec)
    mu = _mu_edge_mean(edges, lvec, rvec, lam_pf)

    # b_i = E[xi - mu | state i] under Parry chain.
    b = np.zeros((n,), dtype=float)
    # Each edge from i to j has conditional probability r_j/(lam r_i), independent of parallel-edge index.
    for e in edges:
        b[e.src] += (rvec[e.dst] / (lam_pf * rvec[e.src])) * (float(e.xi) - mu)

    f = _solve_poisson(P, pi, b)
    sigma2_poisson = _sigma2_from_f(edges, lvec, rvec, lam_pf, mu, f)
    kappa_poisson = 0.5 * sigma2_poisson

    # Pressure second derivative check: P(t)=log rho(M(1,1,exp(t))) with third_axis N2.
    h = float(args.h)
    lam0 = _lambda_of_t(states, kernel_map, 0.0)
    P0 = math.log(lam0)
    Pp = math.log(_lambda_of_t(states, kernel_map, +h))
    Pm = math.log(_lambda_of_t(states, kernel_map, -h))
    sigma2_fd = (Pp - 2.0 * P0 + Pm) / (h * h)
    kappa_fd = 0.5 * sigma2_fd

    # Discrete p=5 comparison from JSON rho ratio.
    rho_ratio_p5 = float("nan")
    p5_path = Path(args.arity_3d_n2_json)
    if p5_path.is_file():
        data = json.loads(p5_path.read_text(encoding="utf-8"))
        rho_map = data["triple_rho"]["3x3x5"]
        rho_max = max(float(v) for v in rho_map.values())
        rho_ratio_p5 = rho_max / lam_target
    theta5 = 2.0 * math.pi / 5.0
    kappa_p5_lin = (1.0 - rho_ratio_p5) / (theta5 * theta5) if 0.0 < rho_ratio_p5 < 1.0 else float("nan")
    kappa_p5_log = (-math.log(rho_ratio_p5)) / (theta5 * theta5) if 0.0 < rho_ratio_p5 < 1.0 else float("nan")

    payload = {
        "n_states": n,
        "n_edges": len(edges),
        "lambda_target": lam_target,
        "lambda_pf": lam_pf,
        "lambda_abs_err": lam_err,
        "mu_edge_mean": mu,
        "sigma2_poisson": float(sigma2_poisson),
        "kappa_poisson": float(kappa_poisson),
        "sigma2_pressure_fd": float(sigma2_fd),
        "kappa_pressure_fd": float(kappa_fd),
        "kappa_abs_diff": float(abs(kappa_fd - kappa_poisson)),
        "pressure_fd_h": h,
        "rho_ratio_p5": float(rho_ratio_p5),
        "theta5": theta5,
        "kappa_p5_lin": float(kappa_p5_lin),
        "kappa_p5_log": float(kappa_p5_log),
    }

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[kappa-poisson] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_eq_tex(tout, payload)
    print(f"[kappa-poisson] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

