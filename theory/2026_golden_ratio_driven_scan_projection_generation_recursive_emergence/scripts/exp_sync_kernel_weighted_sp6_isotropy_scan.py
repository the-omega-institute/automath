#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Scan (u,v,w) for an Sp(6)-isotropy point in the 3D weighted sync-kernel pressure.

We work with the 10-state sync-kernel SFT and its 3-parameter positive weighting:
  u = exp(theta_e)     (output-bit cocycle)
  v = exp(theta_neg)   (negative-zone indicator)
  w = exp(theta_2)     (input-is-2 indicator)

Define the pressure:
  P(theta) := log rho(B(theta)),
and the Fisher / covariance matrix:
  Sigma(theta) := ∇^2 P(theta)  (3×3).

PW / higher-gauge motivated "Sp(6) isotropy" test (minimal, auditable):
  - Promote Sigma to a 6×6 phase-space covariance C := diag(Sigma, Sigma)
    on coordinates (theta; J) with canonical symplectic form ω = dθ ∧ dJ.
  - The Williamson (symplectic) eigenvalues of C are exactly the eigenvalues of Sigma.
  - Hence "Sp(6)-isotropy" at theta means: Sigma has one scale, i.e. its three
    eigenvalues are (numerically) equal.

This script scans a rectangular grid in (u,v,w), evaluates Sigma(theta) by central
finite differences at each grid point, and reports the best candidates minimizing:
  score := log( max(eigs(Sigma)) / min(eigs(Sigma)) ).

Outputs (default):
  - artifacts/export/sync_kernel_weighted_sp6_isotropy_scan.json
  - sections/generated/tab_sync_kernel_weighted_sp6_isotropy_scan.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


@dataclass(frozen=True)
class Edge:
    src: str
    dst: str
    d: int
    e: int


STATES = [
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


def build_edges() -> List[Edge]:
    edges: List[Edge] = []
    for d in (0, 1, 2):
        edges.append(Edge("000", f"00{d}", d, 0))
    for d in (0, 1, 2):
        edges.append(Edge("100", f"00{d}", d, 1))
    edges += [
        Edge("001", "010", 0, 0),
        Edge("001", "100", 1, 0),
        Edge("001", "101", 2, 0),
        Edge("002", "11-1", 0, 0),
        Edge("002", "000", 1, 1),
        Edge("002", "001", 2, 1),
        Edge("010", "100", 0, 0),
        Edge("010", "101", 1, 0),
        Edge("010", "0-12", 2, 1),
        Edge("101", "010", 0, 1),
        Edge("101", "100", 1, 1),
        Edge("101", "101", 2, 1),
        Edge("0-12", "01-1", 0, 0),
        Edge("0-12", "010", 1, 0),
        Edge("0-12", "100", 2, 0),
        Edge("1-12", "01-1", 0, 1),
        Edge("1-12", "010", 1, 1),
        Edge("1-12", "100", 2, 1),
        Edge("01-1", "001", 0, 0),
        Edge("01-1", "002", 1, 0),
        Edge("01-1", "1-12", 2, 0),
        Edge("11-1", "001", 0, 1),
        Edge("11-1", "002", 1, 1),
        Edge("11-1", "1-12", 2, 1),
    ]
    return edges


def weighted_matrix(theta_e: float, theta_neg: float, theta_2: float, edges: List[Edge]) -> np.ndarray:
    idx = {s: i for i, s in enumerate(STATES)}
    n = len(STATES)
    u = math.exp(theta_e)
    v = math.exp(theta_neg)
    w = math.exp(theta_2)
    B = np.zeros((n, n), dtype=float)
    for edge in edges:
        i = idx[edge.src]
        j = idx[edge.dst]
        neg = 1 if "-" in edge.dst else 0
        two = 1 if edge.d == 2 else 0
        weight = (u**edge.e) * (v**neg) * (w**two)
        B[i, j] += weight
    return B


def spectral_radius(B: np.ndarray) -> float:
    vals = np.linalg.eigvals(B)
    return float(np.max(np.abs(vals)))


def pressure(theta_e: float, theta_neg: float, theta_2: float, edges: List[Edge]) -> float:
    B = weighted_matrix(theta_e, theta_neg, theta_2, edges)
    lam = spectral_radius(B)
    return math.log(lam)


def _grid_linspace(min_val: float, max_val: float, steps: int) -> np.ndarray:
    if steps <= 0:
        raise ValueError("steps must be positive")
    if steps == 1:
        return np.array([0.5 * (min_val + max_val)], dtype=float)
    return np.linspace(min_val, max_val, num=int(steps), dtype=float)


def _finite_diff_values(
    theta: Tuple[float, float, float],
    h: float,
    edges: List[Edge],
) -> Dict[Tuple[int, int, int], float]:
    """Cache pressure evaluations on the +/-1 stencil for 3D Hessian."""
    if not (h > 0.0 and math.isfinite(h)):
        raise ValueError("h must be positive and finite")
    t0, t1, t2 = theta
    vals: Dict[Tuple[int, int, int], float] = {}

    def P_at(oe: int, on: int, o2: int) -> float:
        key = (oe, on, o2)
        if key in vals:
            return vals[key]
        th0 = t0 + float(oe) * h
        th1 = t1 + float(on) * h
        th2 = t2 + float(o2) * h
        v = pressure(th0, th1, th2, edges)
        vals[key] = float(v)
        return float(v)

    # Base.
    P_at(0, 0, 0)
    # Axes.
    for i in (-1, 1):
        P_at(i, 0, 0)
        P_at(0, i, 0)
        P_at(0, 0, i)
    # Mixed (4 corners per pair).
    for a in (-1, 1):
        for b in (-1, 1):
            P_at(a, b, 0)  # (e,neg)
            P_at(a, 0, b)  # (e,2)
            P_at(0, a, b)  # (neg,2)
    return vals


def grad_and_hessian_central(theta: Tuple[float, float, float], *, h: float, edges: List[Edge]) -> Tuple[np.ndarray, np.ndarray, float]:
    """Return (grad, Hessian, P(theta)) using central finite differences at theta."""
    vals = _finite_diff_values(theta, h=h, edges=edges)
    f0 = vals[(0, 0, 0)]

    # Gradient: ∂i f ≈ (f(+h)-f(-h))/2h
    g = np.zeros((3,), dtype=float)
    g[0] = (vals[(1, 0, 0)] - vals[(-1, 0, 0)]) / (2.0 * h)
    g[1] = (vals[(0, 1, 0)] - vals[(0, -1, 0)]) / (2.0 * h)
    g[2] = (vals[(0, 0, 1)] - vals[(0, 0, -1)]) / (2.0 * h)

    # Hessian diag: ∂ii f ≈ (f(+h)-2f(0)+f(-h))/h^2
    H = np.zeros((3, 3), dtype=float)
    H[0, 0] = (vals[(1, 0, 0)] - 2.0 * f0 + vals[(-1, 0, 0)]) / (h * h)
    H[1, 1] = (vals[(0, 1, 0)] - 2.0 * f0 + vals[(0, -1, 0)]) / (h * h)
    H[2, 2] = (vals[(0, 0, 1)] - 2.0 * f0 + vals[(0, 0, -1)]) / (h * h)

    # Mixed: ∂ij f ≈ (f(++ )-f(+-)-f(-+)+f(--))/4h^2
    H[0, 1] = (vals[(1, 1, 0)] - vals[(1, -1, 0)] - vals[(-1, 1, 0)] + vals[(-1, -1, 0)]) / (4.0 * h * h)
    H[1, 0] = H[0, 1]
    H[0, 2] = (vals[(1, 0, 1)] - vals[(1, 0, -1)] - vals[(-1, 0, 1)] + vals[(-1, 0, -1)]) / (4.0 * h * h)
    H[2, 0] = H[0, 2]
    H[1, 2] = (vals[(0, 1, 1)] - vals[(0, 1, -1)] - vals[(0, -1, 1)] + vals[(0, -1, -1)]) / (4.0 * h * h)
    H[2, 1] = H[1, 2]

    return g, H, float(f0)


def _is_spd_symmetric(H: np.ndarray, *, tol: float = 1e-12) -> bool:
    if H.shape != (3, 3):
        return False
    if not np.all(np.isfinite(H)):
        return False
    if float(np.max(np.abs(H - H.T))) > tol:
        return False
    evals = np.linalg.eigvalsh(H)
    return bool(float(np.min(evals)) > 0.0)


def _score_isotropy_from_eigs(eigs: np.ndarray) -> float:
    # score = log(max/min). This is 0 iff all eigenvalues equal.
    mn = float(np.min(eigs))
    mx = float(np.max(eigs))
    if not (mn > 0.0 and mx > 0.0 and math.isfinite(mn) and math.isfinite(mx)):
        return float("inf")
    return float(math.log(mx / mn))


def _tex_table(path: Path, rows: List[dict]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Sp(6)-isotropy scan for the 3D weighted sync-kernel pressure. "
        "At each grid point $(u,v,w)$ we compute $\\Sigma=\\nabla^2P(\\theta)$ "
        "(Fisher/covariance in $\\theta=(\\log u,\\log v,\\log w)$) by central finite differences, "
        "and report the best candidates minimizing $\\log(\\lambda_{\\max}/\\lambda_{\\min})$ "
        "over eigenvalues of $\\Sigma$.}"
    )
    lines.append("\\label{tab:sync_kernel_weighted_sp6_isotropy_scan}")
    lines.append("\\begin{tabular}{r r r r r}")
    lines.append("\\toprule")
    lines.append("$u$ & $v$ & $w$ & eigs$(\\Sigma)$ & $\\log(\\lambda_{\\max}/\\lambda_{\\min})$\\\\")
    lines.append("\\midrule")
    for r in rows:
        u = float(r["weights"]["u"])
        v = float(r["weights"]["v"])
        w = float(r["weights"]["w"])
        e = [float(x) for x in r["sigma_eigenvalues"]]
        score = float(r["isotropy_score_log_ratio"])
        eigs_tex = f"({e[0]:.4g},{e[1]:.4g},{e[2]:.4g})"
        lines.append(f"{u:.6g} & {v:.6g} & {w:.6g} & {eigs_tex} & {score:.6g}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Scan (u,v,w) for Sp(6)-isotropy via the pressure Hessian eigenvalues.")
    ap.add_argument("--u-min", type=float, default=0.5, help="Minimum u in scan (u>0).")
    ap.add_argument("--u-max", type=float, default=1.5, help="Maximum u in scan.")
    ap.add_argument("--u-steps", type=int, default=11, help="Number of u grid points.")
    ap.add_argument("--v-min", type=float, default=0.5, help="Minimum v in scan (v>0).")
    ap.add_argument("--v-max", type=float, default=1.5, help="Maximum v in scan.")
    ap.add_argument("--v-steps", type=int, default=11, help="Number of v grid points.")
    ap.add_argument("--w-min", type=float, default=0.3, help="Minimum w in scan (w>0).")
    ap.add_argument("--w-max", type=float, default=1.5, help="Maximum w in scan.")
    ap.add_argument("--w-steps", type=int, default=13, help="Number of w grid points.")
    ap.add_argument("--h", type=float, default=2e-4, help="Central finite difference step in theta=log(weight).")
    ap.add_argument("--top-k", type=int, default=20, help="Report the top-K best candidates.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_weighted_sp6_isotropy_scan.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_weighted_sp6_isotropy_scan.tex"),
    )
    args = ap.parse_args()

    if not (args.u_min > 0.0 and args.v_min > 0.0 and args.w_min > 0.0):
        raise SystemExit("Require u_min,v_min,w_min > 0.")
    if not (args.u_max > 0.0 and args.v_max > 0.0 and args.w_max > 0.0):
        raise SystemExit("Require u_max,v_max,w_max > 0.")
    if int(args.top_k) <= 0:
        raise SystemExit("Require --top-k >= 1.")

    edges = build_edges()
    prog = Progress(label="sp6-isotropy-scan", every_seconds=10.0)

    u_grid = _grid_linspace(float(args.u_min), float(args.u_max), int(args.u_steps))
    v_grid = _grid_linspace(float(args.v_min), float(args.v_max), int(args.v_steps))
    w_grid = _grid_linspace(float(args.w_min), float(args.w_max), int(args.w_steps))

    total = int(len(u_grid) * len(v_grid) * len(w_grid))
    scanned = 0
    skipped_nonspd = 0

    best: List[dict] = []
    worst_score = float("inf")

    def maybe_add(rec: dict) -> None:
        nonlocal best, worst_score
        best.append(rec)
        best.sort(key=lambda r: float(r["isotropy_score_log_ratio"]))
        if len(best) > int(args.top_k):
            best = best[: int(args.top_k)]
        worst_score = float(best[-1]["isotropy_score_log_ratio"]) if best else float("inf")

    for u in u_grid:
        for v in v_grid:
            for w in w_grid:
                scanned += 1
                theta = (math.log(float(u)), math.log(float(v)), math.log(float(w)))
                g, H, P0 = grad_and_hessian_central(theta, h=float(args.h), edges=edges)
                if not _is_spd_symmetric(H):
                    skipped_nonspd += 1
                    prog.tick(f"scanned={scanned}/{total} skipped_nonspd={skipped_nonspd}")
                    continue
                evals = np.linalg.eigvalsh(H)
                score = _score_isotropy_from_eigs(evals)

                # Keep only if it can improve the current top-K.
                if len(best) >= int(args.top_k) and score >= worst_score:
                    prog.tick(f"scanned={scanned}/{total} best_score={best[0]['isotropy_score_log_ratio']:.4g}")
                    continue

                rec = {
                    "weights": {"u": float(u), "v": float(v), "w": float(w)},
                    "theta": {"theta_e": float(theta[0]), "theta_neg": float(theta[1]), "theta_2": float(theta[2])},
                    "pressure_P": float(P0),
                    "pressure_grad": {"theta_e": float(g[0]), "theta_neg": float(g[1]), "theta_2": float(g[2])},
                    "pressure_hessian_Sigma": H.tolist(),
                    "sigma_eigenvalues": [float(x) for x in evals.tolist()],
                    "isotropy_score_log_ratio": float(score),
                    "isotropy_ratio_max_over_min": float(float(np.max(evals)) / float(np.min(evals))),
                }
                maybe_add(rec)
                prog.tick(f"scanned={scanned}/{total} best_score={best[0]['isotropy_score_log_ratio']:.4g}")

    payload: Dict[str, object] = {
        "scan": {
            "u": {"min": float(args.u_min), "max": float(args.u_max), "steps": int(args.u_steps)},
            "v": {"min": float(args.v_min), "max": float(args.v_max), "steps": int(args.v_steps)},
            "w": {"min": float(args.w_min), "max": float(args.w_max), "steps": int(args.w_steps)},
            "h_theta": float(args.h),
            "total_points": total,
            "scanned": scanned,
            "skipped_nonspd": skipped_nonspd,
            "criterion": "minimize score = log(max_eig(Sigma)/min_eig(Sigma)) at theta=log(u,v,w)",
            "sp6_note": "For C=diag(Sigma,Sigma), Williamson symplectic eigenvalues equal eigs(Sigma).",
        },
        "best": best,
    }
    jout = Path(str(args.json_out))
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[sp6-isotropy-scan] wrote {jout}", flush=True)

    tex_out = Path(str(args.tex_out))
    _tex_table(tex_out, best)
    print(f"[sp6-isotropy-scan] wrote {tex_out}", flush=True)

    if best:
        r0 = best[0]
        print(
            "[sp6-isotropy-scan] best "
            f"u={r0['weights']['u']:.6g} v={r0['weights']['v']:.6g} w={r0['weights']['w']:.6g} "
            f"score={r0['isotropy_score_log_ratio']:.6g} eigs={r0['sigma_eigenvalues']}",
            flush=True,
        )
    print("[sp6-isotropy-scan] done", flush=True)


if __name__ == "__main__":
    main()

