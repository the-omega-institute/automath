#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Minimal, self-contained closed loop for the ((3,3,p)) near-1 pole on the N2 mod p axis.

Goal:
  - Compute kappa_infty from the Poisson equation for the collision cocycle xi=1_{d=2}.
  - Compute rho_{3,3,p} by explicit character scan on the real-input 40-state kernel.
  - Fit the O(theta^4) correction and compare extrapolated predictions at p>=17.

This file intentionally DOES NOT import any of the existing paper scripts; it reproduces
the needed kernel construction and all computations from scratch (numpy-only).

Repository convention note: script messages are English-only.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np


def _phi() -> float:
    return (1.0 + 5.0**0.5) / 2.0


def _lam() -> float:
    p = _phi()
    return p * p


@dataclass(frozen=True)
class KernelEdge:
    src: str
    dst: str
    d: int  # x+y in {0,1,2}
    e: int  # output bit in {0,1}


KERNEL_STATES: List[str] = [
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


def build_kernel_edges() -> List[KernelEdge]:
    edges: List[KernelEdge] = []
    for d in (0, 1, 2):
        edges.append(KernelEdge("000", f"00{d}", d, 0))
    for d in (0, 1, 2):
        edges.append(KernelEdge("100", f"00{d}", d, 1))
    edges += [
        KernelEdge("001", "010", 0, 0),
        KernelEdge("001", "100", 1, 0),
        KernelEdge("001", "101", 2, 0),
        KernelEdge("002", "11-1", 0, 0),
        KernelEdge("002", "000", 1, 1),
        KernelEdge("002", "001", 2, 1),
        KernelEdge("010", "100", 0, 0),
        KernelEdge("010", "101", 1, 0),
        KernelEdge("010", "0-12", 2, 1),
        KernelEdge("101", "010", 0, 1),
        KernelEdge("101", "100", 1, 1),
        KernelEdge("101", "101", 2, 1),
        KernelEdge("0-12", "01-1", 0, 0),
        KernelEdge("0-12", "010", 1, 0),
        KernelEdge("0-12", "100", 2, 0),
        KernelEdge("1-12", "01-1", 0, 1),
        KernelEdge("1-12", "010", 1, 1),
        KernelEdge("1-12", "100", 2, 1),
        KernelEdge("01-1", "001", 0, 0),
        KernelEdge("01-1", "002", 1, 0),
        KernelEdge("01-1", "1-12", 2, 0),
        KernelEdge("11-1", "001", 0, 1),
        KernelEdge("11-1", "002", 1, 1),
        KernelEdge("11-1", "1-12", 2, 1),
    ]
    return edges


def build_kernel_map(edges: Sequence[KernelEdge]) -> Dict[Tuple[str, int], Tuple[str, int]]:
    return {(e.src, e.d): (e.dst, e.e) for e in edges}


def build_real_input_states() -> List[Tuple[str, int, int]]:
    # (kernel_state, prev_x, prev_y), where prev_* is in {0,1}.
    out: List[Tuple[str, int, int]] = []
    for s in KERNEL_STATES:
        for px in (0, 1):
            for py in (0, 1):
                out.append((s, px, py))
    return out


def build_weighted_matrix(
    *,
    q: complex,
    r: complex,
    u: complex,
    states: Sequence[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> np.ndarray:
    """40x40 complex matrix for a single character (q,r,u).

    Definitions (paper):
      chi := e - 1_{d=2}
      nu  := 1_{s' in Q_-}  (entering negative-carry zone)
      w3  := 1_{d=2}        (third axis is N2 mod p)
      weight = q^chi * r^nu * u^w3
    """
    idx = {st: i for i, st in enumerate(states)}
    n = len(states)
    M = np.zeros((n, n), dtype=np.complex128)
    for s, px, py in states:
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, e = kernel_map[(s, d)]
                chi = int(e) - (1 if d == 2 else 0)
                nu = 1 if "-" in dst_state else 0
                w3 = 1 if d == 2 else 0
                i = idx[(s, px, py)]
                j = idx[(dst_state, x, y)]
                M[i, j] += (q**chi) * (r**nu) * (u**w3)
    return M


def spectral_radius(M: np.ndarray) -> float:
    vals = np.linalg.eigvals(M)
    return float(np.max(np.abs(vals)))


@dataclass(frozen=True)
class ScanRow:
    p: int
    rho: float
    rho_ratio: float
    gap: float
    g: float
    kappa_p: float
    argmax: List[Tuple[int, int, int]]


def scan_rho_33p(
    *,
    p: int,
    states: Sequence[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
    tol: float = 1e-12,
) -> ScanRow:
    """Compute rho_{3,3,p} = max_{(j1,j2,j3)!=(0,0,0)} rho(M_{j1,j2,j3})."""
    m1, m2, m3 = 3, 3, int(p)
    lam = _lam()

    omega3 = np.exp(2j * math.pi / 3.0)
    omega_p = np.exp(2j * math.pi / float(m3))

    qs = [omega3**j for j in range(m1)]
    rs = [omega3**j for j in range(m2)]
    us = [omega_p**j for j in range(m3)]

    rho_max = -1.0
    argmax: List[Tuple[int, int, int]] = []

    for j1 in range(m1):
        q = qs[j1]
        for j2 in range(m2):
            r = rs[j2]
            for j3 in range(m3):
                if j1 == 0 and j2 == 0 and j3 == 0:
                    continue
                u = us[j3]
                M = build_weighted_matrix(q=q, r=r, u=u, states=states, kernel_map=kernel_map)
                rho = spectral_radius(M)
                if rho > rho_max + tol:
                    rho_max = rho
                    argmax = [(j1, j2, j3)]
                elif abs(rho - rho_max) <= tol:
                    argmax.append((j1, j2, j3))

    rho_ratio = rho_max / lam
    gap = 1.0 - rho_ratio
    g = gap * float(p * p)
    theta = (2.0 * math.pi) / float(p)
    kappa_p = gap / (theta * theta)
    return ScanRow(
        p=int(p),
        rho=float(rho_max),
        rho_ratio=float(rho_ratio),
        gap=float(gap),
        g=float(g),
        kappa_p=float(kappa_p),
        argmax=sorted(argmax),
    )


@dataclass(frozen=True)
class Edge:
    src: int
    dst: int
    xi: int  # collision cocycle 1_{d=2}


def build_edges_with_xi(
    *,
    states: Sequence[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> List[Edge]:
    idx = {st: i for i, st in enumerate(states)}
    out: List[Edge] = []
    for s, px, py in states:
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, _e = kernel_map[(s, d)]
                out.append(
                    Edge(
                        src=idx[(s, px, py)],
                        dst=idx[(dst_state, x, y)],
                        xi=(1 if d == 2 else 0),
                    )
                )
    return out


def adjacency_from_edges(n: int, edges: Sequence[Edge]) -> np.ndarray:
    A = np.zeros((n, n), dtype=float)
    for e in edges:
        A[e.src, e.dst] += 1.0
    return A


def pf_eigenvectors(A: np.ndarray) -> Tuple[float, np.ndarray, np.ndarray]:
    """Return (lambda_pf, left, right) with normalization left^T right = 1."""
    vals, vecs = np.linalg.eig(A)
    i0 = int(np.argmax(np.real(vals)))
    lam = float(np.real(vals[i0]))
    r = np.real(vecs[:, i0]).astype(float)

    valsL, vecsL = np.linalg.eig(A.T)
    j0 = int(np.argmax(np.real(valsL)))
    l = np.real(vecsL[:, j0]).astype(float)

    if float(np.sum(r)) < 0.0:
        r = -r
    if float(np.sum(l)) < 0.0:
        l = -l

    lr = float(l @ r)
    if lr == 0.0:
        raise RuntimeError("PF normalization failed: left^T right = 0")
    l = l / lr
    return lam, l, r


def parry_chain(A: np.ndarray, lam: float, l: np.ndarray, r: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
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
    pi = (l * r).astype(float)
    s = float(np.sum(pi))
    if s <= 0.0:
        raise RuntimeError("Invalid stationary mass")
    pi = pi / s
    return P, pi


def solve_poisson(P: np.ndarray, pi: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Solve (I-P)f=b with gauge constraint pi^T f = 0."""
    n = P.shape[0]
    A = np.eye(n, dtype=float) - P
    M = np.zeros((n + 1, n + 1), dtype=float)
    M[:n, :n] = A
    M[:n, n] = pi
    M[n, :n] = pi
    rhs = np.zeros((n + 1,), dtype=float)
    rhs[:n] = b
    sol = np.linalg.solve(M, rhs)
    f = sol[:n]
    f = f - float(pi @ f)
    return f


def kappa_infty_via_poisson(
    *,
    states: Sequence[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> Dict[str, float]:
    """Return sigma^2 and kappa_inf for xi=1_{d=2} under the Parry measure."""
    edges = build_edges_with_xi(states=states, kernel_map=kernel_map)
    n = len(states)
    A = adjacency_from_edges(n, edges)
    lam_pf, l, r = pf_eigenvectors(A)
    P, pi = parry_chain(A, lam_pf, l, r)

    # Edge weight (each parallel edge separately): m(e)=l_src*r_dst/lam, with l^T r = 1.
    def w_edge(src: int, dst: int) -> float:
        return float(l[src] * r[dst] / lam_pf)

    mu = 0.0
    for e in edges:
        mu += w_edge(e.src, e.dst) * float(e.xi)
    mu = float(mu)

    # b_i = E[xi - mu | state i] under the Parry chain.
    b = np.zeros((n,), dtype=float)
    for e in edges:
        b[e.src] += (r[e.dst] / (lam_pf * r[e.src])) * (float(e.xi) - mu)

    f = solve_poisson(P, pi, b)
    sigma2 = 0.0
    for e in edges:
        d = float(e.xi) - mu + float(f[e.dst] - f[e.src])
        sigma2 += w_edge(e.src, e.dst) * d * d
    sigma2 = float(sigma2)

    return {
        "n_states": float(n),
        "n_edges": float(len(edges)),
        "lambda_pf": float(lam_pf),
        "lambda_target": float(_lam()),
        "lambda_abs_err": float(abs(lam_pf - _lam())),
        "mu_edge_mean": float(mu),
        "sigma2": float(sigma2),
        "kappa_infty": float(0.5 * sigma2),
        "g_infty": float(4.0 * (math.pi**2) * (0.5 * sigma2)),
    }


def _parse_int_list_csv(s: str) -> List[int]:
    out: List[int] = []
    for chunk in (x.strip() for x in s.split(",")):
        if not chunk:
            continue
        out.append(int(chunk))
    return out


def _theta(p: int) -> float:
    return (2.0 * math.pi) / float(p)


def _re_s_from_ratio(ratio: float, lam: float) -> float:
    # Re(s)=log(rho)/log(lam) = 1 + log(ratio)/log(lam), where ratio=rho/lam.
    if ratio <= 0.0:
        return float("nan")
    return 1.0 + (math.log(ratio) / math.log(lam))


def main() -> None:
    parser = argparse.ArgumentParser(description="Self-contained ((3,3,p)) diffusion loop (Poisson + scan + extrapolation).")
    parser.add_argument(
        "--p-list",
        type=str,
        default="5,7,11,13,17,19,23,29,31",
        help="Comma-separated list of odd moduli p to scan.",
    )
    parser.add_argument(
        "--fit-pair",
        type=str,
        default="7,13",
        help="Two p values (comma-separated) used to fit the O(theta^4) correction.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default="",
        help="Optional JSON output path (default: paper-local artifacts/export/mini_arity_335_diffusion_loop.json).",
    )
    args = parser.parse_args()

    # Build kernel.
    edges0 = build_kernel_edges()
    kernel_map = build_kernel_map(edges0)
    states = build_real_input_states()

    # 1) Poisson: kappa_infty (variance density / 2).
    kappa_payload = kappa_infty_via_poisson(states=states, kernel_map=kernel_map)
    kappa_inf = float(kappa_payload["kappa_infty"])
    lam = float(_lam())

    # 2) Scan rho_{3,3,p} for requested p.
    p_list = _parse_int_list_csv(str(args.p_list))
    if not p_list:
        raise SystemExit("[mini-arity-335] empty p-list")
    rows: List[ScanRow] = []
    for p in p_list:
        if p < 2:
            raise SystemExit(f"[mini-arity-335] invalid p: {p}")
        rows.append(scan_rho_33p(p=p, states=states, kernel_map=kernel_map))

    # Build quick index by p.
    by_p: Dict[int, ScanRow] = {r.p: r for r in rows}

    # 3) Fit O(theta^4) correction using two moduli (p1,p2) from actual kappa_p.
    fit_pair = _parse_int_list_csv(str(args.fit_pair))
    if len(fit_pair) != 2:
        raise SystemExit("[mini-arity-335] fit-pair must contain exactly two integers, e.g. 7,13")
    p1, p2 = int(fit_pair[0]), int(fit_pair[1])
    if p1 not in by_p or p2 not in by_p:
        raise SystemExit("[mini-arity-335] fit-pair p values must be included in p-list scans")
    th1, th2 = _theta(p1), _theta(p2)
    kap1, kap2 = by_p[p1].kappa_p, by_p[p2].kappa_p
    # Model: kappa_p = kappa_inf + c4 * theta^2 + O(theta^4).
    c4_fit = float((kap1 - kap2) / (th1 * th1 - th2 * th2))
    kappa_inf_fit = float(kap1 - c4_fit * (th1 * th1))

    # 4) Optional: log-form coefficient beta in log ratio = -kappa_inf*theta^2 + beta*theta^4.
    # Use fit_pair average (two-point fit is also possible).
    def beta_from_row(rr: ScanRow) -> float:
        th = _theta(rr.p)
        return float((math.log(rr.rho_ratio) + kappa_inf * (th * th)) / (th**4))

    beta1 = beta_from_row(by_p[p1])
    beta2 = beta_from_row(by_p[p2])
    beta_avg = 0.5 * (beta1 + beta2)

    # 5) Produce comparison table.
    header = [
        "p",
        "rho/lam (actual)",
        "kappa_p",
        "g(p)",
        "rho/lam pred2",
        "rho/lam pred4(gap)",
        "rho/lam pred4(log)",
        "err4(gap)",
        "Re(s) actual",
    ]
    print("[mini-arity-335] Poisson kappa_infty =", f"{kappa_inf:.12f}")
    print("[mini-arity-335] Poisson sigma^2     =", f"{2.0 * kappa_inf:.12f}")
    print("[mini-arity-335] g_infty=4pi^2*kappa  =", f"{(4.0 * math.pi**2 * kappa_inf):.12f}")
    print("[mini-arity-335] fit-pair            =", f"({p1},{p2})")
    print("[mini-arity-335] c4_fit (gap model)  =", f"{c4_fit:.12f}")
    print("[mini-arity-335] kappa_inf_fit       =", f"{kappa_inf_fit:.12f}", "(from two-point Richardson)")
    print("[mini-arity-335] beta_avg (log model)=", f"{beta_avg:.12f}")
    print()
    print(" | ".join(header))
    for rr in rows:
        th = _theta(rr.p)
        pred2 = 1.0 - kappa_inf * (th * th)
        pred4_gap = 1.0 - (kappa_inf * (th * th) + c4_fit * (th**4))
        pred4_log = math.exp(-(kappa_inf * (th * th)) + beta_avg * (th**4))
        err4_gap = pred4_gap - rr.rho_ratio
        re_s = _re_s_from_ratio(rr.rho_ratio, lam)
        print(
            f"{rr.p:>3d} | "
            f"{rr.rho_ratio:.12f} | "
            f"{rr.kappa_p:.6f} | "
            f"{rr.g:.6f} | "
            f"{pred2:.12f} | "
            f"{pred4_gap:.12f} | "
            f"{pred4_log:.12f} | "
            f"{err4_gap:+.3e} | "
            f"{re_s:.12f}"
        )

    # 6) JSON artifact (optional but useful for audit).
    out_path = Path(str(args.json_out)) if str(args.json_out).strip() else None
    if out_path is None:
        # paper_root/scripts/../artifacts/export/...
        paper_root = Path(__file__).resolve().parents[1]
        out_path = paper_root / "artifacts" / "export" / "mini_arity_335_diffusion_loop.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "kappa_poisson": kappa_payload,
        "scan": [asdict(r) for r in rows],
        "fit": {
            "fit_pair": [p1, p2],
            "c4_fit_gap_model": c4_fit,
            "kappa_infty_fit_from_pair": kappa_inf_fit,
            "beta_from_pair_avg_log_model": beta_avg,
            "beta_pair": [beta1, beta2],
        },
        "notes": {
            "model_gap": "1 - rho/lam = kappa_infty*theta^2 + c4*theta^4 + O(theta^6)",
            "model_log": "log(rho/lam) = -kappa_infty*theta^2 + beta*theta^4 + O(theta^6)",
            "theta": "2*pi/p",
            "lambda": "phi^2",
        },
    }
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print()
    print("[mini-arity-335] wrote", str(out_path))


if __name__ == "__main__":
    main()

