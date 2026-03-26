#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute real-input 40-state sync-kernel spectrum and 3D pressure.

Outputs:
- artifacts/export/sync_kernel_real_input_40.json (default)
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir
from common_phi_fold import Progress


@dataclass(frozen=True)
class KernelEdge:
    src: str
    dst: str
    d: int
    e: int


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


def build_kernel_map(edges: List[KernelEdge]) -> Dict[Tuple[str, int], Tuple[str, int]]:
    return {(edge.src, edge.d): (edge.dst, edge.e) for edge in edges}


def build_real_input_states() -> List[Tuple[str, int, int]]:
    states: List[Tuple[str, int, int]] = []
    for s in KERNEL_STATES:
        for px in (0, 1):
            for py in (0, 1):
                states.append((s, px, py))
    return states


def build_real_input_matrix_int(
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> List[List[int]]:
    idx = {state: i for i, state in enumerate(states)}
    n = len(states)
    M = [[0] * n for _ in range(n)]
    for s, px, py in states:
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, _ = kernel_map[(s, d)]
                nxt = (dst_state, x, y)
                M[idx[(s, px, py)]][idx[nxt]] += 1
    return M


def build_weighted_matrix(
    theta_e: float,
    theta_neg: float,
    theta_2: float,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> np.ndarray:
    idx = {state: i for i, state in enumerate(states)}
    n = len(states)
    u = math.exp(theta_e)
    v = math.exp(theta_neg)
    w = math.exp(theta_2)
    B = np.zeros((n, n), dtype=float)
    for s, px, py in states:
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, e = kernel_map[(s, d)]
                neg = 1 if "-" in dst_state else 0
                two = 1 if d == 2 else 0
                weight = (u**e) * (v**neg) * (w**two)
                B[idx[(s, px, py)]][idx[(dst_state, x, y)]] += weight
    return B


def spectral_radius(B: np.ndarray) -> float:
    vals = np.linalg.eigvals(B)
    return float(np.max(np.abs(vals)))


def pressure(
    theta_e: float,
    theta_neg: float,
    theta_2: float,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> float:
    B = build_weighted_matrix(theta_e, theta_neg, theta_2, states, kernel_map)
    lam = spectral_radius(B)
    return math.log(lam)


def mat_mul_int(A: List[List[int]], B: List[List[int]]) -> List[List[int]]:
    n = len(A)
    res = [[0] * n for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        for k in range(n):
            if Ai[k] == 0:
                continue
            aik = Ai[k]
            Bk = B[k]
            for j in range(n):
                if Bk[j]:
                    res[i][j] += aik * Bk[j]
    return res


def mat_trace_int(A: List[List[int]]) -> int:
    return sum(A[i][i] for i in range(len(A)))


def mobius(n: int) -> int:
    if n == 1:
        return 1
    mu = 1
    p = 2
    nn = n
    while p * p <= nn:
        if nn % p == 0:
            nn //= p
            if nn % p == 0:
                return 0
            mu = -mu
        p += 1
    if nn > 1:
        mu = -mu
    return mu


def traces_and_primitives_int(
    M: List[List[int]],
    max_n: int,
    prog: Progress,
) -> Dict[str, List[int]]:
    if max_n <= 0:
        return {"a_n": [], "p_n": []}
    A = [row[:] for row in M]
    traces: List[int] = []
    for k in range(1, max_n + 1):
        if k > 1:
            A = mat_mul_int(A, M)
        traces.append(mat_trace_int(A))
        prog.tick(f"trace n={k}/{max_n}")

    pvals: List[int] = []
    for n in range(1, max_n + 1):
        s = 0
        for d in range(1, n + 1):
            if n % d == 0:
                s += mobius(d) * traces[n // d - 1]
        if s % n != 0:
            raise ValueError(f"p_n not integer at n={n}")
        pvals.append(s // n)
    return {"a_n": traces, "p_n": pvals}


def mertens_constant(
    pvals: List[int],
    lam_dec: Decimal,
    gamma_dec: Decimal,
) -> Tuple[Decimal, Decimal]:
    sum_diff = Decimal(0)
    for n, pn in enumerate(pvals, start=1):
        pn_dec = Decimal(pn)
        term = pn_dec / (lam_dec**n) - (Decimal(1) / Decimal(n))
        sum_diff += term
    return sum_diff, sum_diff + gamma_dec


def residue_constant(sqrt5: Decimal) -> Decimal:
    # C := lim_{z -> z_star} (1 - lambda z) zeta_M(z)
    # For det(I - zM) = (1-z)^2 (1+z)^3 (1-3z+z^2) (1+z-z^2),
    # where lambda = (3+sqrt5)/2, z_star = 1/lambda.
    return (Decimal(47) + Decimal(21) * sqrt5) / Decimal(100)


def det_real_input_40(z: Decimal) -> Decimal:
    one = Decimal(1)
    return (one - z) ** 2 * (one + z) ** 3 * (one - Decimal(3) * z + z * z) * (one + z - z * z)


def zeta_real_input_40(z: Decimal) -> Decimal:
    return Decimal(1) / det_real_input_40(z)


def log_mathfrak_M_from_zeta(
    z_star: Decimal,
    C: Decimal,
    m_max: int,
) -> Decimal:
    # log M = log C + sum_{m>=2} mu(m)/m * log zeta(z_star^m)
    s = Decimal(0)
    for m in range(2, m_max + 1):
        mu = mobius(m)
        if mu == 0:
            continue
        zm = z_star**m
        s += (Decimal(mu) / Decimal(m)) * zeta_real_input_40(zm).ln()
    return C.ln() + s


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Real-input 40-state sync-kernel spectrum")
    parser.add_argument("--max-n", type=int, default=10, help="Max n for a_n/p_n outputs")
    parser.add_argument("--mertens-n", type=int, default=200, help="Max n for Mertens sum")
    parser.add_argument("--zeta-m-max", type=int, default=50, help="Max m for zeta-based log M series")
    parser.add_argument("--diff-step", type=float, default=1e-4, help="Step for derivatives")
    parser.add_argument("--precision", type=int, default=80, help="Decimal precision")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output")
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/sync_kernel_real_input_40.json)",
    )
    args = parser.parse_args()

    prog = Progress(label="sync-kernel-real-input-40", every_seconds=20.0)
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()

    M_int = build_real_input_matrix_int(states, kernel_map)
    M_float = np.array(M_int, dtype=float)
    lambda_pf = spectral_radius(M_float)

    phi = (1.0 + 5.0**0.5) / 2.0
    lambda_phi2 = phi * phi
    entropy_log = math.log(lambda_phi2)

    max_n = max(args.max_n, args.mertens_n)
    traces = traces_and_primitives_int(M_int, max_n, prog)
    a_n = traces["a_n"][: args.max_n]
    p_n = traces["p_n"][: args.max_n]

    getcontext().prec = args.precision
    sqrt5 = Decimal(5).sqrt()
    lam_dec = (Decimal(3) + sqrt5) / Decimal(2)
    gamma_dec = Decimal("0.577215664901532860606512090082402431")

    sum_diff, mertens = mertens_constant(traces["p_n"][: args.mertens_n], lam_dec, gamma_dec)
    mathfrak_M = sum_diff.exp()
    C = residue_constant(sqrt5)
    z_star = (Decimal(1) / lam_dec)
    log_mathfrak_M_zeta = log_mathfrak_M_from_zeta(z_star=z_star, C=C, m_max=args.zeta_m_max)

    h = args.diff_step
    P0 = pressure(0.0, 0.0, 0.0, states, kernel_map)
    P_e = (pressure(h, 0.0, 0.0, states, kernel_map) - pressure(-h, 0.0, 0.0, states, kernel_map)) / (
        2.0 * h
    )
    P_n = (pressure(0.0, h, 0.0, states, kernel_map) - pressure(0.0, -h, 0.0, states, kernel_map)) / (
        2.0 * h
    )
    P_2 = (pressure(0.0, 0.0, h, states, kernel_map) - pressure(0.0, 0.0, -h, states, kernel_map)) / (
        2.0 * h
    )
    P_ee = (
        pressure(h, 0.0, 0.0, states, kernel_map)
        - 2.0 * P0
        + pressure(-h, 0.0, 0.0, states, kernel_map)
    ) / (h * h)
    P_nn = (
        pressure(0.0, h, 0.0, states, kernel_map)
        - 2.0 * P0
        + pressure(0.0, -h, 0.0, states, kernel_map)
    ) / (h * h)
    P_22 = (
        pressure(0.0, 0.0, h, states, kernel_map)
        - 2.0 * P0
        + pressure(0.0, 0.0, -h, states, kernel_map)
    ) / (h * h)
    P_en = (
        pressure(h, h, 0.0, states, kernel_map)
        - pressure(h, -h, 0.0, states, kernel_map)
        - pressure(-h, h, 0.0, states, kernel_map)
        + pressure(-h, -h, 0.0, states, kernel_map)
    ) / (4.0 * h * h)
    P_e2 = (
        pressure(h, 0.0, h, states, kernel_map)
        - pressure(h, 0.0, -h, states, kernel_map)
        - pressure(-h, 0.0, h, states, kernel_map)
        + pressure(-h, 0.0, -h, states, kernel_map)
    ) / (4.0 * h * h)
    P_n2 = (
        pressure(0.0, h, h, states, kernel_map)
        - pressure(0.0, h, -h, states, kernel_map)
        - pressure(0.0, -h, h, states, kernel_map)
        + pressure(0.0, -h, -h, states, kernel_map)
    ) / (4.0 * h * h)

    hess = np.array([[P_ee, P_en, P_e2], [P_en, P_nn, P_n2], [P_e2, P_n2, P_22]], dtype=float)
    hess_inv = np.linalg.inv(hess)

    payload: Dict[str, object] = {
        "det_factorization": "(1-z)^2(1+z)^3(1-3z+z^2)(1+z-z^2)",
        "lambda_pf": lambda_pf,
        "lambda_phi2": lambda_phi2,
        "entropy_log": entropy_log,
        "a_n": a_n,
        "p_n": p_n,
        "log_mathfrak_M": float(sum_diff),
        "log_mathfrak_M_from_zeta": float(log_mathfrak_M_zeta),
        "zeta_m_max": args.zeta_m_max,
        "mathfrak_M": float(mathfrak_M),
        "zeta_residue_C": float(C),
        "zeta_residue_C_exact": "(47+21*sqrt5)/100",
        "mertens_constant": float(mertens),
        "mertens_n": args.mertens_n,
        "pressure_P0": P0,
        "pressure_grad": {"theta_e": P_e, "theta_neg": P_n, "theta_2": P_2},
        "pressure_hessian": {
            "ee": P_ee,
            "nn": P_nn,
            "22": P_22,
            "en": P_en,
            "e2": P_e2,
            "n2": P_n2,
        },
        "pressure_hessian_inv": {
            "11": float(hess_inv[0, 0]),
            "12": float(hess_inv[0, 1]),
            "13": float(hess_inv[0, 2]),
            "22": float(hess_inv[1, 1]),
            "23": float(hess_inv[1, 2]),
            "33": float(hess_inv[2, 2]),
        },
        "theta": {"theta_e": 0.0, "theta_neg": 0.0, "theta_2": 0.0},
    }

    if not args.no_output:
        out_path = Path(args.output) if args.output else export_dir() / "sync_kernel_real_input_40.json"
        write_json(out_path, payload)
        print(f"[sync-kernel-real-input-40] wrote {out_path}", flush=True)

    print(
        f"[sync-kernel-real-input-40] lambda_pf={lambda_pf:.12g} lambda_phi2={lambda_phi2:.12g}",
        flush=True,
    )
    print(
        f"[sync-kernel-real-input-40] P0={P0:.12g} P_e={P_e:.12g} P_n={P_n:.12g} P_2={P_2:.12g}",
        flush=True,
    )
    print(
        f"[sync-kernel-real-input-40] P_ee={P_ee:.12g} P_nn={P_nn:.12g} P_22={P_22:.12g}",
        flush=True,
    )
    print(
        f"[sync-kernel-real-input-40] P_en={P_en:.12g} P_e2={P_e2:.12g} P_n2={P_n2:.12g}",
        flush=True,
    )
    print(
        f"[sync-kernel-real-input-40] logM={float(sum_diff):.12g} M={float(mathfrak_M):.12g}",
        flush=True,
    )
    print(
        f"[sync-kernel-real-input-40] C={float(C):.12g} logM(zeta)={float(log_mathfrak_M_zeta):.12g} Mertens={float(mertens):.12g}",
        flush=True,
    )
    print("[sync-kernel-real-input-40] done", flush=True)


if __name__ == "__main__":
    main()
