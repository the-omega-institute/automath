#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute 3D weighted pressure and primitive spectrum for sync-kernel SFT.

Outputs:
- artifacts/export/sync_kernel_weighted_pressure_3d.json (default)
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

import numpy as np

from common_paths import export_dir
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
    n = len(STATES)
    idx = {s: i for i, s in enumerate(STATES)}
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


def central_diff(f, h: float) -> float:
    return (f(h) - f(-h)) / (2.0 * h)


def second_diff(f, h: float) -> float:
    return (f(h) - 2.0 * f(0.0) + f(-h)) / (h * h)


def mixed_diff(f, h: float) -> float:
    return (f(h, h) - f(h, -h) - f(-h, h) + f(-h, -h)) / (4.0 * h * h)


def traces_and_primitives(B: np.ndarray, max_n: int, prog: Progress) -> Dict[str, List[float]]:
    if max_n <= 0:
        return {"a_n": [], "p_n": []}
    M = B.copy()
    traces: List[float] = []
    for k in range(1, max_n + 1):
        if k > 1:
            M = M @ B
        traces.append(float(np.trace(M)))
        prog.tick(f"trace n={k}/{max_n}")

    def mobius(x: int) -> int:
        if x == 1:
            return 1
        mu = 1
        p = 2
        nn = x
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

    pvals: List[float] = []
    for k in range(1, max_n + 1):
        s = 0.0
        for d in range(1, k + 1):
            if k % d == 0:
                s += mobius(d) * traces[k // d - 1]
        pvals.append(s / float(k))
    return {"a_n": traces, "p_n": pvals}


def delta_polynomial() -> str:
    return (
        "1-(uw+1)z-u(v^2w+vw+v+2)z^2"
        "+uv(uw+1)(vw+w+1)z^3"
        "-u(u^2v^2w^3-3uv^2w+uv(w^2+w-2)+u(w^2-w)+v^2w)z^4"
        "+uvw(u^3vw^3-2u^2vw-u^2w^3-uv(w+1)-u+v)z^5"
        "+u^2v^2w(2w-1)(u^2w+u+1)z^6"
    )


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="3D weighted pressure for sync-kernel SFT")
    parser.add_argument("--theta-e", type=float, default=0.0, help="Output-bit theta")
    parser.add_argument("--theta-neg", type=float, default=0.0, help="Neg-state theta")
    parser.add_argument("--theta-2", type=float, default=0.0, help="Input d=2 theta")
    parser.add_argument("--max-n", type=int, default=10, help="Max n for weighted traces")
    parser.add_argument("--diff-step", type=float, default=1e-4, help="Step for derivatives")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output")
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/sync_kernel_weighted_pressure_3d.json)",
    )
    args = parser.parse_args()

    prog = Progress(label="sync-kernel-weighted-3d", every_seconds=20.0)
    edges = build_edges()

    P0 = pressure(0.0, 0.0, 0.0, edges)
    h = args.diff_step

    P_e = central_diff(lambda x: pressure(x, 0.0, 0.0, edges), h)
    P_ee = second_diff(lambda x: pressure(x, 0.0, 0.0, edges), h)
    P_n = central_diff(lambda x: pressure(0.0, x, 0.0, edges), h)
    P_nn = second_diff(lambda x: pressure(0.0, x, 0.0, edges), h)
    P_2 = central_diff(lambda x: pressure(0.0, 0.0, x, edges), h)
    P_22 = second_diff(lambda x: pressure(0.0, 0.0, x, edges), h)

    P_en = mixed_diff(lambda a, b: pressure(a, b, 0.0, edges), h)
    P_e2 = mixed_diff(lambda a, b: pressure(a, 0.0, b, edges), h)
    P_n2 = mixed_diff(lambda a, b: pressure(0.0, a, b, edges), h)

    B_theta = weighted_matrix(args.theta_e, args.theta_neg, args.theta_2, edges)
    traces = traces_and_primitives(B_theta, args.max_n, prog)

    payload: Dict[str, object] = {
        "phi_e": "output_bit",
        "phi_neg": "neg_state",
        "phi_2": "input_is_2",
        "delta_polynomial": delta_polynomial(),
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
        "theta": {"theta_e": args.theta_e, "theta_neg": args.theta_neg, "theta_2": args.theta_2},
        "traces_a_n": traces["a_n"],
        "primitive_p_n": traces["p_n"],
    }

    if not args.no_output:
        out_path = (
            Path(args.output)
            if args.output
            else export_dir() / "sync_kernel_weighted_pressure_3d.json"
        )
        write_json(out_path, payload)
        print(f"[sync-kernel-weighted-3d] wrote {out_path}", flush=True)

    print(f"[sync-kernel-weighted-3d] P(0,0,0)={P0:.12g}", flush=True)
    print(
        f"[sync-kernel-weighted-3d] P_e={P_e:.12g} P_n={P_n:.12g} P_2={P_2:.12g}",
        flush=True,
    )
    print(
        f"[sync-kernel-weighted-3d] P_ee={P_ee:.12g} P_nn={P_nn:.12g} P_22={P_22:.12g}",
        flush=True,
    )
    print(
        f"[sync-kernel-weighted-3d] P_en={P_en:.12g} P_e2={P_e2:.12g} P_n2={P_n2:.12g}",
        flush=True,
    )
    print("[sync-kernel-weighted-3d] done", flush=True)


if __name__ == "__main__":
    main()
