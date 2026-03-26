#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute weighted pressure and rate function for sync-kernel SFT.

Outputs:
- artifacts/export/sync_kernel_weighted_pressure.json (default)
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Dict, List, Tuple

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


def phi_output_bit(edge: Edge) -> float:
    return float(edge.e)


def phi_neg_state(edge: Edge) -> float:
    return 1.0 if "-" in edge.dst else 0.0


def phi_neg_or_output(edge: Edge) -> float:
    return 1.0 if ("-" in edge.dst or edge.e == 1) else 0.0


def pick_phi(name: str) -> Callable[[Edge], float]:
    if name == "output_bit":
        return phi_output_bit
    if name == "neg_state":
        return phi_neg_state
    if name == "neg_or_output":
        return phi_neg_or_output
    raise ValueError(f"unknown phi: {name}")


def weighted_matrix(theta: float, phi: Callable[[Edge], float], edges: List[Edge]) -> np.ndarray:
    n = len(STATES)
    idx = {s: i for i, s in enumerate(STATES)}
    B = np.zeros((n, n), dtype=float)
    for edge in edges:
        i = idx[edge.src]
        j = idx[edge.dst]
        B[i, j] += math.exp(theta * phi(edge))
    return B


def spectral_radius(B: np.ndarray) -> float:
    vals = np.linalg.eigvals(B)
    return float(np.max(np.abs(vals)))


def pressure(theta: float, phi: Callable[[Edge], float], edges: List[Edge]) -> float:
    B = weighted_matrix(theta, phi, edges)
    lam = spectral_radius(B)
    return math.log(lam)


def central_diff(f: Callable[[float], float], h: float) -> float:
    return (f(h) - f(-h)) / (2.0 * h)


def second_diff(f: Callable[[float], float], h: float) -> float:
    return (f(h) - 2.0 * f(0.0) + f(-h)) / (h * h)


def rate_function(alpha_grid: List[float], theta_grid: List[float], P_vals: List[float]) -> List[float]:
    P0 = P_vals[len(theta_grid) // 2]
    out = []
    for a in alpha_grid:
        best = -1e100
        for th, Pth in zip(theta_grid, P_vals):
            val = th * a - (Pth - P0)
            if val > best:
                best = val
        out.append(best)
    return out


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Weighted pressure for sync-kernel SFT")
    parser.add_argument(
        "--phi",
        type=str,
        default="output_bit",
        choices=["output_bit", "neg_state", "neg_or_output"],
        help="Edge observable",
    )
    parser.add_argument("--theta-max", type=float, default=2.0, help="Theta grid max")
    parser.add_argument("--theta-step", type=float, default=0.1, help="Theta grid step")
    parser.add_argument("--alpha-step", type=float, default=0.02, help="Alpha grid step")
    parser.add_argument("--diff-step", type=float, default=1e-4, help="Step for derivatives")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output")
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/sync_kernel_weighted_pressure.json)",
    )
    args = parser.parse_args()

    prog = Progress(label="sync-kernel-weighted", every_seconds=20.0)
    edges = build_edges()
    phi = pick_phi(args.phi)

    theta_grid = []
    t = -args.theta_max
    while t <= args.theta_max + 1e-12:
        theta_grid.append(round(t, 12))
        t += args.theta_step

    alpha_grid = []
    a = 0.0
    while a <= 1.0 + 1e-12:
        alpha_grid.append(round(a, 12))
        a += args.alpha_step

    P_vals = []
    for th in theta_grid:
        P_vals.append(pressure(th, phi, edges))
        prog.tick(f"P(theta) grid size={len(P_vals)}/{len(theta_grid)}")

    P0 = pressure(0.0, phi, edges)
    Pp = central_diff(lambda x: pressure(x, phi, edges), args.diff_step)
    Ppp = second_diff(lambda x: pressure(x, phi, edges), args.diff_step)

    I_vals = rate_function(alpha_grid, theta_grid, P_vals)

    payload: Dict[str, object] = {
        "phi": args.phi,
        "states": STATES,
        "theta_grid": theta_grid,
        "pressure_P": P_vals,
        "pressure_P0": P0,
        "pressure_P1": Pp,
        "pressure_P2": Ppp,
        "alpha_grid": alpha_grid,
        "rate_I": I_vals,
    }

    if not args.no_output:
        out_path = Path(args.output) if args.output else export_dir() / "sync_kernel_weighted_pressure.json"
        write_json(out_path, payload)
        print(f"[sync-kernel-weighted] wrote {out_path}", flush=True)

    print(f"[sync-kernel-weighted] phi={args.phi}", flush=True)
    print(f"[sync-kernel-weighted] P(0)={P0:.12g}", flush=True)
    print(f"[sync-kernel-weighted] P'(0)≈{Pp:.12g}", flush=True)
    print(f"[sync-kernel-weighted] P''(0)≈{Ppp:.12g}", flush=True)
    print("[sync-kernel-weighted] done", flush=True)


if __name__ == "__main__":
    main()
