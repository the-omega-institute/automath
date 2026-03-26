#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute 2D arity-charge/negative-carry primitive spectrum for real-input 40-state kernel.

Outputs:
- artifacts/export/sync_kernel_real_input_40_arity_2d.json (default)
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
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


Poly2D = Dict[Tuple[int, int], int]


def poly_add(a: Poly2D, b: Poly2D) -> Poly2D:
    out = dict(a)
    for exp, coeff in b.items():
        out[exp] = out.get(exp, 0) + coeff
        if out[exp] == 0:
            del out[exp]
    return out


def poly_mul(a: Poly2D, b: Poly2D) -> Poly2D:
    out: Poly2D = {}
    for (eq, er), ca in a.items():
        for (fq, fr), cb in b.items():
            exp = (eq + fq, er + fr)
            out[exp] = out.get(exp, 0) + ca * cb
    return out


def poly_scale_exponent(a: Poly2D, factor: int) -> Poly2D:
    return {(eq * factor, er * factor): coeff for (eq, er), coeff in a.items()}


def term_to_latex(coeff: int, exp_q: int, exp_r: int) -> str:
    parts: List[str] = []
    if exp_q != 0:
        if exp_q == 1:
            parts.append("q")
        else:
            parts.append(f"q^{{{exp_q}}}")
    if exp_r != 0:
        if exp_r == 1:
            parts.append("r")
        else:
            parts.append(f"r^{{{exp_r}}}")
    base = "".join(parts)
    if not base:
        return str(coeff)
    if coeff == 1:
        return base
    if coeff == -1:
        return f"-{base}"
    return f"{coeff}{base}"


def poly_to_latex(poly: Poly2D) -> str:
    if not poly:
        return "0"
    items = sorted(poly.items(), key=lambda kv: (kv[0][0], kv[0][1]), reverse=True)
    out = ""
    for (eq, er), coeff in items:
        if coeff == 0:
            continue
        term = term_to_latex(abs(coeff), eq, er)
        if out == "":
            out = term if coeff > 0 else f"-{term}"
        else:
            out += f" - {term}" if coeff < 0 else f" + {term}"
    return out


def parse_pair_values(text: str) -> List[Tuple[int, int]]:
    raw = [chunk.strip() for chunk in text.split(",")] if text else []
    pairs: List[Tuple[int, int]] = []
    for chunk in raw:
        if not chunk:
            continue
        if "x" not in chunk:
            raise SystemExit(f"[arity-2d] invalid pair (use axb): {chunk}")
        left, right = [part.strip() for part in chunk.split("x", 1)]
        try:
            m1 = int(left)
            m2 = int(right)
        except ValueError as exc:
            raise SystemExit(f"[arity-2d] invalid pair value: {chunk}") from exc
        if m1 < 2 or m2 < 2:
            raise SystemExit(f"[arity-2d] pair entries must be >=2, got {chunk}")
        pairs.append((m1, m2))
    if not pairs:
        pairs = [(2, 2), (3, 2), (5, 2), (3, 3), (5, 5)]
    # keep order but remove duplicates
    seen = set()
    out: List[Tuple[int, int]] = []
    for p in pairs:
        if p in seen:
            continue
        seen.add(p)
        out.append(p)
    return out


def build_weighted_matrix_poly(
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> List[List[Poly2D]]:
    idx = {state: i for i, state in enumerate(states)}
    n = len(states)
    M: List[List[Poly2D]] = [[{} for _ in range(n)] for _ in range(n)]
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
                i = idx[(s, px, py)]
                j = idx[(dst_state, x, y)]
                M[i][j] = poly_add(M[i][j], {(chi, nu): 1})
    return M


def mat_mul(A: List[List[Poly2D]], B: List[List[Poly2D]]) -> List[List[Poly2D]]:
    n = len(A)
    res: List[List[Poly2D]] = [[{} for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if not A[i][k]:
                continue
            for j in range(n):
                if not B[k][j]:
                    continue
                res[i][j] = poly_add(res[i][j], poly_mul(A[i][k], B[k][j]))
    return res


def mat_trace(A: List[List[Poly2D]]) -> Poly2D:
    poly: Poly2D = {}
    for i in range(len(A)):
        poly = poly_add(poly, A[i][i])
    return poly


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


def compute_c_and_P(
    max_n: int,
    prog: Progress,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> Tuple[List[Poly2D], List[Poly2D]]:
    M = build_weighted_matrix_poly(states, kernel_map)
    c: List[Poly2D] = [None] * (max_n + 1)  # type: ignore[assignment]
    A = M
    for n in range(1, max_n + 1):
        if n > 1:
            A = mat_mul(A, M)
        c[n] = mat_trace(A)
        prog.tick(f"trace-2d n={n}/{max_n}")

    P: List[Poly2D] = [None] * (max_n + 1)  # type: ignore[assignment]
    for n in range(1, max_n + 1):
        poly: Poly2D = {}
        for d in range(1, n + 1):
            if n % d != 0:
                continue
            mu = mobius(d)
            cd = poly_scale_exponent(c[n // d], d)
            if mu == 1:
                poly = poly_add(poly, cd)
            elif mu == -1:
                poly = poly_add(poly, {(eq, er): -coeff for (eq, er), coeff in cd.items()})
        for exp, coeff in list(poly.items()):
            if coeff % n != 0:
                raise ValueError(f"Non-integer P_n coefficient at n={n}, exp={exp}")
            poly[exp] = coeff // n
            if poly[exp] == 0:
                del poly[exp]
        P[n] = poly
    return c, P


def build_weighted_matrix_numeric(
    q: complex,
    r: complex,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> np.ndarray:
    idx = {state: i for i, state in enumerate(states)}
    n = len(states)
    M = np.zeros((n, n), dtype=complex)
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
                i = idx[(s, px, py)]
                j = idx[(dst_state, x, y)]
                M[i, j] += (q**chi) * (r**nu)
    return M


def traces_for_qr(
    q: complex,
    r: complex,
    max_n: int,
    prog: Progress,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
    label: str,
) -> List[complex]:
    M = build_weighted_matrix_numeric(q, r, states, kernel_map)
    A = M.copy()
    traces: List[complex] = []
    for n in range(1, max_n + 1):
        if n > 1:
            A = A @ M
        traces.append(np.trace(A))
        prog.tick(f"{label} trace n={n}/{max_n}")
    return traces


def pvals_from_traces(traces: List[complex]) -> List[complex]:
    max_n = len(traces)
    pvals: List[complex] = []
    for n in range(1, max_n + 1):
        s = 0.0 + 0.0j
        for d in range(1, n + 1):
            if n % d == 0:
                s += mobius(d) * traces[n // d - 1]
        pvals.append(s / float(n))
    return pvals


def spectral_radius(B: np.ndarray) -> float:
    vals = np.linalg.eigvals(B)
    return float(np.max(np.abs(vals)))


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="2D arity/negative-carry primitive spectrum")
    parser.add_argument("--max-n", type=int, default=8, help="Max n for P_n(q,r)")
    parser.add_argument("--mertens-n", type=int, default=200, help="Max n for constants")
    parser.add_argument(
        "--pair-values",
        type=str,
        default="2x2,3x2,5x2,3x3,5x5",
        help="Comma-separated m1xm2 pairs for Dirichlet–Mertens constants",
    )
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output")
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/sync_kernel_real_input_40_arity_2d.json)",
    )
    args = parser.parse_args()

    prog = Progress(label="sync-kernel-real-input-arity-2d", every_seconds=20.0)
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()

    c, P = compute_c_and_P(args.max_n, prog, states, kernel_map)
    P_latex = [poly_to_latex(P[n]) for n in range(1, args.max_n + 1)]
    # Audit: minimum q-exponent in each P_n(q,r) (evidence for nonnegativity conjecture).
    min_q_exp: List[int] = []
    for n in range(1, args.max_n + 1):
        exps = [eq for (eq, _er) in P[n].keys()]
        min_q_exp.append(int(min(exps)) if exps else 0)

    # Unweighted Mertens constant
    phi = (1.0 + 5.0**0.5) / 2.0
    lam = phi * phi
    gamma = 0.5772156649015329
    mertens_n = args.mertens_n

    traces_one = traces_for_qr(1.0 + 0.0j, 1.0 + 0.0j, mertens_n, prog, states, kernel_map, "q=1 r=1")
    p_one = pvals_from_traces(traces_one)
    logM = 0.0
    for n, pn in enumerate(p_one, start=1):
        logM += (pn.real / (lam**n)) - 1.0 / n
    mathsf_M = logM + gamma

    pair_values = parse_pair_values(args.pair_values)
    pair_keys = [f"{m1}x{m2}" for m1, m2 in pair_values]
    pair_twist_C: Dict[str, Dict[str, Dict[str, float]]] = {}
    pair_class_C: Dict[str, Dict[str, float]] = {}
    pair_rho: Dict[str, Dict[str, float]] = {}
    pair_rho_max: Dict[str, float] = {}

    for m1, m2 in pair_values:
        omega1 = np.exp(2j * math.pi / m1)
        omega2 = np.exp(2j * math.pi / m2)
        twist_constants: Dict[str, Dict[str, float]] = {}
        rho_vals: Dict[str, float] = {}
        for j1 in range(m1):
            q = omega1**j1
            for j2 in range(m2):
                if j1 == 0 and j2 == 0:
                    continue
                r = omega2**j2
                label = f"m1={m1} m2={m2} j1={j1} j2={j2}"
                traces = traces_for_qr(q, r, mertens_n, prog, states, kernel_map, label)
                pvals = pvals_from_traces(traces)
                C = sum(p / (lam**(i + 1)) for i, p in enumerate(pvals))
                key = f"{j1},{j2}"
                twist_constants[key] = {"re": float(C.real), "im": float(C.imag)}
                rho = spectral_radius(build_weighted_matrix_numeric(q, r, states, kernel_map))
                rho_vals[key] = rho

        class_constants: Dict[str, float] = {}
        denom = float(m1 * m2)
        for r1 in range(m1):
            for r2 in range(m2):
                acc = mathsf_M / denom
                for j1 in range(m1):
                    for j2 in range(m2):
                        if j1 == 0 and j2 == 0:
                            continue
                        key = f"{j1},{j2}"
                        q = omega1**j1
                        r = omega2**j2
                        phase = (q ** (-r1)) * (r ** (-r2))
                        acc += (phase * complex(twist_constants[key]["re"], twist_constants[key]["im"])) / denom
                class_constants[f"{r1},{r2}"] = float(acc.real)

        key_pair = f"{m1}x{m2}"
        pair_twist_C[key_pair] = twist_constants
        pair_class_C[key_pair] = class_constants
        pair_rho[key_pair] = rho_vals
        pair_rho_max[key_pair] = max(rho_vals.values()) if rho_vals else 0.0

    # Backward-compatible (2,2) shortcut
    twist_constants_22 = pair_twist_C.get("2x2", {})
    class_constants_22 = pair_class_C.get("2x2", {})
    rho_vals_22 = pair_rho.get("2x2", {})

    payload: Dict[str, object] = {
        "chi_def": "chi = e - 1_{d=2}",
        "nu_def": "nu = 1_{t in Q_-}",
        "max_n": args.max_n,
        "mertens_n": mertens_n,
        "P_n_2d_latex": P_latex,
        "P_n_2d_terms": [
            {f"{eq},{er}": coeff for (eq, er), coeff in P[n].items()} for n in range(1, args.max_n + 1)
        ],
        "P_n_2d_min_q_exp": min_q_exp,
        "P_n_2d_all_q_exp_nonnegative": all(x >= 0 for x in min_q_exp),
        "mathsf_M": mathsf_M,
        "pair_values": pair_keys,
        "pair_twist_C": pair_twist_C,
        "pair_class_C": pair_class_C,
        "pair_rho": pair_rho,
        "pair_rho_max": pair_rho_max,
        "pair_rho_max_ratio": {k: v / lam for k, v in pair_rho_max.items()},
        "twist_C_22": twist_constants_22,
        "class_C_22": class_constants_22,
        "rho_22": rho_vals_22,
        "rho_22_ratio": {k: v / lam for k, v in rho_vals_22.items()},
    }

    if not args.no_output:
        out_path = (
            Path(args.output)
            if args.output
            else export_dir() / "sync_kernel_real_input_40_arity_2d.json"
        )
        write_json(out_path, payload)
        print(f"[sync-kernel-real-input-arity-2d] wrote {out_path}", flush=True)

    print(f"[sync-kernel-real-input-arity-2d] P_1(q,r)={P_latex[0]}", flush=True)
    print("[sync-kernel-real-input-arity-2d] done", flush=True)


if __name__ == "__main__":
    main()
