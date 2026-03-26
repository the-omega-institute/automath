#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute arity-charge primitive spectrum for real-input 40-state kernel.

Outputs:
- artifacts/export/sync_kernel_real_input_40_arity.json (default)
"""

from __future__ import annotations

import argparse
import cmath
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


def build_weighted_matrix_numeric(
    q: complex,
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
                i = idx[(s, px, py)]
                j = idx[(dst_state, x, y)]
                M[i, j] += q**chi
    return M


def parse_m_values(text: str) -> List[int]:
    raw = [chunk.strip() for chunk in text.split(",")] if text else []
    ms: List[int] = []
    for chunk in raw:
        if not chunk:
            continue
        try:
            val = int(chunk)
        except ValueError as exc:
            raise SystemExit(f"[arity] invalid m value: {chunk}") from exc
        if val < 2:
            raise SystemExit(f"[arity] m must be >= 2, got {val}")
        ms.append(val)
    if not ms:
        ms = [2, 3, 5, 7, 11]
    return sorted(set(ms))


def poly_add(a: Dict[int, int], b: Dict[int, int]) -> Dict[int, int]:
    out = dict(a)
    for exp, coeff in b.items():
        out[exp] = out.get(exp, 0) + coeff
        if out[exp] == 0:
            del out[exp]
    return out


def poly_mul(a: Dict[int, int], b: Dict[int, int]) -> Dict[int, int]:
    out: Dict[int, int] = {}
    for exp_a, coeff_a in a.items():
        for exp_b, coeff_b in b.items():
            exp = exp_a + exp_b
            out[exp] = out.get(exp, 0) + coeff_a * coeff_b
    return out


def poly_scale_exponent(a: Dict[int, int], factor: int) -> Dict[int, int]:
    return {exp * factor: coeff for exp, coeff in a.items()}


def poly_to_string(poly: Dict[int, int]) -> str:
    if not poly:
        return "0"
    terms: List[str] = []
    for exp in sorted(poly.keys(), reverse=True):
        coeff = poly[exp]
        if exp == 0:
            term = str(coeff)
        elif exp == 1:
            term = "q" if coeff == 1 else f"{coeff}q"
        else:
            term = f"q^{exp}" if coeff == 1 else f"{coeff}q^{exp}"
        terms.append(term)
    return " + ".join(terms)


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


def build_weighted_matrix(
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> List[List[Dict[int, int]]]:
    idx = {state: i for i, state in enumerate(states)}
    n = len(states)
    M: List[List[Dict[int, int]]] = [[{} for _ in range(n)] for _ in range(n)]
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
                i = idx[(s, px, py)]
                j = idx[(dst_state, x, y)]
                M[i][j] = poly_add(M[i][j], {chi: 1})
    return M


def mat_mul(
    A: List[List[Dict[int, int]]],
    B: List[List[Dict[int, int]]],
) -> List[List[Dict[int, int]]]:
    n = len(A)
    res: List[List[Dict[int, int]]] = [[{} for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if not A[i][k]:
                continue
            for j in range(n):
                if not B[k][j]:
                    continue
                res[i][j] = poly_add(res[i][j], poly_mul(A[i][k], B[k][j]))
    return res


def mat_trace(A: List[List[Dict[int, int]]]) -> Dict[int, int]:
    poly: Dict[int, int] = {}
    for i in range(len(A)):
        poly = poly_add(poly, A[i][i])
    return poly


def compute_c_and_P(
    max_n: int,
    prog: Progress,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> Tuple[List[Dict[int, int]], List[Dict[int, int]]]:
    M = build_weighted_matrix(states, kernel_map)
    c: List[Dict[int, int]] = [None] * (max_n + 1)  # type: ignore[assignment]
    A = M
    for n in range(1, max_n + 1):
        if n > 1:
            A = mat_mul(A, M)
        c[n] = mat_trace(A)
        prog.tick(f"trace n={n}/{max_n}")

    P: List[Dict[int, int]] = [None] * (max_n + 1)  # type: ignore[assignment]
    for n in range(1, max_n + 1):
        poly: Dict[int, int] = {}
        for d in range(1, n + 1):
            if n % d != 0:
                continue
            mu = mobius(d)
            cd = poly_scale_exponent(c[n // d], d)
            if mu == 1:
                poly = poly_add(poly, cd)
            elif mu == -1:
                poly = poly_add(poly, {exp: -coeff for exp, coeff in cd.items()})
        # divide by n
        for exp, coeff in list(poly.items()):
            if coeff % n != 0:
                raise ValueError(f"Non-integer P_n coefficient at n={n}, exp={exp}")
            poly[exp] = coeff // n
            if poly[exp] == 0:
                del poly[exp]
        P[n] = poly
    return c, P


def traces_for_q(
    q: complex,
    max_n: int,
    prog: Progress,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
    label: str,
) -> List[complex]:
    M = build_weighted_matrix_numeric(q, states, kernel_map)
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


def class_counts(P: List[Dict[int, int]], max_n: int, m: int) -> List[List[int]]:
    counts: List[List[int]] = []
    for n in range(1, max_n + 1):
        arr = [0] * m
        for exp, coeff in P[n].items():
            arr[exp % m] += coeff
        counts.append(arr)
    return counts


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Arity-charge primitive spectrum for real-input kernel")
    parser.add_argument("--max-n", type=int, default=12, help="Max n for c_n and P_n")
    parser.add_argument("--mertens-n", type=int, default=200, help="Max n for class constants")
    parser.add_argument(
        "--m-values",
        type=str,
        default="2,3,5,7,11",
        help="Comma-separated m values for class decomposition",
    )
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output")
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/sync_kernel_real_input_40_arity.json)",
    )
    args = parser.parse_args()

    prog = Progress(label="sync-kernel-real-input-arity", every_seconds=20.0)
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()

    c, P = compute_c_and_P(args.max_n, prog, states, kernel_map)

    c_polys = [poly_to_string(c[n]) for n in range(1, args.max_n + 1)]
    P_polys = [poly_to_string(P[n]) for n in range(1, args.max_n + 1)]

    # p_n = P_n(1)
    p_vals = [sum(P[n].values()) for n in range(1, args.max_n + 1)]

    # Class constants via roots of unity
    phi = (1.0 + 5.0**0.5) / 2.0
    lam = phi * phi
    gamma = 0.5772156649015329
    mertens_n = args.mertens_n
    m_values = parse_m_values(args.m_values)

    traces_one = traces_for_q(1.0 + 0.0j, mertens_n, prog, states, kernel_map, "q=1")
    p_one = pvals_from_traces(traces_one)
    logM = 0.0
    for n, pn in enumerate(p_one, start=1):
        logM += (pn.real / (lam**n)) - 1.0 / n
    mathsf_M = logM + gamma

    class_constants: Dict[str, Dict[str, List[float]]] = {}
    class_mertens: Dict[str, Dict[str, List[float]]] = {}
    class_rho: Dict[str, List[float]] = {}
    twist_constants: Dict[str, Dict[str, Dict[str, float]]] = {}
    for m in m_values:
        zeta = cmath.exp(2j * math.pi / m)
        Sj: List[complex] = []
        rhos: List[float] = []
        for j in range(1, m):
            q = zeta**j
            traces_q = traces_for_q(q, mertens_n, prog, states, kernel_map, f"m={m} j={j}")
            p_q = pvals_from_traces(traces_q)
            S = 0.0 + 0.0j
            for n, pn in enumerate(p_q, start=1):
                S += pn / (lam**n)
            Sj.append(S)
            rhos.append(float(np.max(np.abs(np.linalg.eigvals(build_weighted_matrix_numeric(q, states, kernel_map))))))

        logM_r: List[float] = []
        mertens_r: List[float] = []
        for r in range(m):
            acc = logM / m
            for j in range(1, m):
                acc += (zeta ** (-j * r)) * Sj[j - 1] / m
            logM_r.append(acc.real)
            mertens_r.append(acc.real + gamma / m)
        class_constants[str(m)] = {str(r): logM_r[r] for r in range(m)}
        class_mertens[str(m)] = {str(r): mertens_r[r] for r in range(m)}
        class_rho[str(m)] = rhos
        twist_constants[str(m)] = {
            str(j + 1): {"re": float(Sj[j].real), "im": float(Sj[j].imag)} for j in range(m - 1)
        }

    class_counts_all = {str(m): class_counts(P, args.max_n, m) for m in m_values}

    payload: Dict[str, object] = {
        "chi_def": "chi = e - 1_{d=2}",
        "max_n": args.max_n,
        "mertens_n": mertens_n,
        "m_values": m_values,
        "c_n_polys": c_polys,
        "P_n_polys": P_polys,
        "P_n_coeffs": [
            {str(exp): coeff for exp, coeff in P[n].items()} for n in range(1, args.max_n + 1)
        ],
        "p_n": p_vals,
        "arity_class_counts": class_counts_all,
        "arity_class_counts_m2": class_counts_all.get("2", class_counts(P, args.max_n, 2)),
        "arity_class_counts_m3": class_counts_all.get("3", class_counts(P, args.max_n, 3)),
        "arity_class_counts_m5": class_counts_all.get("5", class_counts(P, args.max_n, 5)),
        "arity_class_logM": class_constants,
        "arity_class_mertens": class_mertens,
        "arity_class_C": class_mertens,
        "arity_class_rho": class_rho,
        "log_mathfrak_M": logM,
        "mathsf_M": mathsf_M,
        "arity_twist_C": twist_constants,
    }

    if not args.no_output:
        out_path = (
            Path(args.output)
            if args.output
            else export_dir() / "sync_kernel_real_input_40_arity.json"
        )
        write_json(out_path, payload)
        print(f"[sync-kernel-real-input-arity] wrote {out_path}", flush=True)

    print(f"[sync-kernel-real-input-arity] P_1(q)={P_polys[0]}", flush=True)
    print(f"[sync-kernel-real-input-arity] P_2(q)={P_polys[1]}", flush=True)
    print("[sync-kernel-real-input-arity] done", flush=True)


if __name__ == "__main__":
    main()
