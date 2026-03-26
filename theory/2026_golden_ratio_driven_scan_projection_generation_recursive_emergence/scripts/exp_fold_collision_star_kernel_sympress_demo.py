#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Demo: symmetric (orbit-compressed) star moment-kernel from a labeled A2 decomposition.

This script implements the engineering core of the "star + permutation symmetry"
dimension reduction idea:
  - start from a 3-state pair-collision kernel with a *center-symbol* decomposition
      A2 = B0 + B1,
    where Ba[i,j] counts the number of leaf-symbol choices that move leaf-state i
    to leaf-state j given center symbol a in {0,1};
  - build the (k-1)-leaf star kernel and compress by S_{k-1} symmetry, yielding a
    matrix of dimension C(k+1,2) indexed by (n1,n2,n3) with n1+n2+n3=k-1.

IMPORTANT:
  In this repo, the 3x3 A2 used for S2(m) is an *unlabeled* nonnegative realization.
  A decomposition (B0,B1) is additional structure. This demo exposes the interface:
    - if you provide a correct (B0,B1), the script will construct the compressed
      kernel \\tilde A_k and estimate its Perron root.
    - we ship a small placeholder decomposition consistent with the published A2
      adjacency, but it is not guaranteed to match Fold moment roots for k>=3.

Outputs (default):
  - artifacts/export/fold_collision_star_kernel_sympress_demo.json

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from functools import lru_cache
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir


# Placeholder decomposition with B0+B1 = A2 (paper-canonical nonnegative realization).
# Users can override via --B-json.
DEFAULT_B0: List[List[int]] = [
    [0, 0, 0],
    [0, 0, 1],
    [1, 0, 1],
]
DEFAULT_B1: List[List[int]] = [
    [0, 0, 1],
    [0, 1, 0],
    [1, 1, 0],
]


def _fact_upto(n: int) -> List[int]:
    f = [1] * (n + 1)
    for i in range(2, n + 1):
        f[i] = f[i - 1] * i
    return f


def _multinomial(fact: List[int], n: int, a: int, b: int, c: int) -> int:
    return fact[n] // (fact[a] * fact[b] * fact[c])


def orbit_states(k: int) -> List[Tuple[int, int, int]]:
    """Enumerate (n1,n2,n3) with n1+n2+n3=k-1 in a deterministic order."""
    if k < 2:
        raise ValueError("k must be >= 2")
    n = k - 1
    out: List[Tuple[int, int, int]] = []
    for n1 in range(n + 1):
        for n2 in range(n - n1 + 1):
            n3 = n - n1 - n2
            out.append((n1, n2, n3))
    return out


def _as_int_matrix(B: List[List[int]]) -> np.ndarray:
    M = np.array(B, dtype=np.int64)
    if M.shape != (3, 3):
        raise ValueError("Expected a 3x3 matrix")
    if np.any(M < 0):
        raise ValueError("Expected nonnegative entries")
    return M


def _load_B_json(path: Path) -> Tuple[np.ndarray, np.ndarray]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict) or "B0" not in payload or "B1" not in payload:
        raise ValueError("Expected JSON object with keys: B0, B1 (each a 3x3 integer matrix).")
    return _as_int_matrix(payload["B0"]), _as_int_matrix(payload["B1"])


def _power_iteration_sparse(rows: List[List[Tuple[int, float]]], iters: int = 2000, tol: float = 1e-12) -> float:
    """Estimate spectral radius of a nonnegative matrix given sparse rows (row-major)."""
    n = len(rows)
    v = np.ones(n, dtype=np.float64)
    v /= float(n)
    lam_prev = 0.0
    for _ in range(iters):
        w = np.zeros(n, dtype=np.float64)
        for i, row in enumerate(rows):
            s = 0.0
            for j, aij in row:
                s += aij * float(v[j])
            w[i] = s
        ssum = float(np.sum(w))
        if ssum <= 0.0:
            return 0.0
        lam = ssum / float(np.sum(v))
        w /= ssum
        if lam_prev > 0 and abs(lam - lam_prev) / lam_prev < tol:
            return float(lam)
        v = w
        lam_prev = lam
    return float(lam_prev)


def build_tilde_Ak_sparse(B0: np.ndarray, B1: np.ndarray, k: int) -> Tuple[List[Tuple[int, int, int]], List[List[Tuple[int, float]]]]:
    """Return (states, sparse_rows) for \\tilde A_k."""
    if k < 2:
        raise ValueError("k must be >= 2")
    total = k - 1
    states = orbit_states(k)
    idx = {st: i for i, st in enumerate(states)}

    fact = _fact_upto(total)

    # Precompute single-group polynomials for each center symbol a, row i, and exponent e:
    #   (b1 y1 + b2 y2 + b3 y3)^e.
    @lru_cache(maxsize=None)
    def poly_row(a: int, i: int, e: int) -> Dict[Tuple[int, int], int]:
        B = B0 if a == 0 else B1
        w1, w2, w3 = int(B[i, 0]), int(B[i, 1]), int(B[i, 2])
        out: Dict[Tuple[int, int], int] = {}
        for t1 in range(e + 1):
            for t2 in range(e - t1 + 1):
                t3 = e - t1 - t2
                coeff = _multinomial(fact, e, t1, t2, t3)
                if w1 != 0:
                    coeff *= w1**t1
                else:
                    if t1 != 0:
                        continue
                if w2 != 0:
                    coeff *= w2**t2
                else:
                    if t2 != 0:
                        continue
                if w3 != 0:
                    coeff *= w3**t3
                else:
                    if t3 != 0:
                        continue
                if coeff != 0:
                    out[(t1, t2)] = out.get((t1, t2), 0) + int(coeff)
        return out

    def convolve(A: Dict[Tuple[int, int], int], B: Dict[Tuple[int, int], int]) -> Dict[Tuple[int, int], int]:
        out: Dict[Tuple[int, int], int] = {}
        for (a1, a2), ca in A.items():
            for (b1, b2), cb in B.items():
                c1 = a1 + b1
                c2 = a2 + b2
                if c1 + c2 > total:
                    continue
                out[(c1, c2)] = out.get((c1, c2), 0) + ca * cb
        return out

    rows: List[List[Tuple[int, float]]] = [[] for _ in states]
    for st in states:
        n1, n2, n3 = st
        i = idx[st]
        accum: Dict[int, int] = {}
        for a in (0, 1):
            dist: Dict[Tuple[int, int], int] = {(0, 0): 1}
            dist = convolve(dist, poly_row(a, 0, n1))
            dist = convolve(dist, poly_row(a, 1, n2))
            dist = convolve(dist, poly_row(a, 2, n3))
            for (m1, m2), w in dist.items():
                m3 = total - m1 - m2
                j = idx[(m1, m2, m3)]
                accum[j] = accum.get(j, 0) + int(w)
        # Store sparse row as float weights (safe for PF estimation).
        rows[i] = [(j, float(w)) for j, w in sorted(accum.items()) if w != 0]
    return states, rows


@dataclass(frozen=True)
class Summary:
    k: int
    dim: int
    rho_est: float
    note: str


def main() -> None:
    ap = argparse.ArgumentParser(description="Demo: build orbit-compressed star kernel \\tilde A_k from (B0,B1).")
    ap.add_argument("--k", type=int, default=6, help="Moment order k (>=2).")
    ap.add_argument("--B-json", type=str, default="", help="Optional JSON file with keys B0,B1 (3x3 int matrices).")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_star_kernel_sympress_demo.json"),
        help="Output JSON path.",
    )
    args = ap.parse_args()

    k = int(args.k)
    if k < 2:
        raise SystemExit("Require k>=2")

    if str(args.B_json).strip():
        B0, B1 = _load_B_json(Path(str(args.B_json)))
        note = f"loaded B from {args.B_json}"
    else:
        B0, B1 = _as_int_matrix(DEFAULT_B0), _as_int_matrix(DEFAULT_B1)
        note = "default placeholder B0,B1 (B0+B1 equals paper-canonical A2 adjacency)"

    A2 = B0 + B1
    # A cheap spectral-radius proxy for A2 (not exact, but informative in JSON).
    rho_A2 = float(np.max(np.abs(np.linalg.eigvals(A2.astype(np.float64)))))

    states, sparse_rows = build_tilde_Ak_sparse(B0, B1, k=k)
    rho = _power_iteration_sparse(sparse_rows, iters=2500, tol=1e-13)

    # Optional comparison to paper-canonical r_k (if available).
    rk_paper = None
    try:
        import exp_fold_collision_renyi_spectrum as rs

        if k == 2:
            rk_paper = float(rs.perron_root_r2())
        elif k == 3:
            rk_paper = float(rs.perron_root_r3())
        elif k == 4:
            rk_paper = float(rs.perron_root_r4())
        elif k in rs.PRECOMPUTED_RQ:
            rk_paper = float(rs.PRECOMPUTED_RQ[k])
    except Exception:
        rk_paper = None

    summary = Summary(k=k, dim=len(states), rho_est=float(rho), note=note)
    payload = {
        "k": k,
        "dim": len(states),
        "B0": B0.tolist(),
        "B1": B1.tolist(),
        "A2": A2.tolist(),
        "rho_A2_proxy": rho_A2,
        "rho_tilde_Ak_est": float(rho),
        "paper_r_k_if_known": rk_paper,
        "gap_vs_paper": (float(rho) - float(rk_paper)) if rk_paper is not None else None,
        "states_order": [{"idx": i, "n": list(st)} for i, st in enumerate(states)],
        "summary": asdict(summary),
    }

    out = Path(str(args.json_out))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[star-sympress] wrote {out}", flush=True)
    if rk_paper is not None:
        print(f"[star-sympress] k={k} rho(tilde_Ak)~{rho:.12f} vs paper r_k={rk_paper:.12f}", flush=True)
    else:
        print(f"[star-sympress] k={k} rho(tilde_Ak)~{rho:.12f}", flush=True)


if __name__ == "__main__":
    main()

