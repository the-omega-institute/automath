#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Minimal closed-loop for the ((3,3,p)) near-1 pole (pure-collision channel).

What this script does (single file, auditable):
  1) Compute kappa_infty via a Poisson equation on the 4-state memory skeleton
     (Parry Markov chain of A_xi(1)), for the collision cocycle xi=1_{d=2}.
  2) Compute the exact worst twisted ratio rho_{3,3,p}/lambda for odd primes p
     by scanning unit roots u = exp(2π i j/p) in the cubic eigenvalue equation.
  3) Compare exact ratios to the small-angle diffusion law:
       log ratio = -kappa_infty * α^2 + beta * α^4 + O(α^6),  α=2π/p,
     and output errors (2nd-order vs 4th-order).
  4) Provide a first Richardson extrapolation to estimate kappa_infty from data:
       kappa(α) = kappa_infty + c * α^2 + O(α^4),
     hence kappa_infty ≈ (a2*k1 - a1*k2)/(a2 - a1),  a=α^2.
  5) Map ratio -> "pole real part" via s = log_lambda(rho) = 1 + log(ratio)/log(lambda).

Outputs:
  - artifacts/export/arity_pure_collision_near1_pole_closed_loop.json

Notes:
  - We intentionally avoid importing other experiment scripts to keep this a
    minimal, stand-alone reproduction.
  - All stdout is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

import mpmath as mp
import numpy as np

from common_paths import export_dir


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def primes_up_to(n: int) -> List[int]:
    return [p for p in range(2, n + 1) if _is_prime(p)]


def parse_int_list(csv: str) -> List[int]:
    out: List[int] = []
    for tok in csv.split(","):
        t = tok.strip()
        if not t:
            continue
        out.append(int(t))
    return out


def _phi_mp() -> mp.mpf:
    return (1 + mp.sqrt(5)) / 2


def _lambda_mp() -> mp.mpf:
    p = _phi_mp()
    return p * p


def _kappa_closed_mp() -> mp.mpf:
    # kappa_infty = (6*sqrt(5) - 5) / 250.
    return (6 * mp.sqrt(5) - 5) / 250


def _beta_closed_mp() -> mp.mpf:
    # beta = P^{(4)}(0) / 24 = (7 + 24*sqrt(5)) / 75000.
    return (7 + 24 * mp.sqrt(5)) / 75000


def rho_from_u(u: mp.mpc) -> mp.mpf:
    """
    Spectral radius of the 4x4 pure-collision twist A_xi(u) on the unit circle.

    Eigenvalues are -1 and the roots of:
      λ^3 - 2λ^2 - (u+1)λ + u = 0.
    """
    coeffs = [mp.mpc(1), mp.mpc(-2), -(u + 1), u]
    roots = mp.polyroots(coeffs)
    cand = [mp.mpf(1)]  # |-1|
    for r in roots:
        cand.append(abs(r))
    return max(cand)


# --- Poisson equation on the 4-state skeleton (stand-alone) -------------------


@dataclass(frozen=True)
class Edge:
    src: int
    dst: int
    xi: int


def build_skeleton_edges() -> Tuple[np.ndarray, List[Edge]]:
    """
    A_xi(u) in state order (00,01,10,11):
      [[1,1,1,u],
       [1,0,1,0],
       [1,1,0,0],
       [1,0,0,0]]

    At u=1, adjacency A is:
      [[1,1,1,1],
       [1,0,1,0],
       [1,1,0,0],
       [1,0,0,0]]

    The collision cocycle is xi=1 iff transition corresponds to d=2,
    i.e. the unique edge (00 -> 11) which carries the u-weight.
    """
    A = np.array(
        [
            [1.0, 1.0, 1.0, 1.0],
            [1.0, 0.0, 1.0, 0.0],
            [1.0, 1.0, 0.0, 0.0],
            [1.0, 0.0, 0.0, 0.0],
        ],
        dtype=float,
    )
    edges: List[Edge] = []
    for i in range(4):
        for j in range(4):
            if A[i, j] == 0.0:
                continue
            xi = 1 if (i == 0 and j == 3) else 0
            edges.append(Edge(src=i, dst=j, xi=xi))
    return A, edges


def pf_eigenvectors(A: np.ndarray) -> Tuple[float, np.ndarray, np.ndarray]:
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
        raise RuntimeError("PF normalization failed: l^T r = 0")
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


def edge_weight(l: np.ndarray, r: np.ndarray, lam: float, src: int, dst: int) -> float:
    # Parry edge measure: m(e) = l_src * r_dst / lam, assuming l^T r = 1.
    return float(l[src] * r[dst] / lam)


def mu_edge_mean(edges: Sequence[Edge], l: np.ndarray, r: np.ndarray, lam: float) -> float:
    mu = 0.0
    for e in edges:
        mu += edge_weight(l, r, lam, e.src, e.dst) * float(e.xi)
    return float(mu)


def solve_poisson(P: np.ndarray, pi: np.ndarray, b: np.ndarray) -> np.ndarray:
    # Solve (I - P) f = b with gauge constraint pi^T f = 0.
    n = P.shape[0]
    I = np.eye(n, dtype=float)
    A = I - P
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


def sigma2_from_f(edges: Sequence[Edge], l: np.ndarray, r: np.ndarray, lam: float, mu: float, f: np.ndarray) -> float:
    s = 0.0
    for e in edges:
        w = edge_weight(l, r, lam, e.src, e.dst)
        d = float(e.xi) - mu + float(f[e.dst] - f[e.src])
        s += w * d * d
    return float(s)


def kappa_poisson_skeleton() -> Dict[str, float]:
    A, edges = build_skeleton_edges()
    lam, l, r = pf_eigenvectors(A)
    P, pi = parry_chain(A, lam, l, r)
    mu = mu_edge_mean(edges, l, r, lam)

    b = np.zeros((A.shape[0],), dtype=float)
    for e in edges:
        # P_{src,dst} = A_{src,dst} * r_dst/(lam*r_src), and A_{src,dst}∈{0,1}.
        b[e.src] += (r[e.dst] / (lam * r[e.src])) * (float(e.xi) - mu)

    f = solve_poisson(P, pi, b)
    sigma2 = sigma2_from_f(edges, l, r, lam, mu, f)
    return {
        "lambda_pf": float(lam),
        "mu_edge_mean": float(mu),
        "sigma2_poisson": float(sigma2),
        "kappa_poisson": float(0.5 * sigma2),
    }


# --- main experiment ----------------------------------------------------------


@dataclass(frozen=True)
class Row:
    p: int
    j_star: int
    ratio: str
    kappa_p: str
    g_p: str
    s_real: str
    ratio_asymp2: str
    ratio_asymp4: str
    err_asymp2: str
    err_asymp4: str


def richardson_kappa(alpha2_1: mp.mpf, k1: mp.mpf, alpha2_2: mp.mpf, k2: mp.mpf) -> mp.mpf:
    # Cancel the O(alpha^2) drift in kappa(alpha)=k0 + c alpha^2 + O(alpha^4).
    if alpha2_2 == alpha2_1:
        raise ValueError("alpha^2 values must be distinct for Richardson extrapolation")
    return (alpha2_2 * k1 - alpha2_1 * k2) / (alpha2_2 - alpha2_1)


def main() -> None:
    parser = argparse.ArgumentParser(description="Near-1 pole closed loop for pure-collision ((3,3,p)).")
    parser.add_argument("--p-max", type=int, default=101, help="Compute all odd primes up to this bound.")
    parser.add_argument(
        "--p-list",
        type=str,
        default="",
        help="Optional CSV list of odd primes (overrides --p-max).",
    )
    parser.add_argument("--dps", type=int, default=80, help="mpmath decimal precision.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "arity_pure_collision_near1_pole_closed_loop.json"),
    )
    args = parser.parse_args()

    mp.mp.dps = int(args.dps)

    lam = _lambda_mp()
    log_lam = mp.log(lam)

    # kappa_infty from Poisson (4-state skeleton) + closed-form checks
    kp = kappa_poisson_skeleton()
    kappa_poisson = mp.mpf(str(kp["kappa_poisson"]))
    kappa_closed = _kappa_closed_mp()
    beta = _beta_closed_mp()

    print(f"[near1] lambda={mp.nstr(lam, 18)}", flush=True)
    print(f"[near1] kappa_infty (Poisson skeleton) = {mp.nstr(kappa_poisson, 18)}", flush=True)
    print(f"[near1] kappa_infty (closed form)      = {mp.nstr(kappa_closed, 18)}", flush=True)
    print(f"[near1] |diff|                       = {mp.nstr(abs(kappa_poisson - kappa_closed), 6)}", flush=True)
    print(f"[near1] beta (log 4th-order)         = {mp.nstr(beta, 18)}", flush=True)

    # Choose which kappa to use in asymptotics (Poisson is the "auditable extraction").
    kappa_inf = kappa_poisson

    if str(args.p_list).strip():
        ps = [p for p in parse_int_list(str(args.p_list)) if p % 2 == 1 and _is_prime(p)]
    else:
        ps = [p for p in primes_up_to(int(args.p_max)) if p % 2 == 1]

    rows: List[Row] = []
    # For Richardson: store (alpha^2, kappa_p) in order.
    kappa_seq: List[Tuple[int, mp.mpf, mp.mpf]] = []

    for p in ps:
        w = mp.e ** (2 * mp.pi * mp.j / p)
        best_rho = mp.mpf("0")
        best_j = 1
        for j in range(1, p):
            u = w**j
            r = rho_from_u(u)
            if r > best_rho:
                best_rho = r
                best_j = j
        ratio = best_rho / lam
        alpha = 2 * mp.pi / p
        a2 = alpha * alpha
        kappa_p = (1 - ratio) / a2
        g_p = (1 - ratio) * (p * p)
        s_real = 1 + mp.log(ratio) / log_lam

        ratio_as2 = mp.e ** (-kappa_inf * a2)
        ratio_as4 = mp.e ** (-kappa_inf * a2 + beta * (a2 * a2))
        err2 = ratio - ratio_as2
        err4 = ratio - ratio_as4

        rows.append(
            Row(
                p=p,
                j_star=best_j,
                ratio=mp.nstr(ratio, 18),
                kappa_p=mp.nstr(kappa_p, 18),
                g_p=mp.nstr(g_p, 18),
                s_real=mp.nstr(s_real, 18),
                ratio_asymp2=mp.nstr(ratio_as2, 18),
                ratio_asymp4=mp.nstr(ratio_as4, 18),
                err_asymp2=mp.nstr(err2, 6),
                err_asymp4=mp.nstr(err4, 6),
            )
        )
        kappa_seq.append((p, a2, kappa_p))

        if p in (5, 7, 11, 13, 17, 19, 23, 29, 31):
            print(
                f"[near1] p={p:>3} j*={best_j:>3} ratio={mp.nstr(ratio, 12)} "
                f"s={mp.nstr(s_real, 12)} err4={mp.nstr(err4, 3)}",
                flush=True,
            )

    # Richardson estimates using adjacent entries.
    rich: List[Dict[str, object]] = []
    for (p1, a2_1, k1), (p2, a2_2, k2) in zip(kappa_seq, kappa_seq[1:]):
        k0 = richardson_kappa(a2_1, k1, a2_2, k2)
        rich.append(
            {
                "p1": p1,
                "p2": p2,
                "kappa_richardson": mp.nstr(k0, 18),
            }
        )

    payload = {
        "dps": int(args.dps),
        "lambda": mp.nstr(lam, 30),
        "kappa_infty": {
            "poisson_skeleton": {k: (v if isinstance(v, float) else float(v)) for k, v in kp.items()},
            "closed_form": mp.nstr(kappa_closed, 30),
            "abs_diff": mp.nstr(abs(kappa_poisson - kappa_closed), 12),
        },
        "beta_log_4th": mp.nstr(beta, 30),
        "rows": [asdict(r) for r in rows],
        "richardson_adjacent": rich,
    }

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"[near1] wrote {jout}", flush=True)


if __name__ == "__main__":
    main()

