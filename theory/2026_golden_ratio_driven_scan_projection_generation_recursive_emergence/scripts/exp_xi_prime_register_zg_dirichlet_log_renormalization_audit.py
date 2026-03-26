#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit Dirichlet log-renormalization for the Zeckendorf--Gödel prime code.

This script audits identities stated in:
  sections/body/zeta_finite_part/xi/
    subsubsec__xi-time-protocol-conclusions-part15d-prime-register-zg-density-leyang-spectrum.tex

Audits (at s=1):
  - Recurrence for F_N(1) = sum_{eps nonadjacent} prod p_k^{-eps_k}
  - Relation r_N = F_N / F_{N-1} and Delta_N = log r_N - 1/p_N
  - Empirical universal constant C_hat for the tail template
        |Delta_N(1)| <= C ( 1/p_N^2 + 1/(p_N p_{N-1}) )
    over a finite audit window, and a resulting explicit tail bound estimate.

Output:
  - artifacts/export/xi_prime_register_zg_dirichlet_log_renormalization_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import mpmath as mp
import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _first_n_primes(n: int) -> List[int]:
    out: List[int] = []
    p = 2
    while len(out) < n:
        if sp.isprime(p):
            out.append(p)
        p += 1
    return out


def _enumerate_F_exact(primes: List[int], n: int) -> sp.Rational:
    """Exact F_n(1) by explicit sum over nonadjacent subsets of {1,...,n}."""
    total = sp.Rational(0)
    for mask in range(1 << n):
        ok = True
        w = sp.Rational(1)
        for k in range(n):
            if (mask >> k) & 1:
                if k > 0 and ((mask >> (k - 1)) & 1):
                    ok = False
                    break
                w *= sp.Rational(1, primes[k])
        if ok:
            total += w
    return total


def _build_F_mp(primes: List[int], n: int) -> Tuple[List[mp.mpf], List[mp.mpf], List[mp.mpf]]:
    """Return F_k, r_k, Delta_k for k=0..n in mp precision at s=1."""
    F: List[mp.mpf] = [mp.mpf("1")]
    if n >= 1:
        F.append(mp.mpf("1") + mp.mpf(1) / primes[0])
    for k in range(2, n + 1):
        p = primes[k - 1]
        F.append(F[k - 1] + F[k - 2] / p)

    r: List[mp.mpf] = [mp.mpf("nan")]  # placeholder for index 0
    for k in range(1, n + 1):
        r.append(F[k] / F[k - 1])

    Delta: List[mp.mpf] = [mp.mpf("nan"), mp.mpf("nan")]  # indices 0,1 unused
    for k in range(2, n + 1):
        p = primes[k - 1]
        Delta.append(mp.log(r[k]) - mp.mpf(1) / p)
    return F, r, Delta


@dataclass(frozen=True)
class Payload:
    n_primes: int
    exact_window_nmax: int
    exact_window_all_ok: bool
    max_C_hat: float
    argmax_k: int
    tail_template_sum_from: int
    tail_template_sum_to: int
    tail_template_sum_value: float
    tail_bound_estimate: float
    G_partial_n: int
    G_partial_value: float
    G_partial_next_value: float
    G_cauchy_gap: float
    elapsed_s: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit ZG Dirichlet log-renormalization at s=1.")
    parser.add_argument("--n", type=int, default=6000, help="Prime cutoff N for Delta_N window.")
    parser.add_argument("--exact-window", type=int, default=10, help="Exact enumeration window for F_n(1).")
    parser.add_argument("--tail-sum-extra", type=int, default=20000, help="Extra primes for tail template sum.")
    args = parser.parse_args()

    t0 = time.time()
    mp.mp.dps = 120

    n = int(args.n)
    exact_nmax = int(args.exact_window)
    tail_extra = int(args.tail_sum_extra)
    if n < 4:
        raise ValueError("--n must be >= 4")
    if exact_nmax < 1:
        raise ValueError("--exact-window must be >= 1")

    primes = _first_n_primes(n + max(2, tail_extra))

    # Exact verification for small n.
    exact_ok = True
    for k in range(0, exact_nmax + 1):
        if k == 0:
            f_rec = sp.Rational(1)
        elif k == 1:
            f_rec = sp.Rational(1) + sp.Rational(1, primes[0])
        else:
            f0 = sp.Rational(1)
            f1 = sp.Rational(1) + sp.Rational(1, primes[0])
            for m in range(2, k + 1):
                f0, f1 = f1, f1 + sp.Rational(1, primes[m - 1]) * f0
            f_rec = f1
        f_enum = _enumerate_F_exact(primes, k)
        if sp.simplify(f_rec - f_enum) != 0:
            exact_ok = False
            break

    # Build mp sequences up to n.
    F, r, Delta = _build_F_mp(primes[:n], n)

    # Empirical best constant C_hat over k=3..n (k=2 has missing p_{k-1} term shape).
    max_ratio = mp.mpf("0")
    argmax_k = 3
    for k in range(3, n + 1):
        pk = mp.mpf(primes[k - 1])
        pkm1 = mp.mpf(primes[k - 2])
        denom = (1 / (pk * pk)) + (1 / (pk * pkm1))
        ratio = abs(Delta[k]) / denom
        if ratio > max_ratio:
            max_ratio = ratio
            argmax_k = k

    # Tail template sum using additional primes for a concrete upper-bound estimate.
    # This is a finite approximation to sum_{k>n} (1/p_k^2 + 1/(p_k p_{k-1})).
    tail_from = n + 1
    tail_to = n + tail_extra
    tail_sum = mp.mpf("0")
    for k in range(tail_from, tail_to + 1):
        pk = mp.mpf(primes[k - 1])
        pkm1 = mp.mpf(primes[k - 2])
        tail_sum += (1 / (pk * pk)) + (1 / (pk * pkm1))

    # Partial sums of G(1) = sum_{k>=2} Delta_k(1) and a Cauchy gap check.
    G_n = mp.fsum(Delta[2 : n + 1])
    n2 = min(2 * n, len(primes) - 2)
    _, _, Delta2 = _build_F_mp(primes[:n2], n2)
    G_2n = mp.fsum(Delta2[2 : n2 + 1])
    gap = abs(G_2n - G_n)

    payload = Payload(
        n_primes=n,
        exact_window_nmax=exact_nmax,
        exact_window_all_ok=bool(exact_ok),
        max_C_hat=float(max_ratio),
        argmax_k=int(argmax_k),
        tail_template_sum_from=int(tail_from),
        tail_template_sum_to=int(tail_to),
        tail_template_sum_value=float(tail_sum),
        tail_bound_estimate=float(max_ratio * tail_sum),
        G_partial_n=int(n),
        G_partial_value=float(G_n),
        G_partial_next_value=float(G_2n),
        G_cauchy_gap=float(gap),
        elapsed_s=float(time.time() - t0),
    )

    out = export_dir() / "xi_prime_register_zg_dirichlet_log_renormalization_audit.json"
    _write_json(out, asdict(payload))

    if not payload.exact_window_all_ok:
        raise AssertionError("Exact recurrence check for F_n(1) failed in the audit window.")
    if not (math.isfinite(payload.max_C_hat) and payload.max_C_hat > 0.0):
        raise AssertionError("Unexpected C_hat value.")

    print(
        "[xi-zg-dirichlet-renormalization] "
        f"N={payload.n_primes} "
        f"C_hat={payload.max_C_hat:.6g} "
        f"G_N={payload.G_partial_value:.12f} "
        f"gap={payload.G_cauchy_gap:.3e} "
        f"tail_bound~{payload.tail_bound_estimate:.3e}",
        flush=True,
    )


if __name__ == "__main__":
    main()

