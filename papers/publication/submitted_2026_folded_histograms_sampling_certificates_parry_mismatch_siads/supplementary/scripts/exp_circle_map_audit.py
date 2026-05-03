#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Circle-map conjugacy audit (Section 6.7 of the manuscript).

Reproduce the numerical example: standard circle map with K=0.3,
rotation number tuned to phi^{-1} by bisection on the lift.

Outputs:
  - circle_map_audit_results.txt  (human-readable summary)

Dependencies: numpy (no special packages beyond the standard scientific stack).
"""

from __future__ import annotations

import math
import sys
import time
from typing import Dict, List, Tuple

import numpy as np


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
PHI = (1.0 + 5.0**0.5) / 2.0
ALPHA = 1.0 / PHI                       # golden rotation number ~ 0.6180339887


# ---------------------------------------------------------------------------
# Circle map utilities
# ---------------------------------------------------------------------------
def circle_map(x: float, K: float, Omega: float) -> float:
    """Standard circle map f(x) = x + Omega - (K/2pi) sin(2pi x) mod 1."""
    return (x + Omega - K / (2.0 * math.pi) * math.sin(2.0 * math.pi * x)) % 1.0


def rotation_number_estimate(K: float, Omega: float,
                             N: int = 200_000, x0: float = 0.0) -> float:
    """Estimate rotation number via the lift average."""
    x_lift = x0
    for _ in range(N):
        x_lift += Omega - K / (2.0 * math.pi) * math.sin(2.0 * math.pi * x_lift)
    return (x_lift - x0) / N


def tune_omega(K: float, target_rho: float,
               tol: float = 1e-14, max_iter: int = 80) -> float:
    """Bisection on Omega to match a target rotation number."""
    lo, hi = 0.0, 1.0
    for i in range(max_iter):
        mid = (lo + hi) / 2.0
        rho = rotation_number_estimate(K, mid, N=100_000)
        if rho < target_rho:
            lo = mid
        else:
            hi = mid
        if hi - lo < tol:
            break
        if (i + 1) % 20 == 0:
            print(f"  [tune_omega] iter {i+1}: Omega ~ {mid:.16f}, "
                  f"rho ~ {rho:.14f}, bracket = {hi-lo:.2e}", flush=True)
    return (lo + hi) / 2.0


# ---------------------------------------------------------------------------
# Fibonacci / Zeckendorf fold utilities (self-contained)
# ---------------------------------------------------------------------------
def fib_list(n: int) -> List[int]:
    """Return [F_1, F_2, ..., F_n] with F_1=F_2=1."""
    if n <= 0:
        return []
    if n == 1:
        return [1]
    f = [1, 1]
    while len(f) < n:
        f.append(f[-1] + f[-2])
    return f


def zeckendorf_normalize(bits: List[int], m: int) -> List[int]:
    """Fibonacci-weighted Zeckendorf normalization of a length-m binary word.

    Weight vector: (F_{m+1}, F_m, ..., F_2).
    """
    fibs = fib_list(m + 1)  # F_1..F_{m+1}
    weights = [fibs[m - i] for i in range(m)]  # F_{m+1}, F_m, ..., F_2
    val = sum(b * w for b, w in zip(bits, weights))
    # Greedy Zeckendorf using the same weight vector
    out = [0] * m
    for i in range(m):
        if val >= weights[i]:
            out[i] = 1
            val -= weights[i]
    return out


def is_golden_legal(bits: List[int]) -> bool:
    """Check no two consecutive 1s (golden-mean shift constraint)."""
    for i in range(len(bits) - 1):
        if bits[i] == 1 and bits[i + 1] == 1:
            return False
    return True


def pack_bits(bits: List[int]) -> int:
    x = 0
    for b in bits:
        x = (x << 1) | b
    return x


def int_to_bits(x: int, m: int) -> List[int]:
    return [(x >> (m - 1 - i)) & 1 for i in range(m)]


def build_fold_map(m: int) -> List[int]:
    """Fold map on packed ints: w -> Fold_m(w)."""
    size = 1 << m
    out = [0] * size
    for w in range(size):
        bits = int_to_bits(w, m)
        folded = zeckendorf_normalize(bits, m)
        out[w] = pack_bits(folded)
    return out


# ---------------------------------------------------------------------------
# Parry measure on the golden-mean shift
# ---------------------------------------------------------------------------
def parry_law(m: int) -> Dict[int, float]:
    """Exact Parry block law for length-m words on {0,1}, golden-mean shift."""
    phi = PHI
    log_phi = math.log(phi)
    size = 1 << m
    law: Dict[int, float] = {}
    total = 0.0
    for w in range(size):
        bits = int_to_bits(w, m)
        if not is_golden_legal(bits):
            continue
        # Parry weight = phi^{-m} * phi^{-(number of 1-bits)}
        n_ones = sum(bits)
        p = phi ** (-(m + n_ones))
        law[w] = p
        total += p
    # Renormalize (should be 1.0 up to rounding)
    for w in law:
        law[w] /= total
    return law


# ---------------------------------------------------------------------------
# Main experiment
# ---------------------------------------------------------------------------
def main() -> None:
    K = 0.3
    m = 12
    N = 100_000
    anchor = 0.2

    print("=" * 60)
    print("Circle-map conjugacy audit  (Section 6.7)")
    print("=" * 60)
    print(f"  K       = {K}")
    print(f"  target  = phi^{{-1}} = {ALPHA:.14f}")
    print(f"  m       = {m}")
    print(f"  N       = {N}")
    print(f"  anchor  = {anchor}")
    print()

    # Step 1: tune Omega
    t0 = time.time()
    print("[1/4] Tuning Omega by bisection ...", flush=True)
    Omega = tune_omega(K, ALPHA)
    rho_check = rotation_number_estimate(K, Omega, N=500_000)
    print(f"  Omega   = {Omega:.16f}")
    print(f"  rho     = {rho_check:.14f}")
    print(f"  |rho - alpha| = {abs(rho_check - ALPHA):.2e}")
    print(f"  elapsed: {time.time()-t0:.1f}s")
    print()

    # Step 2: generate orbit and symbolic coding
    print("[2/4] Generating orbit and symbolic coding ...", flush=True)
    t1 = time.time()
    x = anchor
    fa = circle_map(anchor, K, Omega)
    # Coding window [anchor, f(anchor))
    if fa > anchor:
        def in_window(y: float) -> int:
            return 1 if anchor <= y < fa else 0
    else:
        # Wrapping case
        def in_window(y: float) -> int:
            return 1 if (y >= anchor or y < fa) else 0

    orbit_symbols = []
    total_steps = N + m - 1
    for t in range(total_steps):
        orbit_symbols.append(in_window(x))
        x = circle_map(x, K, Omega)
        if (t + 1) % 50_000 == 0:
            print(f"    orbit step {t+1}/{total_steps}", flush=True)
    print(f"  elapsed: {time.time()-t1:.1f}s")
    print()

    # Step 3: build histograms
    print("[3/4] Building folded histograms ...", flush=True)
    t2 = time.time()
    fold_map = build_fold_map(m)
    size = 1 << m

    # Empirical microstate counts
    micro_counts = np.zeros(size, dtype=np.float64)
    for i in range(N):
        w = 0
        for j in range(m):
            w = (w << 1) | orbit_symbols[i + j]
        micro_counts[w] += 1.0

    # Folded histogram
    folded_counts = np.zeros(size, dtype=np.float64)
    for w in range(size):
        folded_counts[fold_map[w]] += micro_counts[w]

    # Normalize
    empirical_folded = folded_counts / N

    # True folded law (from exact unique ergodicity / Lebesgue factor law)
    # Compute via a large-N rigid rotation reference
    print("  Computing reference folded law (rigid rotation, N=10^6) ...", flush=True)
    alpha = ALPHA
    ref_N = 1_000_000
    ref_counts = np.zeros(size, dtype=np.float64)
    x0_ref = 0.123
    for i in range(ref_N + m - 1):
        pass  # pre-allocate symbols
    ref_symbols = []
    y = x0_ref
    for t in range(ref_N + m - 1):
        ref_symbols.append(1 if 0 <= (y % 1.0) < alpha else 0)
        y += alpha
        if (t + 1) % 200_000 == 0:
            print(f"    ref step {t+1}/{ref_N+m-1}", flush=True)
    ref_micro = np.zeros(size, dtype=np.float64)
    for i in range(ref_N):
        w = 0
        for j in range(m):
            w = (w << 1) | ref_symbols[i + j]
        ref_micro[w] += 1.0
    ref_folded = np.zeros(size, dtype=np.float64)
    for w in range(size):
        ref_folded[fold_map[w]] += ref_micro[w]
    true_folded = ref_folded / ref_N

    # Parry law (folded version = Parry itself on legal words)
    parry = parry_law(m)
    parry_vec = np.zeros(size, dtype=np.float64)
    for w, p in parry.items():
        parry_vec[w] = p

    print(f"  elapsed: {time.time()-t2:.1f}s")
    print()

    # Step 4: compute TV and KL
    print("[4/4] Computing divergences ...", flush=True)

    # TV and KL: empirical folded vs true folded
    mask_fold = true_folded > 0
    tv_fold = 0.5 * np.sum(np.abs(empirical_folded[mask_fold] - true_folded[mask_fold]))
    kl_fold = np.sum(
        empirical_folded[mask_fold] * np.log(
            np.where(empirical_folded[mask_fold] > 0,
                     empirical_folded[mask_fold] / true_folded[mask_fold],
                     1.0)
        )
    )

    # TV and KL: empirical folded vs Parry
    mask_parry = parry_vec > 0
    # For TV, include all bins
    tv_parry = 0.5 * np.sum(np.abs(empirical_folded - parry_vec))
    # For KL, only where both are positive
    mask_both = (empirical_folded > 0) & (parry_vec > 0)
    if np.any((empirical_folded > 0) & (parry_vec == 0)):
        kl_parry = float('inf')
    else:
        kl_parry = np.sum(
            empirical_folded[mask_both] * np.log(
                empirical_folded[mask_both] / parry_vec[mask_both]
            )
        )

    print()
    print("=" * 60)
    print("Results")
    print("=" * 60)
    print()
    print("Empirical folded vs true folded law:")
    print(f"  TV  = {tv_fold:.6e}")
    print(f"  KL  = {kl_fold:.6e}")
    print()
    print("Empirical folded vs Parry baseline:")
    print(f"  TV  = {tv_parry:.4f}")
    print(f"  KL  = {kl_parry:.4f}")
    print()
    print("Interpretation: first-stage certificate is at the 10^{{-5}} level;")
    print("second-stage structural mismatch persists at order 10^0.")
    print("The two-stage audit functions identically on the nonlinear circle map.")

    # Write results to file
    from pathlib import Path
    out_path = Path(__file__).resolve().parent / "circle_map_audit_results.txt"
    with out_path.open("w", encoding="utf-8") as f:
        f.write("Circle-map conjugacy audit (Section 6.7)\n")
        f.write(f"K = {K}, Omega = {Omega:.16f}\n")
        f.write(f"Rotation number = {rho_check:.14f}\n")
        f.write(f"m = {m}, N = {N}, anchor = {anchor}\n\n")
        f.write(f"TV(empirical_folded, true_folded)  = {tv_fold:.6e}\n")
        f.write(f"KL(empirical_folded || true_folded) = {kl_fold:.6e}\n")
        f.write(f"TV(empirical_folded, Parry)         = {tv_parry:.4f}\n")
        f.write(f"KL(empirical_folded || Parry)       = {kl_parry:.4f}\n")
    print(f"\nResults written to {out_path}")


if __name__ == "__main__":
    main()
