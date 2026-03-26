#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit: empirical Haar mixing for the Fold Stokes defect D_{n->m}.

This script is English-only by repository convention.

We sample omega ~ Unif({0,1}^n) and compute the m-bit defect:
  D_{n->m}(omega) = Fold_m(omega_{1..m}) XOR pi_{n->m}(Fold_n(omega)).

We report, for each m:
- F2-rank of the linear span of observed defects in (Z/2)^m (a proxy for H_m generation),
- empirical TV distance to uniform on (Z/2)^m when rank==m and 2^m is tractable,
- max absolute empirical Fourier coefficient over characters (exact when m<=12; else random subset).

Outputs:
- artifacts/export/fold_stokes_defect_haar_mixing_audit.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir


def fib_upto(n: int) -> List[int]:
    """Return Fibonacci numbers F_0..F_n with F_0=0,F_1=1."""
    if n < 0:
        raise ValueError("n must be >= 0")
    F = [0, 1]
    for _ in range(2, n + 1):
        F.append(F[-1] + F[-2])
    return F[: n + 1]


def zeckendorf_digits_fixed(N: int, length: int, F: List[int]) -> List[int]:
    """Greedy Zeckendorf digits of length `length` for weights F_{k+1}, k=1..length."""
    if N < 0:
        raise ValueError("N must be >= 0")
    if length < 0:
        raise ValueError("length must be >= 0")
    if length == 0:
        return []
    # Need weights up to F_{length+1}.
    if len(F) <= length + 1:
        raise ValueError("F list too short for requested length")
    rem = int(N)
    out = [0] * length
    prev_one = False
    for k in range(length, 0, -1):
        w = int(F[k + 1])  # F_{k+1}
        if (not prev_one) and rem >= w:
            out[k - 1] = 1
            rem -= w
            prev_one = True
        else:
            out[k - 1] = 0
            prev_one = False
    if rem != 0:
        raise RuntimeError("Zeckendorf greedy failed to exhaust remainder")
    return out


def fold_micro_bits_to_stable_bits(micro_bits: np.ndarray, F: List[int]) -> np.ndarray:
    """Fold micro bits (0/1 array) to a stable word in X_len (as uint8 array)."""
    if micro_bits.ndim != 1:
        raise ValueError("micro_bits must be a 1D array")
    m = int(micro_bits.shape[0])
    if m == 0:
        return np.zeros((0,), dtype=np.uint8)
    # Compute N = sum_{k=1}^m omega_k F_{k+1}.
    N = 0
    for idx in range(m):
        if int(micro_bits[idx]) & 1:
            N += int(F[idx + 2])  # F_{(idx+1)+1} = F_{idx+2}
    # One extra digit captures the overflow bit at weight F_{m+2}.
    digits = zeckendorf_digits_fixed(N, length=m + 1, F=F)
    stable = np.asarray(digits[:m], dtype=np.uint8)
    return stable


def _mask_from_bits(bits: np.ndarray) -> int:
    """Pack a 0/1 uint8 array into an integer bitmask (LSB = first coordinate)."""
    x = 0
    for i, b in enumerate(bits.tolist()):
        if int(b) & 1:
            x |= 1 << int(i)
    return int(x)


def f2_rank(vectors: List[int], m: int) -> int:
    """Rank of the F2-span of bitmasks in m bits."""
    basis: Dict[int, int] = {}
    r = 0
    for v in vectors:
        x = int(v) & ((1 << int(m)) - 1)
        while x:
            hb = int(x.bit_length() - 1)
            if hb in basis:
                x ^= basis[hb]
            else:
                basis[hb] = x
                r += 1
                break
    return int(r)


def parity(mask_u: int, mask_v: int) -> int:
    """Return (-1)^{popcount(u&v)} as +1 or -1."""
    return -1 if (int(mask_u & mask_v).bit_count() & 1) else 1


@dataclass(frozen=True)
class Row:
    m: int
    n: int
    samples: int
    span_rank_f2: int
    tv_to_uniform_if_full_rank: float | None
    max_abs_fourier: float
    max_abs_fourier_u: int
    fourier_examined: int


def run_for_m(m: int, n: int, samples: int, seed: int, max_chars_exact: int = 12) -> Row:
    if n < m:
        raise ValueError("Require n >= m")
    rng = np.random.default_rng(int(seed) + 1000003 * int(m) + 10007 * int(n))
    F_n = fib_upto(n + 2)
    F_m = fib_upto(m + 2)

    defects: List[int] = []
    counts: Dict[int, int] = {}

    for _ in range(int(samples)):
        omega = rng.integers(0, 2, size=n, dtype=np.uint8)
        fold_m = fold_micro_bits_to_stable_bits(omega[:m], F=F_m)
        fold_n = fold_micro_bits_to_stable_bits(omega, F=F_n)
        d_bits = np.bitwise_xor(fold_m, fold_n[:m])
        d = _mask_from_bits(d_bits)
        defects.append(int(d))
        counts[d] = int(counts.get(d, 0) + 1)

    rank = f2_rank(defects, m=m)

    tv: float | None = None
    if rank == m and m <= int(max_chars_exact):
        # Exact histogram TV vs uniform on full group.
        tot = float(samples)
        unif = 1.0 / float(1 << m)
        s = 0.0
        for x in range(1 << m):
            p = float(counts.get(int(x), 0)) / tot
            s += abs(p - unif)
        tv = 0.5 * s

    # Fourier audit: exact for small m, otherwise random subset.
    tot = float(samples)
    if m <= int(max_chars_exact):
        us = list(range(1, 1 << m))
    else:
        # Random subset of characters.
        k = min(2048, (1 << min(m, 20)) - 1)
        us = rng.choice(np.arange(1, 1 << m, dtype=np.int64), size=int(k), replace=False).tolist()

    max_abs = -1.0
    max_u = 0
    for u in us:
        s = 0.0
        for d, c in counts.items():
            s += float(c) * float(parity(int(u), int(d)))
        coef = abs(s / tot)
        if coef > max_abs:
            max_abs = float(coef)
            max_u = int(u)

    return Row(
        m=int(m),
        n=int(n),
        samples=int(samples),
        span_rank_f2=int(rank),
        tv_to_uniform_if_full_rank=tv,
        max_abs_fourier=float(max_abs),
        max_abs_fourier_u=int(max_u),
        fourier_examined=int(len(us)),
    )


def main() -> None:
    ap = argparse.ArgumentParser(description="Empirical Haar mixing audit for D_{n->m}.")
    ap.add_argument("--m-list", type=str, default="4,6,8,10,12")
    ap.add_argument("--n", type=int, default=64)
    ap.add_argument("--samples", type=int, default=20000)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()

    ms = [int(x.strip()) for x in str(args.m_list).split(",") if x.strip()]
    if not ms:
        raise SystemExit("Require --m-list to contain at least one integer")
    if args.n < 1 or args.samples < 1:
        raise SystemExit("Require --n >= 1 and --samples >= 1")

    rows: List[Row] = []
    for m in ms:
        if m < 1:
            raise SystemExit("Require all m >= 1")
        if args.n < m:
            raise SystemExit("Require --n >= max(m)")
        row = run_for_m(m=m, n=int(args.n), samples=int(args.samples), seed=int(args.seed))
        rows.append(row)
        tv_str = "n/a" if row.tv_to_uniform_if_full_rank is None else f"{row.tv_to_uniform_if_full_rank:.4e}"
        print(
            f"[fold_stokes_defect_haar_mixing_audit] m={row.m} n={row.n} samples={row.samples} "
            f"rank={row.span_rank_f2} tv={tv_str} max|Fourier|={row.max_abs_fourier:.4e}",
            flush=True,
        )

    payload = {
        "params": {"m_list": ms, "n": int(args.n), "samples": int(args.samples), "seed": int(args.seed)},
        "rows": [asdict(r) for r in rows],
    }
    out = export_dir() / "fold_stokes_defect_haar_mixing_audit.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

