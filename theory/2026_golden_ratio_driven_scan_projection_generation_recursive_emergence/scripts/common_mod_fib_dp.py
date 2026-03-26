#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Fast modular DP for Fibonacci residue counts c_m(r) modulo F_{m+2}.

Many scripts in this paper use the congruence DP:

    c <- c + roll(c, w),    w = F_{i+1},

where `c[r]` counts subset sums of Fibonacci weights modulo F_{m+2}. A naive
implementation with `np.roll` allocates a fresh array at each step and becomes
allocation-bound for large moduli.

This module implements the same update with a reusable scratch buffer:

    tmp = roll(c, w)
    c  += tmp

which reduces allocations and improves throughput without changing results.

All output is English-only by repository convention.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import List, Protocol, Tuple

import numpy as np

from common_paths import artifacts_dir


class ProgressLike(Protocol):
    def tick(self, msg: str) -> None: ...


def fib_upto(n: int) -> List[int]:
    """Return Fibonacci numbers F_0..F_n with F_0=0,F_1=1."""
    if n < 0:
        raise ValueError("n must be >= 0")
    if n == 0:
        return [0]
    if n == 1:
        return [0, 1]
    F = [0, 1]
    for _ in range(2, n + 1):
        F.append(F[-1] + F[-2])
    return F


def _roll_into(tmp: np.ndarray, c: np.ndarray, shift: int) -> None:
    """tmp[:] = np.roll(c, shift) without allocating."""
    if shift <= 0:
        tmp[:] = c
        return
    # shift is in (0, len(c)).
    tmp[:shift] = c[-shift:]
    tmp[shift:] = c[:-shift]


def counts_mod_fib(m: int, prog: ProgressLike | None = None) -> np.ndarray:
    """Compute residue counts c_m(r) for modulus F_{m+2}.

    Returns:
        c: uint64 array of length F_{m+2}.
    """
    if m < 0:
        raise ValueError("m must be >= 0")

    # Optional on-disk cache to avoid repeated O(m*F_{m+2}) DP across scripts.
    # Disable with OMEGA_MODFIB_NO_CACHE=1.
    no_cache = os.environ.get("OMEGA_MODFIB_NO_CACHE", "").strip() in {"1", "true", "TRUE", "yes", "YES"}

    # Need weights F_{i+1} for i=1..m, and modulus F_{m+2}.
    F = fib_upto(m + 2)
    mod = int(F[m + 2])

    cache_dir = artifacts_dir() / "cache" / "modfib_counts"
    cache_path = cache_dir / f"counts_mod_fib_m{m}_mod{mod}.npy"
    if (not no_cache) and cache_path.is_file():
        try:
            return np.load(cache_path)
        except Exception:
            # Corrupted cache; fall back to recomputation.
            pass

    c = np.zeros(mod, dtype=np.uint64)
    c[0] = 1
    tmp = np.empty_like(c)

    for i in range(1, m + 1):
        w = int(F[i + 1])  # < mod
        _roll_into(tmp, c, w)
        c += tmp
        if prog is not None:
            prog.tick(f"moddp m={m} step={i}/{m} mod={mod}")

    if not no_cache:
        cache_dir.mkdir(parents=True, exist_ok=True)
        tmp_path = cache_path.with_suffix(".tmp.npy")
        try:
            np.save(tmp_path, c)
            tmp_path.replace(cache_path)
        except Exception:
            # Cache write failures must never break reproducibility.
            try:
                if tmp_path.exists():
                    tmp_path.unlink()
            except Exception:
                pass
    return c


def hist_from_counts(c: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    """Return (vals,freq) histogram for nonnegative integer counts.

    This avoids sorting the full array (unlike np.unique on large moduli).
    """
    if c.size == 0:
        return np.array([], dtype=np.uint64), np.array([], dtype=np.uint64)
    try:
        freq = np.bincount(c)  # type: ignore[arg-type]
    except TypeError:
        freq = np.bincount(c.astype(np.int64))
    idx = np.nonzero(freq)[0]
    vals = idx.astype(np.uint64, copy=False)
    fr = freq[idx].astype(np.uint64, copy=False)
    return vals, fr


def counts_mod_fib_hist(m: int, prog: ProgressLike | None = None) -> Tuple[np.ndarray, np.ndarray]:
    """Return (vals,freq) histogram for residue counts c_m(r) mod F_{m+2}."""
    c = counts_mod_fib(m, prog=prog)
    return hist_from_counts(c)

