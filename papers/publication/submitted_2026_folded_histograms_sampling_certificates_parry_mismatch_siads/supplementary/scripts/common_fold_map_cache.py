#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Cached construction of Fold_m maps on packed micro-words.

Several audit scripts enumerate over packed micro words w in [0,2^m) and require:
    fold_map_m[w] = pack(Fold_m(bits(w)))   in [0,2^m).

Building this map repeatedly across scripts is expensive. We therefore cache it
on disk under:
    artifacts/cache/fold_maps/fold_map_m{m}.npy

Disable caching with:
    OMEGA_FOLDMAP_NO_CACHE=1

All output is English-only by repository convention.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import List, Protocol

import numpy as np

from common_paths import artifacts_dir
from common_phi_fold import fold_m


class ProgressLike(Protocol):
    def tick(self, msg: str) -> None: ...


def _cache_path(m: int) -> Path:
    return artifacts_dir() / "cache" / "fold_maps" / f"fold_map_m{int(m)}.npy"


def _int_to_bits(x: int, m: int) -> List[int]:
    # MSB-first bit list, length m.
    return [(x >> (m - 1 - i)) & 1 for i in range(m)]


def fold_map_packed(m: int, prog: ProgressLike | None = None) -> np.ndarray:
    """Return fold_map_m as a uint32 array of length 2^m."""
    m = int(m)
    if m < 0:
        raise ValueError("m must be >= 0")
    size = 1 << m

    no_cache = os.environ.get("OMEGA_FOLDMAP_NO_CACHE", "").strip() in {"1", "true", "TRUE", "yes", "YES"}
    cache_path = _cache_path(m)
    if (not no_cache) and cache_path.is_file():
        try:
            arr = np.load(cache_path)
            if int(arr.shape[0]) == size:
                return arr.astype(np.uint32, copy=False)
        except Exception:
            pass

    out = np.zeros(size, dtype=np.uint32)
    for w in range(size):
        bits = _int_to_bits(w, m)
        folded = fold_m(bits)
        y = 0
        for b in folded:
            y = (y << 1) | (1 if b else 0)
        out[w] = np.uint32(y)
        # Reduce Python overhead: only tick occasionally; Progress already rate-limits prints.
        if prog is not None and (w & 0x3FFF) == 0:
            prog.tick(f"build_fold_map m={m} w={w}/{size}")

    if not no_cache:
        cache_path.parent.mkdir(parents=True, exist_ok=True)
        tmp_path = cache_path.with_suffix(".tmp.npy")
        try:
            np.save(tmp_path, out)
            tmp_path.replace(cache_path)
        except Exception:
            try:
                if tmp_path.exists():
                    tmp_path.unlink()
            except Exception:
                pass
    return out

