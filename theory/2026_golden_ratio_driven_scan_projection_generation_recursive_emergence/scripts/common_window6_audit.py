#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Shared helpers for the window-6 audit scripts.

All code is English-only by repository convention.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from functools import lru_cache
from typing import Dict, List, Mapping, Sequence, Tuple

import numpy as np

from common_phi_fold import fib_upto, word_to_str, zeckendorf_digits


BOUNDARY_WORDS_6: Tuple[str, str, str] = ("100001", "100101", "101001")
EVENT_CODES_6: Mapping[str, int] = {
    "stay": 1,
    "refine": 2,
    "flip_100001": 3,
    "flip_100101": 4,
    "flip_101001": 5,
    "decode": 6,
}
LEDGER_BASE_6 = 8


def golden_words(m: int) -> List[str]:
    """All length-m golden-mean legal binary words."""
    if m < 0:
        raise ValueError("m must be non-negative")
    out: List[str] = []

    def rec(pos: int, prev1: int, acc: List[int]) -> None:
        if pos == m:
            out.append(word_to_str(acc))
            return
        acc.append(0)
        rec(pos + 1, 0, acc)
        acc.pop()
        if prev1 == 0:
            acc.append(1)
            rec(pos + 1, 1, acc)
            acc.pop()

    rec(0, 0, [])
    return out


def _K_of_target(limit: int) -> int:
    fib = [1, 1]
    while fib[-1] <= limit:
        fib.append(fib[-1] + fib[-2])
    return len(fib) - 2


def K_of_m(m: int) -> int:
    if m < 0:
        raise ValueError("m must be non-negative")
    return _K_of_target((1 << m) - 1)


def V_word(word: str) -> int:
    """Zeckendorf value V_m(word)=sum_k w_k F_{k+1}."""
    m = len(word)
    fib = fib_upto(m + 2)
    return sum((1 if ch == "1" else 0) * fib[i + 1] for i, ch in enumerate(word))


def fold_bin_word(n: int, m: int) -> str:
    """Binary-interval fold prefix of n to a legal word of length m."""
    if n < 0 or n >= (1 << m):
        raise ValueError(f"n must lie in [0, 2^{m})")
    K = K_of_m(m)
    digits = zeckendorf_digits(n, K)
    return word_to_str(digits[:m])


def micro_bits(n: int, m: int = 6) -> str:
    return format(int(n), f"0{m}b")


def first_primes(count: int) -> List[int]:
    if count < 0:
        raise ValueError("count must be non-negative")
    out: List[int] = []
    x = 2
    while len(out) < count:
        is_prime = True
        r = int(x**0.5)
        for p in out:
            if p > r:
                break
            if x % p == 0:
                is_prime = False
                break
        if is_prime:
            out.append(x)
        x += 1
    return out


def boundary_words(m: int) -> List[str]:
    return [w for w in golden_words(m) if w[0] == "1" and w[-1] == "1"]


def boundary_delta_pattern(m: int) -> List[int]:
    words = boundary_words(m)
    pre = fold_preimages(m)
    patterns = sorted({tuple(sorted({n - V_word(w) for n in pre[w]})) for w in words})
    if len(patterns) != 1:
        raise AssertionError(f"Boundary delta pattern is not unique at m={m}: {patterns}")
    return list(patterns[0])


def fold_preimages(m: int) -> Dict[str, List[int]]:
    words = golden_words(m)
    pre: Dict[str, List[int]] = {w: [] for w in words}
    for n in range(1 << m):
        pre[fold_bin_word(n, m)].append(n)
    if any(len(v) == 0 for v in pre.values()):
        raise AssertionError("Some legal words have empty fold preimages.")
    return pre


@dataclass
class Window6Data:
    m: int
    words: List[str]
    cyclic_words: List[str]
    boundary_words: List[str]
    V_map: Dict[str, int]
    preimages: Dict[str, List[int]]
    d_map: Dict[str, int]
    histogram: Dict[int, int]
    sheet_pairs: List[Dict[str, int | str]]
    log_gauge: float
    g6: float
    kappa6: float
    anomaly_rank: int
    representative_microstates: Dict[str, int]


@lru_cache(maxsize=1)
def window6_data() -> Window6Data:
    m = 6
    words = sorted(golden_words(m))
    bwords = [w for w in words if w in BOUNDARY_WORDS_6]
    cyc = [w for w in words if w not in set(bwords)]
    pre = fold_preimages(m)
    V_map = {w: V_word(w) for w in words}
    d_map = {w: len(pre[w]) for w in words}
    hist: Dict[int, int] = {}
    for d in d_map.values():
        hist[int(d)] = hist.get(int(d), 0) + 1
    if hist != {2: 8, 3: 4, 4: 9}:
        raise AssertionError(f"Unexpected window-6 histogram: {hist}")
    sheet_pairs: List[Dict[str, int | str]] = []
    for w in bwords:
        ns = sorted(pre[w])
        if len(ns) != 2:
            raise AssertionError(f"Boundary word {w} is not two-sheeted: {ns}")
        sheet_pairs.append(
            {
                "word": w,
                "lower": int(ns[0]),
                "upper": int(ns[1]),
                "delta": int(ns[1] - ns[0]),
            }
        )
    log_gauge = 39.0 * math.log(2.0) + 13.0 * math.log(3.0)
    g6 = log_gauge / 64.0
    kappa6 = sum(float(d) * math.log(float(d)) * float(count) for d, count in hist.items()) / 64.0
    reps = {
        "cyclic": int(min(pre[cyc[0]])),
        "boundary_lower": int(sheet_pairs[0]["lower"]),
        "boundary_upper": int(sheet_pairs[0]["upper"]),
    }
    return Window6Data(
        m=m,
        words=words,
        cyclic_words=cyc,
        boundary_words=bwords,
        V_map=V_map,
        preimages=pre,
        d_map=d_map,
        histogram=hist,
        sheet_pairs=sheet_pairs,
        log_gauge=log_gauge,
        g6=g6,
        kappa6=kappa6,
        anomaly_rank=21,
        representative_microstates=reps,
    )


def sigma_vector(n: int, data: Window6Data | None = None) -> Tuple[int, int, int]:
    """Boundary sheet indicator in the canonical (Z/2)^3 coordinates.

    Lower sheet -> 0, upper sheet -> basis vector of the corresponding boundary word.
    """
    wd = data if data is not None else window6_data()
    sig = [0, 0, 0]
    for idx, pair in enumerate(wd.sheet_pairs):
        if int(pair["upper"]) == int(n):
            sig[idx] = 1
            break
    return (int(sig[0]), int(sig[1]), int(sig[2]))


def event_stream(n: int, data: Window6Data | None = None) -> List[str]:
    wd = data if data is not None else window6_data()
    bits = micro_bits(n, wd.m)
    stream = ["refine" if ch == "1" else "stay" for ch in bits]
    sig = sigma_vector(n, wd)
    if any(sig):
        idx = sig.index(1)
        stream.append(f"flip_{wd.boundary_words[idx]}")
    stream.append("decode")
    return stream


def ledger_prefix_integers(events: Sequence[str], codes: Mapping[str, int] | None = None) -> List[int]:
    code_map = dict(codes or EVENT_CODES_6)
    ps = first_primes(len(events))
    out: List[int] = []
    current = 1
    for p, evt in zip(ps, events, strict=True):
        current *= p ** int(code_map[evt])
        out.append(int(current))
    return out


def ledger_prefix_addresses(
    events: Sequence[str],
    *,
    base: int = LEDGER_BASE_6,
    codes: Mapping[str, int] | None = None,
) -> List[float]:
    code_map = dict(codes or EVENT_CODES_6)
    out: List[float] = []
    x = 0.0
    scale = 1.0
    for evt in events:
        scale /= float(base)
        x += float(code_map[evt]) * scale
        out.append(float(x))
    return out


def visible_phase(word: str, j: int, data: Window6Data | None = None) -> float:
    wd = data if data is not None else window6_data()
    return 2.0 * math.pi * (((j + 1) * wd.V_map[word]) % len(wd.words)) / float(len(wd.words))


def boundary_phase(sig: Tuple[int, int, int], j: int) -> float:
    weights = (0.125, 0.25, 0.375)
    level = sum(float(s) * w for s, w in zip(sig, weights, strict=True))
    return 2.0 * math.pi * ((j + 1) * level)


def ledger_phase(address: float, j: int) -> float:
    return 2.0 * math.pi * ((j + 1) * float(address))


def trajectory(
    n: int,
    *,
    mode: str,
    J: int,
    a: float,
    t: np.ndarray,
    data: Window6Data | None = None,
) -> np.ndarray:
    wd = data if data is not None else window6_data()
    word = fold_bin_word(int(n), wd.m)
    sig = sigma_vector(int(n), wd)
    events = event_stream(int(n), wd)
    addresses = ledger_prefix_addresses(events)
    y = np.zeros_like(t, dtype=np.float64)
    for j in range(J + 1):
        phi = visible_phase(word, j, wd)
        if mode in {"visible_boundary", "full"}:
            phi += boundary_phase(sig, j)
        if mode == "full":
            phi += ledger_phase(addresses[min(j, len(addresses) - 1)], j)
        y += (float(a) ** float(j)) * np.cos((2.0 * math.pi * (2**j) * t) + phi)
    return y


def trajectory_modes() -> Tuple[str, str, str]:
    return ("visible_only", "visible_boundary", "full")
