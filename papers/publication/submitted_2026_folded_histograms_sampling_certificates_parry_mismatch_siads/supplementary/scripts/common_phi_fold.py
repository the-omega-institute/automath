#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Golden-mean folding and Parry/PF baseline utilities.

All code is English-only by repository convention.
"""

from __future__ import annotations

import math
import time
from dataclasses import dataclass
from typing import Dict, Iterable, Iterator, List, Sequence, Tuple


PHI = (1.0 + 5.0 ** 0.5) / 2.0


def fib_upto(n: int) -> List[int]:
    """Return Fibonacci numbers F_1..F_n with F_1=F_2=1."""
    if n <= 0:
        return []
    if n == 1:
        return [1]
    f = [1, 1]
    while len(f) < n:
        f.append(f[-1] + f[-2])
    return f


def zeckendorf_digits(N: int, m: int) -> List[int]:
    """Zeckendorf digits (c_1..c_m) for weights F_{k+1}, k=1..m.

    Greedy: pick largest Fibonacci weight <= remaining, skip adjacent.
    """
    if N < 0:
        raise ValueError("N must be non-negative")
    if m <= 0:
        return []

    # Need weights up to F_{m+2} (since weight at position k is F_{k+1}).
    fib = fib_upto(m + 2)
    # Map position k -> weight F_{k+1} = fib[k] with 0-based indexing.
    digits = [0] * m

    remaining = N
    k = m
    while remaining > 0 and k >= 1:
        w = fib[k]  # F_{k+1}
        if w <= remaining:
            digits[k - 1] = 1
            remaining -= w
            k -= 2  # skip adjacent position
        else:
            k -= 1

    return digits


def fold_m(micro: Sequence[int]) -> List[int]:
    """Fold a length-m microstate (0/1) to a golden-mean legal word (no '11').

    IMPORTANT:
    - In the paper, a length-m micro word can carry *one* hidden overflow bit b in
      the next Fibonacci weight F_{m+2}. The canonical statement is:
        N(micro) = V_m(Fold_m(micro)) + b * F_{m+2},  b in {0,1}.
    - Therefore, to compute Fold_m correctly, we compute the Zeckendorf canonical
      digits up to length (m+1) and then drop the overflow digit.
    """
    m = len(micro)
    if m == 0:
        return []
    fib = fib_upto(m + 2)
    N = 0
    for k, b in enumerate(micro, start=1):
        if b:
            N += fib[k]  # F_{k+1}
    # Compute one extra digit to allow the overflow bit at weight F_{m+2},
    # then drop it to obtain the length-m stable type.
    digits = zeckendorf_digits(N, m + 1)
    return digits[:m]


def is_golden_legal(word: Sequence[int]) -> bool:
    for i in range(len(word) - 1):
        if word[i] == 1 and word[i + 1] == 1:
            return False
    return True


def word_to_str(word: Sequence[int]) -> str:
    return "".join("1" if b else "0" for b in word)


def parry_params() -> Tuple[float, float, float, float, float]:
    """Return (phi, pi0, pi1, p00, p01) for the golden mean Parry measure."""
    phi = PHI
    pi1 = 1.0 / (phi * phi + 1.0)
    pi0 = 1.0 - pi1
    p00 = 1.0 / phi
    p01 = 1.0 / (phi * phi)
    # p10 = 1, p11 = 0 implied
    return phi, pi0, pi1, p00, p01


def parry_pi_m(word: Sequence[int]) -> float:
    """Parry maximal entropy cylinder probability for a 0/1 golden-legal word."""
    if not word:
        return 1.0
    if not is_golden_legal(word):
        return 0.0
    _, pi0, pi1, p00, p01 = parry_params()
    p = pi1 if word[0] == 1 else pi0
    for a, b in zip(word, word[1:]):
        if a == 0 and b == 0:
            p *= p00
        elif a == 0 and b == 1:
            p *= p01
        elif a == 1 and b == 0:
            p *= 1.0
        else:
            return 0.0
    return p


def tv_distance(p: Dict[str, float], q: Dict[str, float]) -> float:
    keys = set(p.keys()) | set(q.keys())
    s = 0.0
    for k in keys:
        s += abs(p.get(k, 0.0) - q.get(k, 0.0))
    return 0.5 * s


def kl_divergence(p: Dict[str, float], q: Dict[str, float], eps: float = 1e-300) -> float:
    """Compute KL(p||q) with a tiny floor on q to avoid log(0) explosions."""
    s = 0.0
    for k, pk in p.items():
        if pk <= 0.0:
            continue
        qk = q.get(k, 0.0)
        qk = qk if qk > 0.0 else eps
        s += pk * math.log(pk / qk)
    return s


@dataclass
class Progress:
    label: str
    every_seconds: float = 20.0
    _t0: float = time.time()
    _last: float = 0.0

    def tick(self, msg: str) -> None:
        now = time.time()
        if self._last == 0.0:
            self._last = now
        if now - self._last >= self.every_seconds:
            dt = now - self._t0
            print(f"[{self.label}] t={dt:.1f}s {msg}", flush=True)
            self._last = now

