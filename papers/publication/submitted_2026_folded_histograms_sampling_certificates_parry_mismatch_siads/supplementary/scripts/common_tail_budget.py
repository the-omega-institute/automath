#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Tail-budget certificate utilities (paper-local, small and auditable).

We provide a compact implementation of the optimized Chernoff tail budget:

  gamma_cert_m(eps) := inf_{q>=2} ( log r_q - log |A_out| + (1/m) log(1/eps) ) / (q-1)

and an exact finite-m variant using log S_q(m) in place of log r_q.

All output is English-only by repository convention.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Dict, Iterable, Iterator, List, Mapping, Tuple


@dataclass(frozen=True)
class GammaCert:
    gamma: float
    q_star: int
    gamma_by_q: Dict[int, float]


def gamma_cert_from_rq(
    *,
    m: int,
    eps: float,
    rq_by_q: Mapping[int, float],
    out_alphabet_size: int = 2,
) -> GammaCert:
    """Compute gamma_cert using Perron roots r_q (asymptotic certificate)."""
    if m <= 0:
        raise ValueError("m must be positive")
    if not (0.0 < eps < 1.0):
        raise ValueError("eps must be in (0,1)")
    if out_alphabet_size <= 1:
        raise ValueError("out_alphabet_size must be >= 2")
    if not rq_by_q:
        raise ValueError("rq_by_q must be non-empty")

    logA = math.log(float(out_alphabet_size))
    log1eps_over_m = math.log(1.0 / float(eps)) / float(m)
    gamma_by_q: Dict[int, float] = {}
    best = float("inf")
    q_star = -1

    for q, rq in sorted(rq_by_q.items(), key=lambda t: int(t[0])):
        q = int(q)
        rq = float(rq)
        if q < 2:
            continue
        if not (rq > 0.0) or (not math.isfinite(rq)):
            continue
        gq = (math.log(rq) - logA + log1eps_over_m) / float(q - 1)
        gamma_by_q[q] = float(gq)
        if gq < best:
            best = float(gq)
            q_star = int(q)

    if q_star < 0 or not math.isfinite(best):
        raise ValueError("No valid q/r_q pairs for gamma_cert")
    return GammaCert(gamma=float(best), q_star=int(q_star), gamma_by_q=gamma_by_q)


def gamma_cert_from_logSq(
    *,
    m: int,
    eps: float,
    logSq_by_q: Mapping[int, float],
    out_alphabet_size: int = 2,
) -> GammaCert:
    """Compute gamma_cert using finite-m log S_q(m) (exact certificate for that m)."""
    if m <= 0:
        raise ValueError("m must be positive")
    if not (0.0 < eps < 1.0):
        raise ValueError("eps must be in (0,1)")
    if out_alphabet_size <= 1:
        raise ValueError("out_alphabet_size must be >= 2")
    if not logSq_by_q:
        raise ValueError("logSq_by_q must be non-empty")

    logA = math.log(float(out_alphabet_size))
    log1eps = math.log(1.0 / float(eps))
    gamma_by_q: Dict[int, float] = {}
    best = float("inf")
    q_star = -1

    for q, logSq in sorted(logSq_by_q.items(), key=lambda t: int(t[0])):
        q = int(q)
        logSq = float(logSq)
        if q < 2:
            continue
        if not math.isfinite(logSq):
            continue
        gq = ((logSq / float(m)) - logA + (log1eps / float(m))) / float(q - 1)
        gamma_by_q[q] = float(gq)
        if gq < best:
            best = float(gq)
            q_star = int(q)

    if q_star < 0 or not math.isfinite(best):
        raise ValueError("No valid q/logS_q pairs for gamma_cert")
    return GammaCert(gamma=float(best), q_star=int(q_star), gamma_by_q=gamma_by_q)


def logB_from_gamma(*, m: int, gamma: float) -> float:
    return float(m) * float(gamma)


def B_from_logB(logB: float) -> float | None:
    """Return exp(logB) if it fits safely in float; else None."""
    if logB > 700.0:  # exp(709) ~ 8e307 near float overflow
        return None
    return float(math.exp(float(logB)))


def iter_primes() -> Iterator[int]:
    """Deterministic, dependency-free prime generator (trial division)."""
    yield 2
    primes: List[int] = [2]
    n = 3
    while True:
        is_p = True
        r = int(math.isqrt(n))
        for p in primes:
            if p > r:
                break
            if (n % p) == 0:
                is_p = False
                break
        if is_p:
            primes.append(n)
            yield n
        n += 2


def prime_list_for_log_target(log_target: float) -> Tuple[List[int], float]:
    """Return primes whose product exceeds exp(log_target), in log space."""
    if not math.isfinite(log_target):
        raise ValueError("log_target must be finite")
    if log_target <= 0.0:
        return ([], 0.0)
    logp = 0.0
    out: List[int] = []
    for p in iter_primes():
        out.append(int(p))
        logp += math.log(float(p))
        if logp > float(log_target):
            return out, float(logp)
    raise RuntimeError("unreachable")


def prime_list_for_int_target(target: int) -> Tuple[List[int], int]:
    """Return primes whose product exceeds `target` (uses big integers)."""
    if target <= 1:
        return ([], 1)
    prod = 1
    out: List[int] = []
    for p in iter_primes():
        out.append(int(p))
        prod *= int(p)
        if prod > target:
            return out, int(prod)
    raise RuntimeError("unreachable")

