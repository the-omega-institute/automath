#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Ostrowski numeration utilities (general continued fractions).

This module generalizes the Fibonacci/Zeckendorf folding utilities by working
with a finite prefix of continued-fraction partial quotients a_1..a_m.

Conventions (matching the paper's Appendix H and Section 6):
- alpha = [0; a_1, a_2, ...], with a_k >= 1 integers.
- Denominators: q_{-1}=0, q_0=1, q_{n+1}=a_{n+1} q_n + q_{n-1}.
- Ostrowski digits (d_1..d_m) satisfy 0 <= d_n <= a_n and
  if d_n == a_n then d_{n-1} == 0 (for n >= 2).
"""

from __future__ import annotations

from typing import List, Sequence, Tuple


def denominators_from_partial_quotients(a: Sequence[int]) -> List[int]:
    """Return denominators q_0..q_m for partial quotients a_1..a_m.

    Args:
        a: a_1..a_m (length m), each >= 1.
    """
    if any(x < 1 for x in a):
        raise ValueError("All partial quotients must be >= 1")

    # q_{-1}=0, q_0=1
    q_minus_1 = 0
    q_0 = 1
    qs = [q_0]
    q_prev, q_curr = q_minus_1, q_0
    for ak in a:
        q_next = ak * q_curr + q_prev
        qs.append(q_next)
        q_prev, q_curr = q_curr, q_next
    return qs  # length m+1: q_0..q_m


def is_ostrowski_legal(digits: Sequence[int], a: Sequence[int]) -> bool:
    """Check Ostrowski legality for a finite digit block d_1..d_m."""
    if len(digits) != len(a):
        return False
    m = len(a)
    if any(d < 0 or d > a[i] for i, d in enumerate(digits)):
        return False
    for n in range(2, m + 1):
        if digits[n - 1] == a[n - 1] and digits[n - 2] != 0:
            return False
    return True


def ostrowski_digits(N: int, a: Sequence[int]) -> List[int]:
    """Compute the Ostrowski digits d_1..d_m for a given N and a_1..a_m.

    This is a greedy implementation for a finite prefix. It is intended for
    constructing canonical digits used by the paper's Fold_m^(alpha) definition.
    """
    if N < 0:
        raise ValueError("N must be non-negative")
    if any(x < 1 for x in a):
        raise ValueError("All partial quotients must be >= 1")

    m = len(a)
    if m == 0:
        return []

    qs = denominators_from_partial_quotients(a)  # q_0..q_m
    # weights are q_{n-1}, n=1..m
    out = [0] * m
    remaining = N
    force_zero_next = False

    for n in range(m, 0, -1):
        if force_zero_next:
            out[n - 1] = 0
            force_zero_next = False
            continue

        w = qs[n - 1]  # q_{n-1}
        dn = remaining // w
        if dn > a[n - 1]:
            dn = a[n - 1]
        out[n - 1] = int(dn)
        remaining -= int(dn) * w

        if dn == a[n - 1] and n >= 2:
            # Enforce d_{n-1} = 0
            force_zero_next = True

    return out


def fold_ostrowski(micro_digits: Sequence[int], a: Sequence[int]) -> List[int]:
    """Fold a length-m digit block to an Ostrowski-legal block.

    Args:
        micro_digits: length m, digits in 0..a_n (not necessarily legal).
        a: a_1..a_m (length m), partial quotients (bounds).
    """
    if len(micro_digits) != len(a):
        raise ValueError("micro_digits and a must have the same length")
    if any(x < 1 for x in a):
        raise ValueError("All partial quotients must be >= 1")

    qs = denominators_from_partial_quotients(a)
    N = 0
    for n, dn in enumerate(micro_digits, start=1):
        if dn < 0 or dn > a[n - 1]:
            raise ValueError("micro digit out of allowed range 0..a_n")
        N += int(dn) * qs[n - 1]  # q_{n-1}

    out = ostrowski_digits(N, a)
    # Defensive check: legality should hold.
    if not is_ostrowski_legal(out, a):
        raise RuntimeError("ostrowski_digits produced an illegal digit block")
    return out


def value_from_digits(digits: Sequence[int], a: Sequence[int]) -> int:
    """Compute N = sum_{n=1}^m d_n q_{n-1} for given digits."""
    if len(digits) != len(a):
        raise ValueError("digits and a must have the same length")
    qs = denominators_from_partial_quotients(a)
    N = 0
    for n, dn in enumerate(digits, start=1):
        N += int(dn) * qs[n - 1]
    return N


def metallic_alpha(A: int) -> float:
    """Return alpha = [0; A, A, A, ...] as a float."""
    if A < 1:
        raise ValueError("A must be >= 1")
    # alpha satisfies alpha = 1/(A + alpha)
    # => alpha^2 + A alpha - 1 = 0, pick positive root.
    return (-A + (A * A + 4) ** 0.5) / 2.0

