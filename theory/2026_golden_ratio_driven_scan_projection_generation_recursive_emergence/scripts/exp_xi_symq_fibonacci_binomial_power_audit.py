#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit Fibonacci closed forms for powers of C^{(q)} and sign-regularity.

This script audits identities stated in:
  sections/body/zeta_finite_part/xi/subsubsec__xi-time-protocol-conclusions-part31h.tex

Definitions:
  C^{(q)}_{i,j} = binom(q-i, j), 0<=i,j<=q.
  Fibonacci: F_0=0, F_1=1, F_{n+1}=F_n+F_{n-1}.

We audit:
- Entrywise closed form for (C^{(q)})^m in terms of Fibonacci numbers
- Boundary entries and row-sum closed form
- Strict sign-regularity signature for minors of (C^{(q)})^m

Outputs:
- artifacts/export/xi_symq_fibonacci_binomial_power_audit.json
"""

from __future__ import annotations

import itertools
import json
from dataclasses import dataclass
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir


def _fib(n: int) -> int:
    if n < 0:
        raise ValueError("fib expects n>=0")
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def _C_q(q: int) -> sp.Matrix:
    M = sp.zeros(q + 1, q + 1)
    for i in range(q + 1):
        for j in range(q + 1):
            # binom(q-i, j) is 0 for j > q-i.
            M[i, j] = sp.binomial(q - i, j) if j <= q - i else sp.Integer(0)
    return M


def _C_power_entry_rhs(q: int, m: int, i: int, j: int) -> int:
    Fm1 = _fib(m - 1)
    Fm = _fib(m)
    Fm1p = _fib(m + 1)
    lo = max(0, i + j - q)
    hi = min(i, j)
    s = 0
    for t in range(lo, hi + 1):
        s += (
            sp.binomial(i, t)
            * sp.binomial(q - i, j - t)
            * (Fm1p ** (q - i - j + t))
            * (Fm ** (i + j - 2 * t))
            * (Fm1 ** t)
        )
    return int(s)


def _signature(m: int, k: int) -> int:
    # (-1)^{m * binom(k,2)}
    return -1 if ((m * (k * (k - 1) // 2)) % 2 == 1) else 1


@dataclass(frozen=True)
class EntryCheck:
    q: int
    m: int
    ok_entries: bool
    ok_boundary_and_row_sum: bool


@dataclass(frozen=True)
class MinorCheck:
    q: int
    m: int
    ok_signature: bool
    total_minors_checked: int
    nonzero_minors_checked: int


def _check_entries(q: int, m: int) -> Tuple[bool, bool]:
    C = _C_q(q)
    Cm = C**m

    ok_entries = True
    for i in range(q + 1):
        for j in range(q + 1):
            rhs = _C_power_entry_rhs(q, m, i, j)
            if int(Cm[i, j]) != rhs:
                ok_entries = False
                break
        if not ok_entries:
            break

    ok_boundary = True
    Fm1 = _fib(m - 1)
    Fm = _fib(m)
    Fm1p = _fib(m + 1)
    Fm2p = _fib(m + 2)
    for j in range(q + 1):
        expected = int(sp.binomial(q, j) * (Fm1p ** (q - j)) * (Fm**j))
        if int(Cm[0, j]) != expected:
            ok_boundary = False
            break
    if ok_boundary:
        for i in range(q + 1):
            if int(Cm[i, 0]) != int((Fm1p ** (q - i)) * (Fm**i)):
                ok_boundary = False
                break
            if int(Cm[i, q]) != int((Fm ** (q - i)) * (Fm1**i)):
                ok_boundary = False
                break
            expected_row_sum = int((Fm2p ** (q - i)) * (Fm1p**i))
            if int(sum(Cm[i, j] for j in range(q + 1))) != expected_row_sum:
                ok_boundary = False
                break

    return ok_entries, ok_boundary


def _check_minors(q: int, m: int) -> MinorCheck:
    C = _C_q(q)
    Cm = C**m
    n = q + 1

    total = 0
    nonzero = 0
    ok = True

    for k in range(1, n + 1):
        sig = _signature(m, k)
        row_subsets = list(itertools.combinations(range(n), k))
        col_subsets = list(itertools.combinations(range(n), k))
        for I in row_subsets:
            for J in col_subsets:
                total += 1
                sub = Cm.extract(I, J)
                det = sp.Integer(sub.det())
                if det == 0:
                    continue
                nonzero += 1
                if det > 0 and sig != 1:
                    ok = False
                    break
                if det < 0 and sig != -1:
                    ok = False
                    break
            if not ok:
                break
        if not ok:
            break

    return MinorCheck(
        q=q,
        m=m,
        ok_signature=ok,
        total_minors_checked=total,
        nonzero_minors_checked=nonzero,
    )


def main() -> None:
    entry_q_max = 8
    entry_m_max = 8

    minor_q_max = 6
    minor_m_max = 4

    entry_results: List[EntryCheck] = []
    for q in range(0, entry_q_max + 1):
        for m in range(1, entry_m_max + 1):
            ok_entries, ok_boundary = _check_entries(q, m)
            entry_results.append(
                EntryCheck(q=q, m=m, ok_entries=ok_entries, ok_boundary_and_row_sum=ok_boundary)
            )

    minor_results: List[MinorCheck] = []
    for q in range(0, minor_q_max + 1):
        for m in range(1, minor_m_max + 1):
            minor_results.append(_check_minors(q, m))

    assert all(r.ok_entries for r in entry_results), "Entrywise Fibonacci/binomial audit failed"
    assert all(
        r.ok_boundary_and_row_sum for r in entry_results
    ), "Boundary/row-sum Fibonacci audit failed"
    assert all(r.ok_signature for r in minor_results), "Sign-regularity audit failed"

    out: Dict[str, object] = {
        "entry_tests": {
            "q_range": [0, entry_q_max],
            "m_range": [1, entry_m_max],
            "results": [
                {
                    "q": r.q,
                    "m": r.m,
                    "ok_entries": r.ok_entries,
                    "ok_boundary_and_row_sum": r.ok_boundary_and_row_sum,
                }
                for r in entry_results
            ],
        },
        "minor_tests": {
            "q_range": [0, minor_q_max],
            "m_range": [1, minor_m_max],
            "results": [
                {
                    "q": r.q,
                    "m": r.m,
                    "ok_signature": r.ok_signature,
                    "total_minors_checked": r.total_minors_checked,
                    "nonzero_minors_checked": r.nonzero_minors_checked,
                }
                for r in minor_results
            ],
        },
    }

    p = export_dir() / "xi_symq_fibonacci_binomial_power_audit.json"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[ok] wrote {p.relative_to(export_dir().parent)}", flush=True)


if __name__ == "__main__":
    main()

