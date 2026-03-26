#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit: reciprocal-moment Fibonacci/partition formulas for exceptional block.

This script is English-only by repository convention.

We verify formulas integrated in:
  sections/body/zeta_finite_part/xi/subsubsec__xi-time-protocol-conclusions-part31u.tex

Checks:
- corner rigidity: (2*C^{-1})^m_{0,0} = 2^m (-1)^{mq} F_{m-1}^q
- reciprocal partition expansion for S_{-m}(q)=Tr((A^(q))^{-m})
- closed forms for S_{-3},...,S_{-6}
- q-direction recurrence annihilator for fixed m
- entrywise convolution closed form for (C^(q))^{-m}_{i,j}

Output:
- artifacts/export/xi_exceptional_reciprocal_fibonacci_partition_audit.json
"""

from __future__ import annotations

import json
import time
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import sympy as sp

from common_paths import export_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


@dataclass(frozen=True)
class Check:
    name: str
    ok: bool
    details: str = ""


def _fib_ext(n: int) -> sp.Integer:
    if n == -1:
        return sp.Integer(1)
    return sp.Integer(sp.fibonacci(n))


def _C(q: int) -> sp.Matrix:
    return sp.Matrix([[sp.binomial(q - i, j) for j in range(q + 1)] for i in range(q + 1)])


def _A(q: int, Cq: sp.Matrix | None = None) -> sp.Matrix:
    Cq = Cq if Cq is not None else _C(q)
    b = sp.Matrix([sp.binomial(q, j) for j in range(q + 1)])
    ones = sp.Matrix([1] * (q + 1))
    return sp.Rational(1, 2) * (ones * b.T + Cq)


def _partitions(n: int, max_part: int | None = None) -> Iterable[List[int]]:
    if max_part is None or max_part > n:
        max_part = n
    if n == 0:
        yield []
        return
    if max_part <= 0:
        return
    for k in range(max_part, 0, -1):
        if k > n:
            continue
        for tail in _partitions(n - k, min(k, n - k)):
            yield [k] + tail


def _partition_counters(m: int) -> List[Counter[int]]:
    out: List[Counter[int]] = []
    for parts in _partitions(m):
        if parts:
            out.append(Counter(parts))
    return out


def _ell(cnt: Counter[int]) -> int:
    return sum(cnt.values())


def _c_pi(cnt: Counter[int], m: int) -> sp.Rational:
    ell = _ell(cnt)
    num = sp.Integer(m) * sp.factorial(ell)
    den = sp.Integer(ell)
    for v in cnt.values():
        den *= sp.factorial(v)
    return sp.Rational(num, den)


def _psi_pi(cnt: Counter[int]) -> sp.Integer:
    val = sp.Integer(1)
    for s_part, mult in cnt.items():
        val *= _fib_ext(s_part - 2) ** mult
    return sp.Integer(val)


def _alpha_pi(cnt: Counter[int], m: int) -> sp.Integer:
    return sp.Integer(((-1) ** (m - _ell(cnt))) * _psi_pi(cnt))


def _check_corner_formula() -> Check:
    fails: List[Tuple[int, int]] = []
    for q in range(2, 15):
        Cq = _C(q)
        U = 2 * Cq.inv()
        for m in range(0, 11):
            lhs = sp.simplify((U**m)[0, 0])
            rhs = sp.simplify((2**m) * ((-1) ** (m * q)) * (_fib_ext(m - 1) ** q))
            if sp.simplify(lhs - rhs) != 0:
                fails.append((q, m))
    return Check(
        name="corner_fibonacci_power_law",
        ok=(len(fails) == 0),
        details="" if len(fails) == 0 else f"failed={fails[:8]}",
    )


def _check_partition_expansion() -> Check:
    fails: List[Tuple[int, int]] = []
    for q in range(2, 11):
        Cq = _C(q)
        Cqi = Cq.inv()
        Aq = _A(q, Cq=Cq)
        Aqi = Aq.inv()
        for m in range(1, 8):
            lhs = sp.simplify(sp.trace(Aqi**m))
            rhs = sp.simplify((2**m) * sp.trace(Cqi**m))
            for cnt in _partition_counters(m):
                ell = _ell(cnt)
                cpi = _c_pi(cnt, m)
                psi = _psi_pi(cnt)
                rhs += sp.simplify(((-1) ** (ell + q * (m - ell))) * cpi * (2 ** (m - ell)) * (psi**q))
            if sp.simplify(lhs - rhs) != 0:
                fails.append((q, m))
    return Check(
        name="reciprocal_partition_expansion",
        ok=(len(fails) == 0),
        details="" if len(fails) == 0 else f"failed={fails[:8]}",
    )


def _check_m3_m6_closed_forms() -> Check:
    fails: List[Tuple[int, int]] = []
    for q in range(2, 13):
        Cq = _C(q)
        Cqi = Cq.inv()
        Aq = _A(q, Cq=Cq)
        Aqi = Aq.inv()
        omega = {m: sp.simplify(sp.trace(Cqi**m)) for m in (3, 4, 5, 6)}
        formulas = {
            3: sp.simplify(8 * omega[3] - 13),
            4: sp.simplify(16 * omega[4] - 32 * ((-1) ** q) + 17),
            5: sp.simplify(32 * omega[5] - 80 * (2**q) + 40 * ((-1) ** q) - 21),
            6: sp.simplify(64 * omega[6] + 96 * (2**q) - 192 * ((-1) ** q) * (3**q) - 48 * ((-1) ** q) + 73),
        }
        for m in (3, 4, 5, 6):
            lhs = sp.simplify(sp.trace(Aqi**m))
            if sp.simplify(lhs - formulas[m]) != 0:
                fails.append((q, m))
    return Check(
        name="reciprocal_m3_m6_closed_forms",
        ok=(len(fails) == 0),
        details="" if len(fails) == 0 else f"failed={fails[:8]}",
    )


def _annihilates(coeffs: Sequence[sp.Expr], seq: Sequence[sp.Expr]) -> bool:
    d = len(coeffs) - 1
    for n in range(0, len(seq) - d):
        residue = sp.Integer(0)
        for j, cj in enumerate(coeffs):
            residue += cj * seq[n + d - j]
        if sp.simplify(residue) != 0:
            return False
    return True


def _check_q_recurrence_factor() -> Check:
    fails: List[int] = []
    for m in range(1, 8):
        # Distinct signed bases from partition channel.
        alphas: set[sp.Integer] = set()
        coeff_by_alpha: Dict[sp.Integer, sp.Expr] = defaultdict(lambda: sp.Integer(0))
        for cnt in _partition_counters(m):
            psi = _psi_pi(cnt)
            if psi == 0:
                continue
            ell = _ell(cnt)
            alpha = _alpha_pi(cnt, m)
            alphas.add(alpha)
            coeff_by_alpha[alpha] += sp.simplify(((-1) ** ell) * _c_pi(cnt, m) * (2 ** (m - ell)))

        # Remove channels with zero aggregated coefficient.
        active_alphas = sorted([a for a in alphas if sp.simplify(coeff_by_alpha[a]) != 0], key=lambda x: int(x))

        x = sp.Symbol("x")
        poly = sp.expand(x**2 - ((-1) ** m) * sp.lucas(m) * x + ((-1) ** m))
        for a in active_alphas:
            poly = sp.expand(poly * (x - a))
        coeffs = sp.Poly(poly, x).all_coeffs()
        deg = len(coeffs) - 1

        q_max = 2 + deg + 12
        seq: List[sp.Expr] = []
        for q in range(2, q_max + 1):
            seq.append(sp.simplify(sp.trace((_A(q).inv()) ** m)))

        if not _annihilates(coeffs, seq):
            fails.append(m)

    return Check(
        name="q_recurrence_annihilator",
        ok=(len(fails) == 0),
        details="" if len(fails) == 0 else f"failed_m={fails}",
    )


def _entry_formula_rhs(q: int, m: int, i: int, j: int) -> sp.Expr:
    lo = max(0, i + j - q)
    hi = min(i, j)
    val = sp.Integer(0)
    for t in range(lo, hi + 1):
        val += (
            sp.binomial(i, t)
            * sp.binomial(q - i, j - t)
            * (_fib_ext(m - 1) ** (q - i - j + t))
            * (_fib_ext(m) ** (i + j - 2 * t))
            * (_fib_ext(m + 1) ** t)
        )
    return sp.simplify(((-1) ** (m * q + i + j)) * val)


def _check_entrywise_convolution() -> Check:
    fails: List[Tuple[int, int, int, int]] = []
    for q in range(2, 9):
        Cq = _C(q)
        Cqi = Cq.inv()
        powers = {m: (sp.eye(q + 1) if m == 0 else Cqi**m) for m in range(0, 7)}
        for m in range(0, 7):
            M = powers[m]
            for i in range(q + 1):
                for j in range(q + 1):
                    rhs = _entry_formula_rhs(q, m, i, j)
                    if sp.simplify(M[i, j] - rhs) != 0:
                        fails.append((q, m, i, j))
    return Check(
        name="entrywise_inverse_power_convolution",
        ok=(len(fails) == 0),
        details="" if len(fails) == 0 else f"failed={fails[:8]}",
    )


def main() -> None:
    t0 = time.time()

    checks = [
        _check_corner_formula(),
        _check_partition_expansion(),
        _check_m3_m6_closed_forms(),
        _check_q_recurrence_factor(),
        _check_entrywise_convolution(),
    ]

    out = {
        "checks": [{"name": c.name, "ok": c.ok, "details": c.details} for c in checks],
        "elapsed_s": time.time() - t0,
    }

    out_path = export_dir() / "xi_exceptional_reciprocal_fibonacci_partition_audit.json"
    _write_text(out_path, json.dumps(out, indent=2, sort_keys=True) + "\n")

    failed = [c for c in checks if not c.ok]
    if failed:
        print(f"[xi_exceptional_reciprocal_fibonacci_partition_audit] FAIL: {len(failed)} checks failed")
        for c in failed:
            print(f"  - {c.name}: {c.details}")
    else:
        print("[xi_exceptional_reciprocal_fibonacci_partition_audit] OK")


if __name__ == "__main__":
    main()

