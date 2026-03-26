#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the weighted hypercube Dirichlet energy spectral identity (Walsh diagonalization).

This script is English-only by repository convention.

We verify, for functions f: {0,1}^n -> Q (tested on random integer samples),
the exact identity

  E_w(f) := (1/2) * sum_{ω} sum_i w_i |f(ω^i)-f(ω)|^2
         = 2^{n+1} * sum_{I != empty} (sum_{i in I} w_i) * |fhat(I)|^2,

where fhat(I) are normalized Walsh coefficients:
  fhat(I) = 2^{-n} * sum_{ω} f(ω) χ_I(ω),  χ_I(ω)=(-1)^{<I,ω>}.

We also verify the tail bound
  sum_{I: sum_{i in I} w_i >= τ} |fhat(I)|^2 <= E_w(f) / (2^{n+1} τ)
for several τ.

Outputs:
  - artifacts/export/fold_hypercube_weighted_energy_spectrum_audit.json
"""

from __future__ import annotations

import json
import random
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir


def _popcount(x: int) -> int:
    return x.bit_count()


def _chi(mask: int, omega: int) -> int:
    return -1 if (_popcount(mask & omega) % 2 == 1) else 1


def _walsh_coeffs(f: List[Fraction]) -> List[Fraction]:
    n = (len(f)).bit_length() - 1
    N = 1 << n
    coeffs: List[Fraction] = [Fraction(0, 1) for _ in range(N)]
    invN = Fraction(1, N)
    for mask in range(N):
        s = 0
        for omega in range(N):
            s += int(f[omega]) * _chi(mask, omega)
        coeffs[mask] = invN * Fraction(s, 1)
    return coeffs


def _lambda_w(mask: int, w: List[int]) -> int:
    lam = 0
    i = 0
    mm = mask
    while mm:
        if mm & 1:
            lam += w[i]
        mm >>= 1
        i += 1
    return lam


def _energy_unnormalized(f: List[Fraction], w: List[int]) -> Fraction:
    n = (len(f)).bit_length() - 1
    N = 1 << n
    tot = 0
    for omega in range(N):
        for i in range(n):
            omega_i = omega ^ (1 << i)
            diff = f[omega_i] - f[omega]
            tot += w[i] * (diff * diff)
    # Each undirected edge counted twice.
    return Fraction(tot, 2)


@dataclass(frozen=True)
class CaseResult:
    n: int
    w: List[int]
    f_values: List[int]
    energy: str
    spectral: str
    ok_energy_identity: bool
    tau_checks: List[Dict[str, object]]


def _as_str(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def _run_case(n: int, *, rng: random.Random) -> CaseResult:
    N = 1 << n
    w = [rng.randint(1, 7) for _ in range(n)]
    f_int = [rng.randint(-3, 3) for _ in range(N)]
    f = [Fraction(v, 1) for v in f_int]

    energy = _energy_unnormalized(f, w)
    coeffs = _walsh_coeffs(f)

    spectral = Fraction(0, 1)
    for mask in range(1, 1 << n):
        lam = _lambda_w(mask, w)
        spectral += Fraction(lam, 1) * (coeffs[mask] * coeffs[mask])
    spectral *= Fraction(1 << (n + 1), 1)

    tau_checks: List[Dict[str, object]] = []
    for tau in sorted(set([1, 2, 3, 4, 5, sum(w) // 2 + 1, sum(w)])):
        tail = Fraction(0, 1)
        for mask in range(1, 1 << n):
            if _lambda_w(mask, w) >= tau:
                tail += coeffs[mask] * coeffs[mask]
        rhs = energy / (Fraction(1 << (n + 1), 1) * Fraction(tau, 1))
        tau_checks.append(
            {
                "tau": int(tau),
                "tail_sum": _as_str(tail),
                "rhs": _as_str(rhs),
                "ok": bool(tail <= rhs),
            }
        )

    return CaseResult(
        n=n,
        w=w,
        f_values=f_int,
        energy=_as_str(energy),
        spectral=_as_str(spectral),
        ok_energy_identity=bool(energy == spectral),
        tau_checks=tau_checks,
    )


def main() -> None:
    rng = random.Random(1337)
    cases: List[CaseResult] = []
    for n in [1, 2, 3, 4, 5, 6]:
        for _ in range(5):
            cases.append(_run_case(n, rng=rng))

    assert all(c.ok_energy_identity for c in cases)
    assert all(all(t["ok"] for t in c.tau_checks) for c in cases)

    payload: Dict[str, object] = {
        "cases": [asdict(c) for c in cases],
        "n_cases": len(cases),
    }

    out = export_dir() / "fold_hypercube_weighted_energy_spectrum_audit.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("[fold-hypercube-weighted-energy-spectrum] ok", flush=True)


if __name__ == "__main__":
    main()

