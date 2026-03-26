#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit: Fibonacci moment collapse and Hankel/Vandermonde product identities.

This script is English-only by repository convention.

We audit the closed-form identities added in:
  sections/body/pom/parts/subsubsec__pom-replica-softcore-fibonacci-moment-collapse.tex

Checks (exact / high precision):
- moment collapse: sum_i w_i d_i^m = 2^{-m} F_{m+3}^q
- Hankel determinant product formula for det(F_{i+j+3}^q)_{0..q}
- Vandermonde square collapse for xi_i = (-1)^i phi^{q-2i}
- Perron fixed point equation (numerical, via Perron root of A^{(q)})

Outputs:
- artifacts/export/pom_replica_softcore_fibonacci_moment_collapse_audit.json
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _fib(n: int) -> int:
    # F_0=0, F_1=1
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def _bareiss_det_int(mat: List[List[int]]) -> int:
    """Exact determinant via fraction-free Bareiss algorithm."""
    n = len(mat)
    if n == 0:
        return 1
    a = [row[:] for row in mat]
    det_sign = 1
    prev = 1
    for k in range(n - 1):
        # Pivoting (very small n; simple swap).
        if a[k][k] == 0:
            pivot = None
            for i in range(k + 1, n):
                if a[i][k] != 0:
                    pivot = i
                    break
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            det_sign *= -1
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = (a[i][j] * pivot - a[i][k] * a[k][j]) // prev
        for i in range(k + 1, n):
            a[i][k] = 0
        prev = pivot
    return det_sign * a[n - 1][n - 1]


def _hankel_det_fibpower(q: int) -> int:
    # H_q = (F_{i+j+3}^q)_{0<=i,j<=q}
    H: List[List[int]] = [[_fib(i + j + 3) ** q for j in range(q + 1)] for i in range(q + 1)]
    return _bareiss_det_int(H)


def _hankel_det_closed_form(q: int) -> int:
    prod_binom = 1
    for i in range(q + 1):
        prod_binom *= math.comb(q, i)
    prod_fib = 1
    for k in range(1, q + 1):
        prod_fib *= _fib(k) ** (2 * (q + 1 - k))
    return prod_binom * prod_fib


def _moment_collapse_ok(q: int, m_max: int) -> Tuple[bool, str]:
    sqrt5 = sp.sqrt(5)
    phi = (1 + sqrt5) / 2
    psi = (1 - sqrt5) / 2
    alpha = 1 + 2 / sqrt5
    beta = 1 - 2 / sqrt5

    for m in range(m_max + 1):
        lhs = sp.Integer(0)
        for i in range(q + 1):
            di = sp.Rational(1, 2) * (phi ** (q - i)) * (psi ** i)
            wi = sp.binomial(q, i) * (alpha ** (q - i)) * (beta ** i)
            lhs += wi * (di ** m)
        rhs = sp.Rational(1, 2) ** m * (sp.Integer(_fib(m + 3)) ** q)
        if sp.simplify(lhs - rhs) != 0:
            return False, f"moment_collapse_failed(q={q},m={m})"
    return True, "ok"


def _vandermonde_square_ok(q: int) -> Tuple[bool, str]:
    sqrt5 = sp.sqrt(5)
    phi = (1 + sqrt5) / 2
    xis = [(-1) ** i * (phi ** (q - 2 * i)) for i in range(q + 1)]
    lhs = sp.Integer(1)
    for i in range(q + 1):
        for j in range(i + 1, q + 1):
            lhs *= (xis[j] - xis[i]) ** 2
    rhs = sp.Integer(5) ** (q * (q + 1) // 2)
    for k in range(1, q + 1):
        rhs *= sp.Integer(_fib(k)) ** (2 * (q + 1 - k))
    if sp.simplify(lhs - rhs) != 0:
        return False, f"vandermonde_square_failed(q={q})"
    # also ensure integer
    if sp.simplify(lhs - sp.Integer(int(lhs))) != 0:
        return False, f"vandermonde_square_not_integer(q={q})"
    return True, "ok"


def _A_q_matrix(q: int) -> sp.Matrix:
    # A^{(q)}_{k,l} = 1/2 (C(q,l) + C(q-k,l))
    A = sp.zeros(q + 1, q + 1)
    for k in range(q + 1):
        for l in range(q + 1):
            A[k, l] = sp.Rational(1, 2) * (sp.binomial(q, l) + sp.binomial(q - k, l))
    return A


def _perron_root_numeric(q: int, iters: int = 5000) -> float:
    # Power iteration on the positive matrix A^{(q)}.
    A = [[0.0 for _ in range(q + 1)] for _ in range(q + 1)]
    for k in range(q + 1):
        for l in range(q + 1):
            A[k][l] = 0.5 * (math.comb(q, l) + (math.comb(q - k, l) if q - k >= l else 0))

    v = [1.0 for _ in range(q + 1)]
    lam = 0.0
    for _ in range(iters):
        w = [0.0 for _ in range(q + 1)]
        for i in range(q + 1):
            s = 0.0
            Ai = A[i]
            for j in range(q + 1):
                s += Ai[j] * v[j]
            w[i] = s
        # Rayleigh quotient estimate using max ratio (positive vectors).
        lam_new = max(w[i] / v[i] for i in range(q + 1) if v[i] != 0.0)
        # Normalize.
        mx = max(w)
        v = [wi / mx for wi in w]
        if abs(lam_new - lam) < 1e-14 * max(1.0, abs(lam_new)):
            lam = lam_new
            break
        lam = lam_new
    return lam


def _fixed_point_residual(q: int, m_terms: int = 600) -> float:
    # x = 1 + sum_{m>=1} (F_{m+3}/2^{m+1})^q x^{-m}
    rho = _perron_root_numeric(q)
    x = rho / (2 ** (q - 1))
    s = 1.0
    for m in range(1, m_terms + 1):
        b = _fib(m + 3) / (2 ** (m + 1))
        s += (b ** q) * (x ** (-m))
    return abs(x - s)


@dataclass(frozen=True)
class Check:
    name: str
    ok: bool
    detail: str


def main() -> None:
    t0 = time.time()

    checks: List[Check] = []
    samples: Dict[str, object] = {}

    # Exact / symbolic checks for small q (kept deliberately small for runtime).
    for q in range(1, 9):
        ok, detail = _moment_collapse_ok(q, m_max=6)
        checks.append(Check(name=f"moment_collapse_q{q}", ok=ok, detail=detail))

        det_num = _hankel_det_fibpower(q)
        det_cf = _hankel_det_closed_form(q)
        checks.append(Check(name=f"hankel_det_q{q}", ok=(det_num == det_cf), detail=f"det_num={det_num} det_cf={det_cf}"))

        # Vandermonde is algebraic-expensive; check a very small range.
        if q <= 4:
            okv, detailv = _vandermonde_square_ok(q)
            checks.append(Check(name=f"vandermonde_square_q{q}", ok=okv, detail=detailv))

        # Fixed-point residual is numeric; only for q>=2 where the statement is used.
        if q >= 2:
            resid = _fixed_point_residual(q, m_terms=900)
            samples[f"fixed_point_residual_q{q}"] = resid
            checks.append(Check(name=f"fixed_point_residual_q{q}", ok=(resid < 1e-10), detail=f"resid={resid:.3e}"))

    out = {
        "checks": [{"name": c.name, "ok": c.ok, "detail": c.detail} for c in checks],
        "samples": samples,
        "elapsed_s": time.time() - t0,
    }

    export_path = export_dir() / "pom_replica_softcore_fibonacci_moment_collapse_audit.json"
    _write_text(export_path, json.dumps(out, indent=2, sort_keys=True) + "\n")

    worst = [c for c in checks if not c.ok]
    if worst:
        raise SystemExit(f"FAILED {len(worst)} checks; first={worst[0].name} {worst[0].detail}")
    print("[pom_replica_softcore_fibonacci_moment_collapse_audit] all checks passed")


if __name__ == "__main__":
    main()

