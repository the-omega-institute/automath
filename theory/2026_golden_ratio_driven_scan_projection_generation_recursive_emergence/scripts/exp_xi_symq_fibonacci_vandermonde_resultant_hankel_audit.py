#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit Fibonacci--Vandermonde discriminant and Sylvester resultant identities for Sym^q(K) and its rank-one coupling.

This script is English-only by repository convention.

We certify for small q (default q=2..8):
  - Disc(g_q) for g_q(z)=det(zI-Sym^q(K)) matches the closed form
      5^{q(q+1)/2} * Π_{k=1}^q F_k^{2(q+1-k)}.
  - Res_z(g_q,p_q) for p_q(z)=det(zI-(Sym^q(K)+Sym^q(J))) matches the closed form
      (-1)^{(q+1)(q+2)/2} * (Π_{i=0}^q binom(q,i)) * Π_{k=1}^q F_k^{2(q+1-k)}.
  - Hankel determinant det(H_q) with H_q=(F_{i+j+3}^q) matches the product form and the bridge to the resultant.
  - Coupling scaling: Res_z(g_q,p_{q,t}) = t^{q+1} Res_z(g_q,p_{q,1}).

Output:
  - artifacts/export/xi_symq_fibonacci_vandermonde_resultant_hankel_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def fib(n: int) -> int:
    """Fibonacci numbers with F_1=F_2=1."""
    if n <= 0:
        raise ValueError("n must be positive")
    if n <= 2:
        return 1
    a, b = 1, 1
    for _ in range(3, n + 1):
        a, b = b, a + b
    return b


def sym_power_matrix(M: sp.Matrix, q: int) -> sp.Matrix:
    """Return Sym^q(M) in the monomial basis x^{q-i} y^i (i=0..q)."""
    if M.shape != (2, 2):
        raise ValueError("M must be 2x2")
    if q < 0:
        raise ValueError("q must be nonnegative")
    a, b, c, d = [sp.Integer(v) for v in list(M)]
    x, y = sp.symbols("x y")
    # Basis: m_i = x^{q-i} y^i.
    basis = [x ** (q - i) * y**i for i in range(q + 1)]
    # Action: (x,y) -> (a x + b y, c x + d y).
    xp = a * x + b * y
    yp = c * x + d * y
    cols: List[List[sp.Expr]] = []
    for m in basis:
        # IMPORTANT: substitution must be simultaneous; otherwise xp's y would be replaced by yp.
        img = sp.expand(m.subs({x: xp, y: yp}, simultaneous=True))
        coeffs = []
        for i in range(q + 1):
            coeffs.append(sp.Poly(img, x, y, domain=sp.ZZ).coeff_monomial(x ** (q - i) * y**i))
        cols.append(coeffs)
    return sp.Matrix(cols).T


def disc_formula(q: int) -> int:
    exp = q * (q + 1) // 2
    out = 5**exp
    for k in range(1, q + 1):
        out *= fib(k) ** (2 * (q + 1 - k))
    return int(out)


def fib_product(q: int) -> int:
    out = 1
    for k in range(1, q + 1):
        out *= fib(k) ** (2 * (q + 1 - k))
    return int(out)


def binom_product(q: int) -> int:
    out = 1
    for i in range(q + 1):
        out *= int(sp.binomial(q, i))
    return int(out)


@dataclass(frozen=True)
class Record:
    q: int
    disc_ok: bool
    disc_value: int
    disc_expected: int
    resultant_ok: bool
    resultant_value: int
    resultant_expected: int
    hankel_det_ok: bool
    hankel_det_value: int
    hankel_det_expected: int
    bridge_ok: bool
    t_scaling_ok: bool


@dataclass(frozen=True)
class Payload:
    q_min: int
    q_max: int
    records: List[Record]
    seconds: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Sym^q(K) discriminant/resultant/Hankel identities for small q.")
    parser.add_argument("--q-min", type=int, default=2)
    parser.add_argument("--q-max", type=int, default=8)
    parser.add_argument("--no-output", action="store_true")
    args = parser.parse_args()

    t0 = time.time()
    print("[xi-symq-fibonacci-vandermonde] start", flush=True)

    z = sp.Symbol("z")
    K = sp.Matrix([[1, 1], [1, 0]])
    J = sp.Matrix([[1, 1], [1, 1]])

    records: List[Record] = []
    for q in range(args.q_min, args.q_max + 1):
        Bq = sym_power_matrix(K, q)
        Eq = sym_power_matrix(J, q)
        Aq = Bq + Eq

        gq = sp.Poly((z * sp.eye(q + 1) - Bq).det(), z, domain=sp.ZZ)
        pq = sp.Poly((z * sp.eye(q + 1) - Aq).det(), z, domain=sp.ZZ)

        disc_val = int(sp.discriminant(gq.as_expr(), z))
        disc_exp = disc_formula(q)
        disc_ok = disc_val == disc_exp

        res_val = int(sp.resultant(gq.as_expr(), pq.as_expr(), z))
        res_exp = ((-1) ** (((q + 1) * (q + 2)) // 2)) * binom_product(q) * fib_product(q)
        res_ok = res_val == res_exp

        # Hankel determinant: H_q = (F_{i+j+3}^q)_{0<=i,j<=q}.
        H = sp.Matrix([[sp.Integer(fib(i + j + 3)) ** q for j in range(q + 1)] for i in range(q + 1)])
        hankel_val = int(H.det())
        hankel_exp = binom_product(q) * fib_product(q)
        hankel_ok = hankel_val == hankel_exp

        bridge_ok = res_val == ((-1) ** (((q + 1) * (q + 2)) // 2)) * hankel_val

        # Coupling scaling check at a fixed nonzero integer t.
        t = sp.Integer(7)
        pqt = sp.Poly((z * sp.eye(q + 1) - (Bq + t * Eq)).det(), z, domain=sp.ZZ)
        res_t = int(sp.resultant(gq.as_expr(), pqt.as_expr(), z))
        t_scaling_ok = res_t == int(t ** (q + 1)) * res_val

        records.append(
            Record(
                q=q,
                disc_ok=disc_ok,
                disc_value=disc_val,
                disc_expected=disc_exp,
                resultant_ok=res_ok,
                resultant_value=res_val,
                resultant_expected=res_exp,
                hankel_det_ok=hankel_ok,
                hankel_det_value=hankel_val,
                hankel_det_expected=hankel_exp,
                bridge_ok=bridge_ok,
                t_scaling_ok=t_scaling_ok,
            )
        )

        assert disc_ok and res_ok and hankel_ok and bridge_ok and t_scaling_ok

    seconds = time.time() - t0
    payload = Payload(q_min=args.q_min, q_max=args.q_max, records=records, seconds=seconds)

    if not args.no_output:
        _write_json(export_dir() / "xi_symq_fibonacci_vandermonde_resultant_hankel_audit.json", asdict(payload))

    print(f"[xi-symq-fibonacci-vandermonde] ok seconds={seconds:.3f}", flush=True)


if __name__ == "__main__":
    main()

