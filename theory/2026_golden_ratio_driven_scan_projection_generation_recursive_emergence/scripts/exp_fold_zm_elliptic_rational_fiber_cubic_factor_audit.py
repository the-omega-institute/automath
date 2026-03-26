#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the integral cubic residual factor on rational fibers of the Fold weight elliptic cover.

This script is English-only by repository convention.

We work with the elliptic curve
  E:  Y^2 = X^3 - X + 1/4
and the weight coordinate
  y := X^2 + Y - 1/2.

Let the Fold spectral quartic be
  Pi(lambda,y) = lambda^4 - lambda^3 - (2y+1)lambda^2 + lambda + y(y+1).

For any rational point Q in E(Q), write
  X(Q) = u / v^2  (lowest terms, v>0),
  y(Q) = a / v^4  (lowest terms).
We verify the explicit integral factorization:
  v^8 * Pi(lambda, a/v^4) = (v^2*lambda - u) * G_Q(lambda)
where G_Q(lambda) is the closed Z[lambda] cubic from the paper.

We also provide finite-window evidence for the conjecture that along the physical orbit
  Q_n = [n]P,  P=(2,-5/2),
the cubic G_{Q_n} is irreducible over Q and has nonsquare discriminant, hence
  Gal(G_{Q_n}/Q) ≅ S3.

Outputs:
  - artifacts/export/fold_zm_elliptic_rational_fiber_cubic_factor_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


Point = Optional[Tuple[sp.Rational, sp.Rational]]  # None denotes the point at infinity O


def _add(P: Point, Q: Point, *, a: sp.Rational) -> Point:
    """Group law on short Weierstrass: Y^2 = X^3 + aX + b (b unused for formulas)."""
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q

    if x1 == x2 and y1 == -y2:
        return None

    if x1 == x2 and y1 == y2:
        m = sp.simplify((3 * x1 * x1 + a) / (2 * y1))
    else:
        m = sp.simplify((y2 - y1) / (x2 - x1))

    x3 = sp.together(m * m - x1 - x2)
    y3 = sp.together(m * (x1 - x3) - y1)
    return (sp.simplify(x3), sp.simplify(y3))


def _mul(n: int, P: Point, *, a: sp.Rational) -> Point:
    if n < 0:
        if P is None:
            return None
        x, y = P
        return _mul(-n, (x, -y), a=a)
    if n == 0:
        return None
    if n == 1:
        return P
    Q: Point = None
    R: Point = P
    k = n
    while k > 0:
        if k & 1:
            Q = _add(Q, R, a=a)
        R = _add(R, R, a=a)
        k >>= 1
    return Q


def _uv_from_x(x: sp.Rational) -> Tuple[int, int]:
    """Return u,v with x = u / v^2 in lowest terms (v>0)."""
    num, den = sp.fraction(sp.together(x))
    num_i = int(num)
    den_i = int(den)
    v, exact = sp.integer_nthroot(den_i, 2)
    if not exact:
        raise ValueError(f"denominator is not a square: den={den_i}")
    if v <= 0:
        raise ValueError("unexpected nonpositive v")
    return num_i, int(v)


def _a_from_weight_y(y: sp.Rational, v: int) -> int:
    """Return integer a such that y = a / v^4 (in lowest terms, guaranteed by theory)."""
    v4 = v**4
    a_rat = sp.together(y * v4)
    num, den = sp.fraction(a_rat)
    if int(den) != 1:
        raise ValueError(f"y*v^4 not integral: denom={den}")
    return int(num)


def _cubic_coeffs(u: int, v: int, a: int) -> Tuple[int, int, int, int]:
    """Return integer coefficients (A,B,C,D) for G_Q(lambda)=A l^3 + B l^2 + C l + D."""
    v2 = v * v
    v4 = v2 * v2
    v6 = v4 * v2
    t = u * u - u * v2 - 2 * a - v4
    A = v6
    B = v4 * (u - v2)
    C = v2 * t
    D = v6 + u * t
    return A, B, C, D


def _discriminant_cubic(A: int, B: int, C: int, D: int) -> int:
    """Integer discriminant of A x^3 + B x^2 + C x + D."""
    return (
        B * B * C * C
        - 4 * A * C * C * C
        - 4 * B * B * B * D
        - 27 * A * A * D * D
        + 18 * A * B * C * D
    )


def _is_square_Z(n: int) -> bool:
    if n < 0:
        return False
    r = math.isqrt(n)
    return r * r == n


def _irreducible_mod_p_cubic(A: int, B: int, C: int, D: int, p: int) -> Optional[bool]:
    """Return True/False if reduction mod p is cubic and (ir)reducible, else None if deg drops."""
    a3 = A % p
    a2 = B % p
    a1 = C % p
    a0 = D % p
    if a3 == 0:
        return None
    # cubic over F_p is reducible iff it has a root in F_p
    for t in range(p):
        val = (((a3 * t + a2) * t + a1) * t + a0) % p
        if val == 0:
            return False
    return True


@dataclass(frozen=True)
class Row:
    n: int
    u: int
    v: int
    a: int
    x: str
    y: str
    factorization_ok: bool
    disc: int
    disc_is_square: bool
    irreducible_witness_p: Optional[int]
    irreducible_mod_p: Optional[bool]


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit the integral cubic residual factor on rational fibers and test the S3 conjecture window."
    )
    parser.add_argument("--max-n", type=int, default=12, help="max multiple n for Q_n=[n]P to audit (default: 12)")
    parser.add_argument(
        "--prime-start",
        type=int,
        default=101,
        help="start of prime search interval for irreducibility witness (default: 101)",
    )
    parser.add_argument(
        "--prime-stop",
        type=int,
        default=2000,
        help="end of prime search interval for irreducibility witness (default: 2000)",
    )
    args = parser.parse_args()

    max_n: int = int(args.max_n)
    if max_n < 1:
        raise ValueError("--max-n must be >= 1")

    # Curve: Y^2 = X^3 - X + 1/4  =>  a = -1
    curve_a = sp.Rational(-1, 1)

    # Physical base point
    P: Point = (sp.Rational(2, 1), sp.Rational(-5, 2))

    prime_candidates = list(sp.primerange(int(args.prime_start), int(args.prime_stop)))
    if not prime_candidates:
        raise ValueError("empty prime candidate list; adjust --prime-start/--prime-stop")

    lam = sp.Symbol("lambda")

    rows: List[Row] = []
    all_factorizations_ok = True
    conj_window_ok = True

    for n in range(1, max_n + 1):
        Q = _mul(n, P, a=curve_a)
        if Q is None:
            raise ValueError("unexpected torsion: [n]P == O for n in audit window")
        X, Y = Q
        y_weight = sp.together(X * X + Y - sp.Rational(1, 2))

        u, v = _uv_from_x(X)
        a_num = _a_from_weight_y(y_weight, v)
        if math.gcd(a_num, v) != 1:
            raise ValueError("expected gcd(a,v)=1 for lowest terms y=a/v^4")

        v2 = v * v
        v4 = v2 * v2
        v8 = v4 * v4

        # Cleared quartic specialization (integer polynomial in lambda)
        #   v^8 Pi(lambda, a/v^4) = v^8 l^4 - v^8 l^3 - (2a v^4 + v^8) l^2 + v^8 l + a(a+v^4)
        P_expr = (
            v8 * lam**4
            - v8 * lam**3
            - (2 * a_num * v4 + v8) * lam**2
            + v8 * lam
            + a_num * (a_num + v4)
        )

        # Closed cubic factor
        A, B, C, D = _cubic_coeffs(u=u, v=v, a=a_num)
        G_expr = A * lam**3 + B * lam**2 + C * lam + D

        L_expr = v2 * lam - u

        factorization_ok = sp.Poly(sp.expand(P_expr - L_expr * G_expr), lam, domain=sp.ZZ).is_zero
        all_factorizations_ok = all_factorizations_ok and bool(factorization_ok)

        disc = _discriminant_cubic(A, B, C, D)
        disc_is_square = _is_square_Z(disc)

        witness_p: Optional[int] = None
        irreducible_mod_p: Optional[bool] = None
        for p in prime_candidates:
            res = _irreducible_mod_p_cubic(A, B, C, D, p)
            if res is None:
                continue
            if res:
                witness_p = int(p)
                irreducible_mod_p = True
                break
            # If reducible mod this p, keep searching.

        if n >= 2:
            # Conjecture window condition: find an irreducibility witness and a nonsquare discriminant.
            if witness_p is None or disc_is_square:
                conj_window_ok = False

        rows.append(
            Row(
                n=n,
                u=u,
                v=v,
                a=a_num,
                x=f"{u}/{v}^2",
                y=f"{a_num}/{v}^4",
                factorization_ok=bool(factorization_ok),
                disc=int(disc),
                disc_is_square=bool(disc_is_square),
                irreducible_witness_p=witness_p,
                irreducible_mod_p=irreducible_mod_p,
            )
        )

    payload: Dict[str, object] = {
        "max_n": max_n,
        "prime_search": {"start": int(args.prime_start), "stop": int(args.prime_stop)},
        "all_factorizations_ok": bool(all_factorizations_ok),
        "conjecture_window_ok_for_n_ge_2": bool(conj_window_ok),
        "rows": [asdict(r) for r in rows],
    }

    _write_json(export_dir() / "fold_zm_elliptic_rational_fiber_cubic_factor_audit.json", payload)


if __name__ == "__main__":
    main()

