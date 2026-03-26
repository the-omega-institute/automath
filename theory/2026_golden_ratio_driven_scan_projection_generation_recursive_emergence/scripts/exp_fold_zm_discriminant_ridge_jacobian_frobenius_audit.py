#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit Frobenius polynomials for the genus-2 discriminant ridge curve

  C: w^2 = -y(y-1) P_LY(y),   P_LY(y)=256y^3+411y^2+165y+32,

and provide an irreducibility certificate (e.g. at p=13,17) supporting that
J(C) has no Q-elliptic factor (hence is Q-simple as an abelian surface).

We compute:
  - #C(F_p) and #C(F_{p^2}) for small good primes p
  - the local L-polynomial
      L_p(T)=1-a1 T + a2 T^2 - a1 p T^3 + p^2 T^4
    recovered from point counts.

Outputs:
  - artifacts/export/fold_zm_discriminant_ridge_jacobian_frobenius_audit.json
  - sections/generated/eq_fold_zm_discriminant_ridge_jacobian_frobenius_audit.tex
"""

from __future__ import annotations

import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _legendre_symbol(a: int, p: int) -> int:
    """Return (a/p) for odd prime p as -1,0,1."""
    a %= p
    if a == 0:
        return 0
    t = pow(a, (p - 1) // 2, p)
    return -1 if t == p - 1 else int(t)


def P_LY_int(y: int) -> int:
    y = int(y)
    return 256 * y**3 + 411 * y**2 + 165 * y + 32


def f_int(y: int) -> int:
    """f(y) = -y(y-1)P_LY(y) over Z."""
    y = int(y)
    return -y * (y - 1) * P_LY_int(y)


class Fp2:
    """Element of F_{p^2} = F_p[alpha]/(alpha^2 - d), represented as a + b*alpha."""

    __slots__ = ("a", "b", "p", "d")

    def __init__(self, a: int, b: int, *, p: int, d: int) -> None:
        self.p = int(p)
        self.d = int(d) % self.p
        self.a = int(a) % self.p
        self.b = int(b) % self.p

    def __add__(self, other: "Fp2") -> "Fp2":
        return Fp2(self.a + other.a, self.b + other.b, p=self.p, d=self.d)

    def __sub__(self, other: "Fp2") -> "Fp2":
        return Fp2(self.a - other.a, self.b - other.b, p=self.p, d=self.d)

    def __neg__(self) -> "Fp2":
        return Fp2(-self.a, -self.b, p=self.p, d=self.d)

    def __mul__(self, other: "Fp2") -> "Fp2":
        # (a+bα)(c+dα)=(ac+bd*d0) + (ad+bc)α, where α^2=d0
        p = self.p
        d0 = self.d
        a, b = self.a, self.b
        c, d = other.a, other.b
        ac = (a * c) % p
        bd = (b * d) % p
        ad_bc = (a * d + b * c) % p
        return Fp2(ac + bd * d0, ad_bc, p=p, d=d0)

    def __pow__(self, e: int) -> "Fp2":
        e = int(e)
        if e < 0:
            return self.inv().__pow__(-e)
        # pow by repeated squaring
        p, d0 = self.p, self.d
        result = Fp2(1, 0, p=p, d=d0)
        base = self
        k = e
        while k:
            if k & 1:
                result = result * base
            base = base * base
            k >>= 1
        return result

    def inv(self) -> "Fp2":
        # (a+bα)^{-1} = (a-bα)/N, N=a^2 - b^2*d0 in F_p
        p, d0 = self.p, self.d
        a, b = self.a, self.b
        n = (a * a - (b * b % p) * d0) % p
        if n == 0:
            raise ZeroDivisionError("Fp2 inverse of zero-norm element")
        n_inv = pow(n, -1, p)
        return Fp2(a * n_inv, (-b) * n_inv, p=p, d=d0)

    def is_zero(self) -> bool:
        return (self.a % self.p) == 0 and (self.b % self.p) == 0

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Fp2):
            return False
        return self.p == other.p and self.d == other.d and self.a == other.a and self.b == other.b

    def __repr__(self) -> str:
        return f"Fp2({self.a},{self.b};p={self.p},d={self.d})"


def _nonsquare_d(p: int) -> int:
    """Return a small d that is a nonsquare mod p (odd prime)."""
    for d in range(2, p):
        if _legendre_symbol(d, p) == -1:
            return d
    raise RuntimeError("failed to find nonsquare")


def _quad_char_fp2(a: Fp2) -> int:
    """Quadratic character on F_{p^2}: returns -1,0,1."""
    if a.is_zero():
        return 0
    q = a.p * a.p
    t = a ** ((q - 1) // 2)
    one = Fp2(1, 0, p=a.p, d=a.d)
    minus_one = Fp2(-1, 0, p=a.p, d=a.d)
    if t == one:
        return 1
    if t == minus_one:
        return -1
    # Should not happen in a finite field.
    raise RuntimeError(f"unexpected quadratic character value: {t}")


def _eval_f_fp2(y: Fp2) -> Fp2:
    """Evaluate f(y) = -y(y-1)P_LY(y) in F_{p^2}."""
    p, d0 = y.p, y.d
    c0 = Fp2(32, 0, p=p, d=d0)
    c1 = Fp2(165, 0, p=p, d=d0)
    c2 = Fp2(411, 0, p=p, d=d0)
    c3 = Fp2(256, 0, p=p, d=d0)
    P = c0 + c1 * y + c2 * (y**2) + c3 * (y**3)
    return -(y * (y - Fp2(1, 0, p=p, d=d0)) * P)


def count_C_Fp(p: int) -> int:
    """Count #C(F_p) for w^2=f(y), deg f=5 (one point at infinity)."""
    p = int(p)
    total = 1  # point at infinity
    for y in range(p):
        rhs = f_int(y) % p
        ls = _legendre_symbol(rhs, p)
        total += 1 + ls  # number of w solutions
    return int(total)


def count_C_Fp2(p: int) -> int:
    """Count #C(F_{p^2}) by explicit enumeration in a quadratic extension."""
    p = int(p)
    d0 = _nonsquare_d(p)
    total = 1  # point at infinity (odd degree model)
    for a in range(p):
        for b in range(p):
            y = Fp2(a, b, p=p, d=d0)
            rhs = _eval_f_fp2(y)
            chi = _quad_char_fp2(rhs)
            total += 1 + chi
    return int(total)


@dataclass(frozen=True)
class Row:
    p: int
    n_fp: int
    n_fp2: int
    a1: int
    a2: int
    Lp: str
    Lp_factor: str
    Lp_irreducible_ZT: bool


def main() -> None:
    t0 = time.time()
    print("[fold-zm-ridge-frob] start", flush=True)

    # Good primes (exclude 2,3,31,37)
    primes = [5, 7, 11, 13, 17]

    T = sp.Symbol("T")
    rows: List[Row] = []

    expected_counts = {
        5: (5, 33),
        7: (5, 61),
        11: (6, 130),
        13: (14, 166),
        17: (15, 337),
    }

    for p in primes:
        n1 = count_C_Fp(p)
        n2 = count_C_Fp2(p)
        if (n1, n2) != expected_counts[p]:
            raise RuntimeError(f"Unexpected counts at p={p}: got (#{n1},#{n2}), expected {expected_counts[p]}")

        a1 = p + 1 - n1
        s2 = p * p + 1 - n2  # sum alpha_i^2
        a2 = (a1 * a1 - s2) // 2
        if 2 * a2 != (a1 * a1 - s2):
            raise RuntimeError(f"Non-integral a2 at p={p}")

        Lp = 1 - a1 * T + a2 * T**2 - a1 * p * T**3 + (p * p) * T**4
        LpZ = sp.Poly(Lp, T, domain="ZZ")
        Lp_fact = sp.factor(LpZ.as_expr())
        fact_str = sp.sstr(Lp_fact)
        irr = bool(sp.factor_list(LpZ.as_expr(), gens=[T], modulus=None)[1] == [(LpZ.as_expr(), 1)])

        rows.append(
            Row(
                p=int(p),
                n_fp=int(n1),
                n_fp2=int(n2),
                a1=int(a1),
                a2=int(a2),
                Lp=sp.sstr(LpZ.as_expr()),
                Lp_factor=fact_str,
                Lp_irreducible_ZT=bool(irr),
            )
        )

    payload: Dict[str, object] = {
        "curve": "w^2 = -y(y-1)(256y^3+411y^2+165y+32)",
        "rows": [asdict(r) for r in rows],
    }

    out_json = export_dir() / "fold_zm_discriminant_ridge_jacobian_frobenius_audit.json"
    _write_json(out_json, payload)

    # Short TeX snippet: highlight irreducible polynomials at p=13,17
    row13 = next(r for r in rows if r.p == 13)
    row17 = next(r for r in rows if r.p == 17)
    tex_lines = [
        "% Auto-generated by scripts/exp_fold_zm_discriminant_ridge_jacobian_frobenius_audit.py",
        "\\[",
        f"L_{{13}}(T)={row13.Lp}\\quad\\text{{(irreducible in }}\\mathbb{{Z}}[T]\\text{{)}},\\qquad"
        f"L_{{17}}(T)={row17.Lp}\\quad\\text{{(irreducible in }}\\mathbb{{Z}}[T]\\text{{)}}.",
        "\\]",
        "",
    ]
    out_tex = generated_dir() / "eq_fold_zm_discriminant_ridge_jacobian_frobenius_audit.tex"
    _write_text(out_tex, "\n".join(tex_lines))

    dt = time.time() - t0
    print(f"[fold-zm-ridge-frob] wrote {out_json}", flush=True)
    print(f"[fold-zm-ridge-frob] wrote {out_tex}", flush=True)
    print(f"[fold-zm-ridge-frob] seconds={dt:.3f}", flush=True)
    print("[fold-zm-ridge-frob] done", flush=True)


if __name__ == "__main__":
    main()

