#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit an upper bound for J(C)(Q)_tors via good-prime specializations.

Curve (genus 2):
  C: w^2 = -y(y-1) P_LY(y),   P_LY(y)=256y^3+411y^2+165y+32.

For good primes p (p not in {2,3,31,37}), the Néron specialization map injects
prime-to-p torsion:
  J(C)(Q)_tors -> J(C)(F_p).

Thus #J(C)(Q)_tors divides gcd_p #J(F_p). We compute #J(F_p) for a fixed list
of good primes, using point counts over F_p and F_{p^2} to recover the local
L-polynomial L_p(T), then evaluate #J(F_p)=L_p(1).

This script is English-only by repository convention.

Outputs:
  - artifacts/export/fold_zm_discriminant_ridge_jacobian_torsion_upper_bound_audit.json
  - sections/generated/eq_fold_zm_discriminant_ridge_jacobian_torsion_upper_bound_audit.tex
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

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
    jacobian_order: int


def _jacobian_order_from_counts(p: int, n1: int, n2: int) -> Tuple[int, int, int]:
    """
    Return (a1, a2, #J(F_p)) recovered from #C(F_p)=n1 and #C(F_{p^2})=n2.
    """
    p = int(p)
    a1 = p + 1 - int(n1)
    s2 = p * p + 1 - int(n2)  # sum alpha_i^2
    a2 = (a1 * a1 - s2) // 2
    if 2 * a2 != (a1 * a1 - s2):
        raise RuntimeError(f"Non-integral a2 at p={p}")
    # L_p(1) = #J(F_p) for the genus-2 Jacobian.
    jac = p * p + 1 + a2 - a1 * (p + 1)
    return int(a1), int(a2), int(jac)


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit gcd bounds for J(C)(Q)_tors via #J(F_p).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-ridge-jac-tors] start", flush=True)

    # Good primes (exclude 2,3,31,37) used in the manuscript statement.
    primes = [5, 7, 11, 13, 17, 19, 23, 29]

    expected_j_orders = {
        5: 24,
        7: 36,
        11: 72,
        13: 168,
        17: 264,
        19: 336,
        23: 456,
        29: 912,
    }

    rows: List[Row] = []
    g = 0

    for p in primes:
        n1 = count_C_Fp(p)
        n2 = count_C_Fp2(p)
        a1, a2, jac = _jacobian_order_from_counts(p, n1, n2)

        if expected_j_orders.get(p) is not None and jac != expected_j_orders[p]:
            raise RuntimeError(f"Unexpected #J(F_{p}): got {jac}, expected {expected_j_orders[p]}")

        g = math.gcd(g, jac)
        rows.append(Row(p=int(p), n_fp=int(n1), n_fp2=int(n2), a1=int(a1), a2=int(a2), jacobian_order=int(jac)))

    payload: Dict[str, object] = {
        "curve": "w^2 = -y(y-1)(256y^3+411y^2+165y+32)",
        "rows": [asdict(r) for r in rows],
        "gcd_jacobian_orders": int(g),
        "primes": primes,
    }

    if not args.no_output:
        out_json = export_dir() / "fold_zm_discriminant_ridge_jacobian_torsion_upper_bound_audit.json"
        _write_json(out_json, payload)

        items = ",\\ ".join([f"\\#J(\\mathbb{{F}}_{{{r.p}}})={r.jacobian_order}" for r in rows])
        gcd_args = ",\\ ".join([f"\\#J(\\mathbb{{F}}_{{{r.p}}})" for r in rows])
        gcd_line = f"\\gcd\\bigl({gcd_args}\\bigr)={g}."
        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_fold_zm_discriminant_ridge_jacobian_torsion_upper_bound_audit.py",
                "\\[",
                items + ".",
                "\\]",
                "\\[",
                gcd_line,
                "\\]",
                "",
            ]
        )
        out_tex = generated_dir() / "eq_fold_zm_discriminant_ridge_jacobian_torsion_upper_bound_audit.tex"
        _write_text(out_tex, tex)

        print(f"[fold-zm-ridge-jac-tors] wrote {out_json}", flush=True)
        print(f"[fold-zm-ridge-jac-tors] wrote {out_tex}", flush=True)

    dt = time.time() - t0
    print(f"[fold-zm-ridge-jac-tors] gcd={g} seconds={dt:.3f}", flush=True)
    print("[fold-zm-ridge-jac-tors] done", flush=True)


if __name__ == "__main__":
    main()
