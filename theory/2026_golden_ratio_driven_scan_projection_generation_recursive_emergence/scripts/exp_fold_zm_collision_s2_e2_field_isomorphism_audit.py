#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the explicit cubic-field identification between the collision S2 cubic P2 and the E[2] 2-division cubic.

This script is English-only by repository convention.

We verify:
  - Tschirnhaus transform: if theta is a root of D2(X)=4X^3-4X+1, then
      Lambda := -2 + 2*theta + 4*theta^2
    satisfies P2(Lambda)=Lambda^3-2Lambda^2-2Lambda+2=0.
  - Elimination identity:
      Res_X(D2(X), Lambda-(-2+2X+4X^2)) = 16*P2(Lambda).
  - For primes p != 2,37, the splitting type of P2 mod p matches that of D2 mod p
    (same underlying cubic number field), hence matches the rationality of E(F_p)[2].
  - The Lee–Yang ramification cubic g(X)=16X^3-9X^2+1 generally has a different mod-p
    splitting pattern (controlled by Q(sqrt(-111)), not Q(sqrt(37))).

Outputs:
  - artifacts/export/fold_zm_collision_s2_e2_field_isomorphism_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _prime_sieve(n: int) -> List[bool]:
    if n < 2:
        return [False] * (n + 1)
    is_prime = [True] * (n + 1)
    is_prime[0] = False
    is_prime[1] = False
    p = 2
    while p * p <= n:
        if is_prime[p]:
            for k in range(p * p, n + 1, p):
                is_prime[k] = False
        p += 1
    return is_prime


def _primes_up_to(n: int) -> List[int]:
    sieve = _prime_sieve(n)
    return [p for p in range(2, n + 1) if sieve[p]]


def _eval_poly_mod(coeffs_desc: Tuple[int, ...], x: int, p: int) -> int:
    """Evaluate a polynomial with integer coefficients (descending order) mod p."""
    acc = 0
    for c in coeffs_desc:
        acc = (acc * x + c) % p
    return acc


def _cubic_splitting_type_mod_p(coeffs_desc: Tuple[int, ...], p: int) -> str:
    """
    Return the splitting type label for a cubic over F_p:
      - "111" (fully split into 3 linear factors, distinct roots),
      - "12"  (one linear factor and one irreducible quadratic),
      - "3"   (irreducible),
      - "bad" (has a repeated root; should only occur at discriminant primes).
    """
    roots = [x for x in range(p) if _eval_poly_mod(coeffs_desc, x, p) == 0]
    if len(roots) == 0:
        return "3"
    if len(roots) == 1:
        return "12"
    if len(roots) == 3:
        return "111"
    return "bad"


@dataclass(frozen=True)
class Counterexample:
    p: int
    P2: str
    D2: str
    g: str


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--p-max", type=int, default=200, help="check primes up to this bound")
    ap.add_argument("--max-counterexamples", type=int, default=12, help="store up to this many counterexamples")
    args = ap.parse_args()

    t0 = time.time()

    X, L = sp.symbols("X L")
    D2 = 4 * X**3 - 4 * X + 1
    P2 = L**3 - 2 * L**2 - 2 * L + 2
    tsh = -2 + 2 * X + 4 * X**2

    # Symbolic checks.
    rem = sp.Poly(P2.subs(L, tsh), X, domain=sp.QQ).rem(sp.Poly(D2, X, domain=sp.QQ)).as_expr()
    rem_ok = sp.simplify(rem) == 0

    res = sp.resultant(D2, L - tsh, X)
    res_factor = sp.factor(res)
    res_ok = sp.expand(res - 16 * P2) == 0

    # Mod-p splitting checks.
    # P2(L)=L^3-2L^2-2L+2, D2(X)=4X^3-4X+1, g(X)=16X^3-9X^2+1
    P2_coeffs = (1, -2, -2, 2)
    D2_coeffs = (4, 0, -4, 1)
    g_coeffs = (16, -9, 0, 1)

    types_count: Dict[str, int] = {"111": 0, "12": 0, "3": 0, "bad": 0}
    p_checked = 0
    mismatch_P2_D2: List[int] = []
    counterexamples_P2_g: List[Counterexample] = []

    for p in _primes_up_to(int(args.p_max)):
        if p in {2, 37}:
            continue

        tP2 = _cubic_splitting_type_mod_p(P2_coeffs, p)
        tD2 = _cubic_splitting_type_mod_p(D2_coeffs, p)
        if tP2 != tD2:
            mismatch_P2_D2.append(p)

        types_count[tP2] = types_count.get(tP2, 0) + 1
        p_checked += 1

        # Compare with the Lee–Yang ramification cubic (exclude its bad primes).
        if p not in {3}:
            tg = _cubic_splitting_type_mod_p(g_coeffs, p)
            if tP2 != tg and len(counterexamples_P2_g) < int(args.max_counterexamples):
                counterexamples_P2_g.append(Counterexample(p=p, P2=tP2, D2=tD2, g=tg))

    payload = {
        "symbolic": {
            "remainder_P2_tschirnhaus_mod_D2": str(rem),
            "remainder_ok": rem_ok,
            "resultant_factor": str(res_factor),
            "resultant_ok": res_ok,
        },
        "modp": {
            "p_max": int(args.p_max),
            "p_checked_excluding_2_37": p_checked,
            "splitting_type_counts_P2": types_count,
            "mismatch_primes_P2_vs_D2": mismatch_P2_D2,
            "counterexamples_P2_vs_g_first": [asdict(c) for c in counterexamples_P2_g],
        },
        "walltime_s": time.time() - t0,
    }

    out = export_dir() / "fold_zm_collision_s2_e2_field_isomorphism_audit.json"
    _write_json(out, payload)

    if mismatch_P2_D2:
        raise AssertionError(f"Unexpected P2 vs D2 mismatches at primes: {mismatch_P2_D2}")
    if not rem_ok or not res_ok:
        raise AssertionError("Symbolic identity check failed (see JSON payload).")


if __name__ == "__main__":
    main()

