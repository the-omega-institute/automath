#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit arithmetic fingerprints of the delta-branch quintic B5.

This script is English-only by repository convention.

We work with the quintic B5(δ) defined in the paper via
  Disc_y(F_delta(T;y)) = 16 (T-4) A5(T)^2 B5(T),
where B5(T) has explicit integer coefficients.

We certify:
  - Disc(B5) factorization in Z and the associated ramified-prime set.
  - Mod-p collision fingerprints at the ramified primes listed in the manuscript.
  - Frobenius cycle-type witnesses mod 59 (a 5-cycle) and mod 89 (a transposition).

Outputs:
  - artifacts/export/fold_zm_delta_b5_arithmetic_audit.json
  - sections/generated/eq_fold_zm_delta_b5_arithmetic_audit.tex
"""

from __future__ import annotations

import argparse
import json
import time
import warnings
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp
from sympy.utilities.exceptions import SymPyDeprecationWarning

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _factor_degrees_mod_p(poly_ZZ: sp.Poly, *, p: int, var: sp.Symbol) -> Tuple[List[int], List[int]]:
    """Return (degrees, multiplicities) of the squarefree factorization mod p."""
    fac = sp.factor_list(poly_ZZ.set_modulus(p).as_expr(), modulus=p)
    degs: List[int] = []
    mults: List[int] = []
    for f_expr, mult in fac[1]:
        degs.append(sp.Poly(f_expr, var, modulus=p).degree())
        mults.append(int(mult))
    # Keep paired order sorted by (deg, mult) for stable reporting.
    paired = sorted(zip(degs, mults))
    return [d for d, _m in paired], [_m for _d, _m in paired]


def _repeated_linear_root_mod_p(poly_ZZ: sp.Poly, *, p: int, var: sp.Symbol) -> int | None:
    """If poly has a repeated linear factor over F_p, return its root in [0,p-1]."""
    poly_p = sp.Poly(poly_ZZ.as_expr(), var, modulus=p)
    dpoly_p = poly_p.diff()
    g = sp.gcd(poly_p, dpoly_p)
    if g.degree() <= 0:
        return None
    # If g has a linear factor, it must correspond to the repeated root.
    fac = sp.factor_list(g.as_expr(), modulus=p)
    for f_expr, _mult in fac[1]:
        f = sp.Poly(f_expr, var, modulus=p)
        if f.degree() == 1:
            # f = a*var + b; root is -b/a.
            a = int(f.all_coeffs()[0]) % p
            b = int(f.all_coeffs()[1]) % p
            inv_a = pow(a, -1, p)
            r = (-b * inv_a) % p
            return int(r)
    return None


@dataclass(frozen=True)
class ModPCollision:
    p: int
    factor_degrees: List[int]
    factor_mults: List[int]
    repeated_linear_root: int | None


@dataclass(frozen=True)
class Payload:
    b5_coeffs_high_to_low: List[int]
    disc_b5: int
    disc_b5_factorization: Dict[int, int]
    ramified_primes_sorted: List[int]
    frob_mod59_degrees: List[int]
    frob_mod89_degrees: List[int]
    modp_collisions: List[ModPCollision]
    seconds: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Disc(B5) and mod-p collision fingerprints.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)

    t0 = time.time()
    print("[fold-zm-delta-b5-arithmetic] start", flush=True)

    delta = sp.Symbol("delta")
    B5 = sp.Poly(
        50000 * delta**5
        + 136112 * delta**4
        + 60776 * delta**3
        - 26712 * delta**2
        + 38961 * delta
        + 35964,
        delta,
        domain=sp.ZZ,
    )

    disc_b5 = int(sp.discriminant(B5.as_expr(), delta))
    disc_fac = sp.factorint(abs(disc_b5))
    ramified_primes_sorted = sorted(disc_fac.keys())

    # Frobenius witnesses:
    frob_mod59_degrees, _ = _factor_degrees_mod_p(B5, p=59, var=delta)
    frob_mod89_degrees, _ = _factor_degrees_mod_p(B5, p=89, var=delta)

    # Collision fingerprints at the ramified primes and selected small characteristics.
    primes_to_check = sorted(set([2, 3, 17, 37, 223, 3739, 7333]))
    modp_collisions: List[ModPCollision] = []
    for p in primes_to_check:
        degs, mults = _factor_degrees_mod_p(B5, p=p, var=delta)
        rr = _repeated_linear_root_mod_p(B5, p=p, var=delta)
        modp_collisions.append(ModPCollision(p=p, factor_degrees=degs, factor_mults=mults, repeated_linear_root=rr))

    seconds = time.time() - t0

    payload = Payload(
        b5_coeffs_high_to_low=[int(c) for c in B5.all_coeffs()],
        disc_b5=disc_b5,
        disc_b5_factorization={int(k): int(v) for k, v in disc_fac.items()},
        ramified_primes_sorted=ramified_primes_sorted,
        frob_mod59_degrees=frob_mod59_degrees,
        frob_mod89_degrees=frob_mod89_degrees,
        modp_collisions=modp_collisions,
        seconds=seconds,
    )

    # Expected discriminant fingerprint recorded in the manuscript.
    expected_fac = {2: 16, 3: 16, 17: 3, 37: 1, 223: 3, 3739: 2, 7333: 2}
    assert disc_b5 < 0
    assert payload.disc_b5_factorization == expected_fac
    assert payload.ramified_primes_sorted == sorted(expected_fac.keys())

    # Frobenius cycle types used in the S5 generation argument.
    assert payload.frob_mod59_degrees == [5]
    assert sorted(payload.frob_mod89_degrees) == [1, 1, 1, 2]

    # Recorded collision roots in odd characteristics (linear double root).
    expected_double_roots = {17: (-2) % 17, 37: 0, 223: (-56) % 223, 3739: 48, 7333: 3257}
    for rec in payload.modp_collisions:
        if rec.p in expected_double_roots:
            assert rec.repeated_linear_root == expected_double_roots[rec.p]

    # Characteristic 3 collapse.
    # B5(δ) ≡ c * δ^3(δ-1)^2 with c ≠ 0 in F_3.
    poly3 = sp.Poly(B5.as_expr(), delta, modulus=3)
    target3 = sp.Poly(delta**3 * (delta - 1) ** 2, delta, modulus=3)
    q, r = sp.div(poly3, target3)
    assert r.is_zero
    assert q.degree() == 0 and int(q.all_coeffs()[0]) % 3 != 0

    if not args.no_output:
        _write_json(export_dir() / "fold_zm_delta_b5_arithmetic_audit.json", asdict(payload))

        tex = r"""% Auto-generated by scripts/exp_fold_zm_delta_b5_arithmetic_audit.py
\begin{align}
\Disc(B_5)
&=-2^{16}\cdot 3^{16}\cdot 17^{3}\cdot 37\cdot 223^{3}\cdot 3739^{2}\cdot 7333^{2},\\
B_5(\delta)\bmod 59\ \text{不可约}\ &\Longleftrightarrow\ \text{Frobenius 含一个 }(5)\text{-循环},\\
B_5(\delta)\bmod 89\ \text{分解型 }(2)(1)(1)(1)\ &\Longleftrightarrow\ \text{Frobenius 含一个换位},\\
B_5(\delta)\bmod 3&\equiv \delta^{3}(\delta-1)^{2}.
\end{align}
"""
        _write_text(generated_dir() / "eq_fold_zm_delta_b5_arithmetic_audit.tex", tex)

    print(f"[fold-zm-delta-b5-arithmetic] ok seconds={seconds:.3f}", flush=True)


if __name__ == "__main__":
    main()

