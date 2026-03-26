#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the R-translation biquartic fingerprint and Galois consequences.

This script certifies the chain used in the xi elliptic-translation section:
  1) The expanded biquartic F(u,v) equals the previously established H1-model.
  2) Disc_v(F) factors as
       -u^3 (u-1)^7 P_LY(u) C(u)^2,
     where
       P_LY(u)=256u^3+411u^2+165u+32,
       C(u)=u^4-4u^3+6u^2+12u-7.
  3) Specialization u=2 gives
       f(v)=81v^4+20v^3-26v^2-10v-1
     with:
       - irreducible over Q and over F_7,
       - discriminant -20270000 (nonsquare),
       - resolvent cubic
         531441 t^3 + 170586 t^2 + 10044 t + 724
         irreducible over Q and over F_19,
       - Galois group order 24 (S4 certificate).
  4) For C(u):
       - irreducible over Q,
       - Disc(C) = -2^16 * 5^2,
       - resolvent factorization (t-10)(t^2+4t+20),
       - Galois group order 8 and dihedral.
  5) The quadratic-sign polynomial
       Delta_sf(u) = -u(u-1)P_LY(u)
     is squarefree.

Output:
  - artifacts/export/fold_zm_elliptic_translation_r_s4_d4_audit.json
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


def _quartic_resolvent_monic(
    b: sp.Rational, c: sp.Rational, d: sp.Rational, e: sp.Rational, t: sp.Symbol
) -> sp.Expr:
    """Classical cubic resolvent for x^4 + b x^3 + c x^2 + d x + e."""
    return sp.expand(t**3 - c * t**2 + (b * d - 4 * e) * t + (4 * c * e - b * b * e - d * d))


def _is_irreducible_over_q(poly: sp.Poly) -> bool:
    return bool(poly.is_irreducible)


def _galois_group(poly: sp.Poly):
    out = poly.galois_group()
    if isinstance(out, tuple):
        return out[0]
    return out


def _is_square_in_q_int(n: int) -> bool:
    if n < 0:
        return False
    _, ok = sp.integer_nthroot(n, 2)
    return bool(ok)


@dataclass(frozen=True)
class Payload:
    expanded_f_matches_h1: bool
    disc_v_factorization_ok: bool
    f_u2_matches_expected: bool
    f_u2_irreducible_over_q: bool
    f_u2_mod7_irreducible: bool
    f_u2_discriminant: int
    f_u2_discriminant_matches_expected: bool
    f_u2_discriminant_is_square: bool
    f_u2_galois_group_order: int
    f_u2_galois_group_is_symmetric: bool
    resolvent_u2_matches_expected: bool
    resolvent_u2_irreducible_over_q: bool
    resolvent_u2_mod19_irreducible: bool
    c_irreducible_over_q: bool
    c_discriminant: int
    c_discriminant_matches_expected: bool
    c_discriminant_is_square: bool
    c_resolvent_factorization_ok: bool
    c_galois_group_order: int
    c_galois_group_is_dihedral: bool
    c_odd_ramified_primes: List[int]
    c_unique_odd_ramified_prime_5: bool
    delta_sf_squarefree: bool
    elapsed_s: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit R-translation biquartic S4/D4 certificates.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    t0 = time.time()
    u, v, t = sp.symbols("u v t")

    F = sp.expand(
        u**4 * v**4
        + 4 * u**3 * v**4
        - u**3 * v**3
        - 9 * u**3 * v**2
        - 5 * u**3 * v
        - u**3
        + 6 * u**2 * v**4
        + 4 * u**2 * v**3
        + 13 * u**2 * v**2
        + 10 * u**2 * v
        + 3 * u**2
        + 4 * u * v**4
        + 6 * u * v**3
        - 2 * u * v**2
        - 5 * u * v
        - 3 * u
        + v**4
        - 2 * v**2
        + 1
    )

    H1 = sp.expand(
        (u + 1) ** 4 * v**4
        + (-u**3 + 4 * u**2 + 6 * u) * v**3
        + (-9 * u**3 + 13 * u**2 - 2 * u - 2) * v**2
        + (-5 * u**3 + 10 * u**2 - 5 * u) * v
        - (u - 1) ** 3
    )
    expanded_f_matches_h1 = sp.expand(F - H1) == 0

    ply = 256 * u**3 + 411 * u**2 + 165 * u + 32
    c_quartic = u**4 - 4 * u**3 + 6 * u**2 + 12 * u - 7
    disc_v = sp.expand(sp.discriminant(F, v))
    disc_v_expected = sp.expand(-u**3 * (u - 1) ** 7 * ply * c_quartic**2)
    disc_v_factorization_ok = sp.expand(disc_v - disc_v_expected) == 0

    f_u2_expr = sp.expand(F.subs(u, sp.Integer(2)))
    f_u2_expected_expr = sp.expand(81 * v**4 + 20 * v**3 - 26 * v**2 - 10 * v - 1)
    f_u2_matches_expected = sp.expand(f_u2_expr - f_u2_expected_expr) == 0

    f_u2 = sp.Poly(f_u2_expr, v, domain=sp.QQ)
    f_u2_irred_q = _is_irreducible_over_q(f_u2)
    f_u2_mod7_irred = bool(sp.Poly(f_u2_expr, v, modulus=7).is_irreducible)

    f_u2_disc = int(sp.discriminant(f_u2_expr, v))
    f_u2_disc_expected = -20270000
    f_u2_disc_match = f_u2_disc == f_u2_disc_expected
    f_u2_disc_is_square = _is_square_in_q_int(f_u2_disc)

    g_u2 = _galois_group(f_u2)
    g_u2_order = int(g_u2.order())
    g_u2_is_symmetric = bool(g_u2.is_symmetric)

    monic_f_u2 = f_u2.monic()
    _, b_u2, c_u2, d_u2, e_u2 = monic_f_u2.all_coeffs()
    resolvent_u2 = sp.expand(_quartic_resolvent_monic(b_u2, c_u2, d_u2, e_u2, t) * 81**3)
    resolvent_u2_expected = sp.expand(531441 * t**3 + 170586 * t**2 + 10044 * t + 724)
    resolvent_u2_match = sp.expand(resolvent_u2 - resolvent_u2_expected) == 0

    resolvent_u2_poly = sp.Poly(resolvent_u2_expected, t, domain=sp.QQ)
    resolvent_u2_irred_q = _is_irreducible_over_q(resolvent_u2_poly)
    resolvent_u2_mod19_irred = bool(sp.Poly(resolvent_u2_expected, t, modulus=19).is_irreducible)

    c_poly = sp.Poly(c_quartic, u, domain=sp.QQ)
    c_irred_q = _is_irreducible_over_q(c_poly)
    c_disc = int(sp.discriminant(c_quartic, u))
    c_disc_expected = -(2**16) * (5**2)
    c_disc_match = c_disc == c_disc_expected
    c_disc_is_square = _is_square_in_q_int(c_disc)

    _, b_c, c_c, d_c, e_c = c_poly.all_coeffs()
    resolvent_c = sp.expand(_quartic_resolvent_monic(b_c, c_c, d_c, e_c, t))
    resolvent_c_expected_factor = sp.expand((t - 10) * (t**2 + 4 * t + 20))
    c_resolvent_factorization_ok = sp.expand(resolvent_c - resolvent_c_expected_factor) == 0

    g_c = _galois_group(c_poly)
    g_c_order = int(g_c.order())
    g_c_is_dihedral = bool(g_c.is_dihedral)

    c_factor_map = sp.factorint(abs(c_disc))
    c_odd_primes = sorted(int(p) for p in c_factor_map if int(p) % 2 == 1)
    c_unique_odd_prime_5 = c_odd_primes == [5]

    delta_sf = sp.expand(-u * (u - 1) * ply)
    delta_sf_squarefree = sp.gcd(delta_sf, sp.diff(delta_sf, u)) == 1

    payload = Payload(
        expanded_f_matches_h1=bool(expanded_f_matches_h1),
        disc_v_factorization_ok=bool(disc_v_factorization_ok),
        f_u2_matches_expected=bool(f_u2_matches_expected),
        f_u2_irreducible_over_q=bool(f_u2_irred_q),
        f_u2_mod7_irreducible=bool(f_u2_mod7_irred),
        f_u2_discriminant=int(f_u2_disc),
        f_u2_discriminant_matches_expected=bool(f_u2_disc_match),
        f_u2_discriminant_is_square=bool(f_u2_disc_is_square),
        f_u2_galois_group_order=int(g_u2_order),
        f_u2_galois_group_is_symmetric=bool(g_u2_is_symmetric),
        resolvent_u2_matches_expected=bool(resolvent_u2_match),
        resolvent_u2_irreducible_over_q=bool(resolvent_u2_irred_q),
        resolvent_u2_mod19_irreducible=bool(resolvent_u2_mod19_irred),
        c_irreducible_over_q=bool(c_irred_q),
        c_discriminant=int(c_disc),
        c_discriminant_matches_expected=bool(c_disc_match),
        c_discriminant_is_square=bool(c_disc_is_square),
        c_resolvent_factorization_ok=bool(c_resolvent_factorization_ok),
        c_galois_group_order=int(g_c_order),
        c_galois_group_is_dihedral=bool(g_c_is_dihedral),
        c_odd_ramified_primes=c_odd_primes,
        c_unique_odd_ramified_prime_5=bool(c_unique_odd_prime_5),
        delta_sf_squarefree=bool(delta_sf_squarefree),
        elapsed_s=float(time.time() - t0),
    )

    if not payload.expanded_f_matches_h1:
        raise AssertionError("expanded F(u,v) does not match H1(u,v)")
    if not payload.disc_v_factorization_ok:
        raise AssertionError("Disc_v(F) factorization failed")
    if not payload.f_u2_matches_expected:
        raise AssertionError("u=2 specialization mismatch")
    if not payload.f_u2_irreducible_over_q:
        raise AssertionError("f_u2 is reducible over Q")
    if not payload.f_u2_mod7_irreducible:
        raise AssertionError("f_u2 is reducible over F_7")
    if not payload.f_u2_discriminant_matches_expected:
        raise AssertionError(f"f_u2 discriminant mismatch: got {payload.f_u2_discriminant}")
    if payload.f_u2_discriminant_is_square:
        raise AssertionError("f_u2 discriminant unexpectedly square")
    if payload.f_u2_galois_group_order != 24 or not payload.f_u2_galois_group_is_symmetric:
        raise AssertionError(
            f"u=2 Galois group certificate failed: order={payload.f_u2_galois_group_order}, "
            f"is_symmetric={payload.f_u2_galois_group_is_symmetric}"
        )
    if not payload.resolvent_u2_matches_expected:
        raise AssertionError("u=2 resolvent cubic mismatch")
    if not payload.resolvent_u2_irreducible_over_q:
        raise AssertionError("u=2 resolvent cubic reducible over Q")
    if not payload.resolvent_u2_mod19_irreducible:
        raise AssertionError("u=2 resolvent cubic reducible over F_19")
    if not payload.c_irreducible_over_q:
        raise AssertionError("C(u) reducible over Q")
    if not payload.c_discriminant_matches_expected:
        raise AssertionError(f"C(u) discriminant mismatch: got {payload.c_discriminant}")
    if payload.c_discriminant_is_square:
        raise AssertionError("C(u) discriminant unexpectedly square")
    if not payload.c_resolvent_factorization_ok:
        raise AssertionError("C(u) resolvent factorization mismatch")
    if payload.c_galois_group_order != 8 or not payload.c_galois_group_is_dihedral:
        raise AssertionError(
            f"C(u) Galois group certificate failed: order={payload.c_galois_group_order}, "
            f"is_dihedral={payload.c_galois_group_is_dihedral}"
        )
    if not payload.c_unique_odd_ramified_prime_5:
        raise AssertionError(f"unexpected odd ramified primes in Disc(C): {payload.c_odd_ramified_primes}")
    if not payload.delta_sf_squarefree:
        raise AssertionError("Delta_sf(u) is not squarefree")

    if not args.no_output:
        out = export_dir() / "fold_zm_elliptic_translation_r_s4_d4_audit.json"
        _write_json(out, asdict(payload))

    print(
        "[fold-zm-elliptic-translation-r-s4-d4] "
        f"disc_ok={payload.disc_v_factorization_ok} "
        f"f_u2_irred={payload.f_u2_irreducible_over_q} "
        f"f_u2_galois_order={payload.f_u2_galois_group_order} "
        f"c_dihedral={payload.c_galois_group_is_dihedral} "
        f"odd_primes={payload.c_odd_ramified_primes} "
        f"elapsed_s={payload.elapsed_s:.3f}",
        flush=True,
    )


if __name__ == "__main__":
    main()
