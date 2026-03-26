#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit local semistable fingerprints for the A5-quotient genus-2 curve C_{A5}.

This script is English-only by repository convention.

We work with the hyperelliptic model
  C_{A5}:  s^2 = f(δ),   f(δ) = (δ-4) B5(δ),
where B5 is the delta-branch quintic in the manuscript.

We certify:
  - Disc(f) = Disc(B5) * B5(4)^2 and its full prime factorization in Z.
  - The odd semistable primes p != 3 at which f mod p has a unique double root.
  - For p in {11,13,17,223,3739,7333}: the normalization quartic, j-invariant,
    node splitting sign ε_p (square class), and a_p from point counting.

Outputs:
  - artifacts/export/xi_delta_ca5_semistable_local_factors_audit.json
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _legendre_symbol(a: int, p: int) -> int:
    a %= p
    if a == 0:
        return 0
    t = pow(a, (p - 1) // 2, p)
    return -1 if t == p - 1 else int(t)


def _repeated_linear_root_mod_p(poly_ZZ: sp.Poly, *, p: int, var: sp.Symbol) -> int | None:
    """If poly has a repeated linear factor over F_p, return its root in [0,p-1]."""
    poly_p = sp.Poly(poly_ZZ.as_expr(), var, modulus=p)
    g = sp.gcd(poly_p, poly_p.diff())
    if g.degree() <= 0:
        return None
    fac = sp.factor_list(g.as_expr(), modulus=p)
    for f_expr, _mult in fac[1]:
        f = sp.Poly(f_expr, var, modulus=p)
        if f.degree() == 1:
            a = int(f.all_coeffs()[0]) % p
            b = int(f.all_coeffs()[1]) % p
            r = (-b * pow(a, -1, p)) % p
            return int(r)
    return None


def _quartic_coeffs_deg4(poly_p: sp.Poly, *, p: int, var: sp.Symbol) -> Tuple[int, int, int, int, int]:
    q = sp.Poly(poly_p.as_expr(), var, modulus=p)
    deg = q.degree()
    if deg > 4:
        raise ValueError(f"expected degree <= 4, got degree={deg}")
    coeffs = [0] * (5 - (deg + 1)) + [int(c) % p for c in q.all_coeffs()]
    a, b, c, d, e = coeffs
    return int(a), int(b), int(c), int(d), int(e)


def _binary_quartic_j_invariant_mod_p(coeffs: Tuple[int, int, int, int, int], *, p: int) -> int:
    a, b, c, d, e = coeffs
    I = (12 * a * e - 3 * b * d + c * c) % p
    J = (72 * a * c * e + 9 * b * c * d - 27 * a * d * d - 27 * b * b * e - 2 * c * c * c) % p
    Delta = (4 * pow(I, 3, p) - (J * J) % p) % p
    if Delta == 0:
        raise ValueError("quartic discriminant is zero mod p (singular normalization)")
    num = (1728 * 4 * pow(I, 3, p)) % p
    return int((num * pow(Delta, -1, p)) % p)


def _count_points_quartic_mod_p(coeffs: Tuple[int, int, int, int, int], *, p: int) -> int:
    """Count points on v^2 = a x^4 + b x^3 + c x^2 + d x + e over F_p (weighted projective closure)."""
    a, b, c, d, e = coeffs
    n = 0
    for x in range(p):
        rhs = (a * x**4 + b * x**3 + c * x**2 + d * x + e) % p
        ls = _legendre_symbol(rhs, p)
        if rhs == 0:
            n += 1
        elif ls == 1:
            n += 2
    # Points at infinity: v^2 = a in P(1,2,1) chart (w=0, x=1).
    ls_inf = _legendre_symbol(a, p)
    if ls_inf == 1:
        n += 2
    return int(n)


@dataclass(frozen=True)
class LocalDatum:
    p: int
    double_root_delta0: int
    quartic_coeffs_a_b_c_d_e: List[int]
    j_mod_p: int
    eps_p: int
    E_count_Fp: int
    a_p: int


def main() -> None:
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
    f = sp.Poly((delta - 4) * B5.as_expr(), delta, domain=sp.ZZ)

    disc_B5 = int(sp.discriminant(B5.as_expr(), delta))
    disc_f = int(sp.discriminant(f.as_expr(), delta))
    B5_4 = int(B5.eval(4))

    disc_B5_fac = {int(k): int(v) for k, v in sp.factorint(abs(disc_B5)).items()}
    disc_f_fac = {int(k): int(v) for k, v in sp.factorint(abs(disc_f)).items()}
    B5_4_fac = {int(k): int(v) for k, v in sp.factorint(abs(B5_4)).items()}

    assert disc_B5 < 0
    assert disc_f < 0

    expected_disc_B5_fac = {2: 16, 3: 16, 17: 3, 37: 1, 223: 3, 3739: 2, 7333: 2}
    expected_B5_4_fac = {2: 6, 3: 4, 11: 3, 13: 1}
    expected_disc_f_fac = {2: 28, 3: 24, 11: 6, 13: 2, 17: 3, 37: 1, 223: 3, 3739: 2, 7333: 2}

    assert disc_B5_fac == expected_disc_B5_fac
    assert B5_4_fac == expected_B5_4_fac
    assert disc_f_fac == expected_disc_f_fac

    # Check the discriminant identity Disc((x-a)g)=Disc(g)*g(a)^2 in this instance.
    assert abs(disc_f) == abs(disc_B5) * (B5_4 * B5_4)

    # Odd semistable primes p != 3: repeated root in f mod p.
    semistable_primes_expected = [11, 13, 17, 37, 223, 3739, 7333]
    semistable_roots_expected = {
        11: 4,
        13: 4,
        17: (-2) % 17,
        37: 0,
        223: (-56) % 223,
        3739: 48,
        7333: 3257,
    }
    for p in semistable_primes_expected:
        r = _repeated_linear_root_mod_p(f, p=p, var=delta)
        assert r is not None and int(r) == int(semistable_roots_expected[p])

    # Collision primes P2: explicit node splitting parameter u_p and sign ε_p.
    # Here r_p is the unique double root of B5 mod p, hence also of f mod p away from δ=4.
    collision_primes_P2 = [17, 37, 223, 3739, 7333]
    expected_collision_u = {17: 15, 37: 29, 223: 10, 3739: 3694, 7333: 6699}
    expected_collision_eps = {17: +1, 37: -1, 223: -1, 3739: -1, 7333: -1}
    d_quadratic = -140267  # = -17*37*223

    B5pp = sp.Poly(sp.diff(B5.as_expr(), delta, 2), delta, domain=sp.ZZ)
    collision_u: Dict[str, int] = {}
    collision_eps: Dict[str, int] = {}
    collision_u_over_d_is_square: Dict[str, bool] = {}

    for p in collision_primes_P2:
        rp = int(semistable_roots_expected[p]) % p
        inv2 = pow(2, -1, p)
        u = ((rp - 4) % p) * (int(B5pp.eval(rp)) % p) % p
        u = (u * inv2) % p
        assert u != 0

        eps = +1 if _legendre_symbol(u, p) == 1 else -1

        assert u == (expected_collision_u[p] % p)
        assert eps == expected_collision_eps[p]

        collision_u[str(p)] = int(u)
        collision_eps[str(p)] = int(eps)

        if p in (3739, 7333):
            dinv = pow(d_quadratic % p, -1, p)
            w = (u * dinv) % p
            collision_u_over_d_is_square[str(p)] = bool(_legendre_symbol(w, p) == 1)
            assert collision_u_over_d_is_square[str(p)]

    # Local data at the primes requested in the manuscript table.
    primes = [11, 13, 17, 223, 3739, 7333]
    expected_j = {11: 5, 13: 2, 17: 15, 223: 98, 3739: 188, 7333: 5450}
    expected_eps = {11: -1, 13: -1, 17: +1, 223: -1, 3739: -1, 7333: -1}
    expected_ap = {11: 5, 13: 1, 17: -5, 223: -6, 3739: 33, 7333: -38}

    local_data: List[LocalDatum] = []
    for p in primes:
        fp = sp.Poly(f.as_expr(), delta, modulus=p)
        delta0 = _repeated_linear_root_mod_p(f, p=p, var=delta)
        if delta0 is None:
            raise ValueError(f"expected a repeated root mod p={p}, found none")
        div = sp.Poly(delta - int(delta0), delta, modulus=p) ** 2
        q, r = fp.div(div)
        assert r.is_zero

        coeffs = _quartic_coeffs_deg4(q, p=p, var=delta)
        j = _binary_quartic_j_invariant_mod_p(coeffs, p=p)

        g_at_root = int(q.eval(int(delta0))) % p
        eps = +1 if _legendre_symbol(g_at_root, p) == 1 else -1

        nE = _count_points_quartic_mod_p(coeffs, p=p)
        ap = p + 1 - nE

        assert int(j) == int(expected_j[p])
        assert int(eps) == int(expected_eps[p])
        assert int(ap) == int(expected_ap[p])

        local_data.append(
            LocalDatum(
                p=int(p),
                double_root_delta0=int(delta0),
                quartic_coeffs_a_b_c_d_e=[int(x) for x in coeffs],
                j_mod_p=int(j),
                eps_p=int(eps),
                E_count_Fp=int(nE),
                a_p=int(ap),
            )
        )

    payload: Dict[str, object] = {
        "B5_coeffs_high_to_low": [int(c) for c in B5.all_coeffs()],
        "disc_B5": int(disc_B5),
        "disc_B5_factorization": disc_B5_fac,
        "quadratic_discriminant_field_d": int(d_quadratic),
        "B5_at_4": int(B5_4),
        "B5_at_4_factorization": B5_4_fac,
        "disc_f": int(disc_f),
        "disc_f_factorization": disc_f_fac,
        "odd_semistable_primes_p_ne_3": semistable_primes_expected,
        "odd_semistable_double_roots_delta0": {str(k): int(v) for k, v in semistable_roots_expected.items()},
        "collision_primes_P2": collision_primes_P2,
        "collision_double_roots_r_p": {str(p): int(semistable_roots_expected[p]) for p in collision_primes_P2},
        "collision_node_u_p": collision_u,
        "collision_node_eps_p": collision_eps,
        "collision_u_over_d_is_square": collision_u_over_d_is_square,
        "local_data": [asdict(d) for d in local_data],
    }

    _write_json(export_dir() / "xi_delta_ca5_semistable_local_factors_audit.json", payload)
    print("[xi-delta-ca5-semistable-local] ok", flush=True)


if __name__ == "__main__":
    main()

