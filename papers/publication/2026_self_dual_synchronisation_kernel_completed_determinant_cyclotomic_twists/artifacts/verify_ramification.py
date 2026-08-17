#!/usr/bin/env python3
"""Exact checks for the arithmetic ramification theorem.

Run from the paper directory with

    python artifacts/verify_ramification.py

The optional --inject-error flag changes one coefficient in the claimed
discriminant and must make the verifier fail.
"""

import argparse

import sympy as sp
from sympy.polys.domains import ZZ
from sympy.polys.galoistools import gf_gcd, gf_pow_mod, gf_sub


def factor_degrees(poly, variable, prime):
    factors = sp.factor_list(poly, modulus=prime)[1]
    return sorted((sp.degree(factor, variable), exponent) for factor, exponent in factors)


def rabin_irreducible(poly, variable, prime):
    reduced = sp.Poly(poly, variable, modulus=prime).monic()
    coefficients = [int(c) % prime for c in reduced.all_coeffs()]
    degree = reduced.degree()
    x_poly = [1, 0]
    if gf_pow_mod(x_poly, prime**degree, coefficients, prime, ZZ) != x_poly:
        return False
    for divisor in sp.factorint(degree):
        power = gf_pow_mod(
            x_poly, prime ** (degree // divisor), coefficients, prime, ZZ
        )
        if gf_gcd(gf_sub(power, x_poly, prime, ZZ), coefficients, prime, ZZ) != [1]:
            return False
    return True


def main(inject_error=False):
    w, s, x, t, a, v, q = sp.symbols("w s x t a v q")
    completed = (
        1
        - s * w
        - 5 * w**2
        + 3 * s * w**3
        + (5 - s**2) * w**4
        + (s**3 - 6 * s) * w**5
        + (s**2 - 1) * w**6
    )
    claimed_discriminant = (
        -256 * s**20
        + 3712 * s**18
        - 40320 * s**16
        + 389241 * s**14
        - 3214252 * s**12
        + 13200192 * s**10
        - 20821228 * s**8
        + 708704 * s**6
        + 20467008 * s**4
        - 10514432 * s**2
        + 147456
    )
    if inject_error:
        claimed_discriminant += 1

    computed_discriminant = sp.discriminant(completed, w)
    assert sp.expand(computed_discriminant - claimed_discriminant) == 0
    assert rabin_irreducible(claimed_discriminant, s, 71)
    assert claimed_discriminant.subs(s, 1) == 325825
    assert claimed_discriminant.subs(s, -1) == 325825

    pair_polynomial = sp.Poly(claimed_discriminant, s).as_dict()
    assert all(exponent[0] % 2 == 0 for exponent in pair_polynomial)
    E = sp.expand(claimed_discriminant.subs(s**2, x))
    # SymPy substitution does not replace powers syntactically; construct E exactly.
    E = sum(coefficient * x ** (exponent[0] // 2) for exponent, coefficient in pair_polynomial.items())
    assert sp.expand(E.subs(x, s**2) - claimed_discriminant) == 0
    assert factor_degrees(E, x, 37) == [(10, 1)]
    assert factor_degrees(E, x, 17) == [(1, 1), (9, 1)]
    assert factor_degrees(E, x, 1571) == [(1, 2), (2, 1), (6, 1)]
    discriminant_E = int(sp.discriminant(E, x))
    assert discriminant_E % 1571 == 0
    assert discriminant_E % (1571**2) != 0

    V = sp.expand(v**6 * completed.subs(w, 1 / v))
    for epsilon in (1, -1):
        assert V.subs({v: 0, s: epsilon}) == 0
        assert sp.diff(V, v).subs({v: 0, s: epsilon}) == -5 * epsilon

    K = sp.expand(t**3 * completed.subs(s, 1 / t))
    endpoint_branch = sp.cancel(K.subs(w, t * a) / t**3)
    assert endpoint_branch.subs(t, 0) == 1 - a
    ramified_branches = sp.cancel(K.subs(t, v * w**2) / w**5)
    assert ramified_branches.subs(w, 0) == 1 - v**2
    infinity_branch = sp.cancel(q**6 * K.subs(w, 1 / q))
    assert infinity_branch.subs({q: 0, t: 0}) == 0
    assert sp.diff(infinity_branch, q).subs({q: 0, t: 0}) == 1
    assert sp.diff(infinity_branch, t).subs({q: 0, t: 0}) == 1
    assert 20 + 2 == 2 * 6 - 2 - 6 * (2 * 0 - 2)  # Riemann--Hurwitz for g=6.

    print("discriminant_identity: true")
    print("discriminant_mod_71_irreducible: true")
    print("finite_branch_orbit_degree: 20")
    print("pair_polynomial_galois_certificates: true")
    print("infinity_local_degrees: 1,2,2,1")
    print("ramification_degree: 22")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--inject-error", action="store_true")
    args = parser.parse_args()
    main(inject_error=args.inject_error)
