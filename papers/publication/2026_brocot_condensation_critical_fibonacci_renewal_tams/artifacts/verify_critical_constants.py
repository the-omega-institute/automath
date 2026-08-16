#!/usr/bin/env python3
"""Reproduce the numerical consistency check for the critical constants."""

from __future__ import annotations

import argparse
from array import array

import mpmath as mp


DEFAULT_CUTOFFS = (1_000, 10_000, 100_000, 1_000_000)


def critical_exponent(decimal_places: int = 50) -> mp.mpf:
    """Solve zeta(s - 1) / zeta(s) = 2 on (2, 3)."""
    mp.mp.dps = decimal_places
    return mp.findroot(lambda s: mp.zeta(s - 1) / mp.zeta(s) - 2, (mp.mpf("2.4"), mp.mpf("2.6")))


def totients(limit: int) -> array:
    """Return phi(0), ..., phi(limit) using an integer sieve."""
    values = array("I", range(limit + 1))
    for prime in range(2, limit + 1):
        if values[prime] == prime:
            for multiple in range(prime, limit + 1, prime):
                values[multiple] -= values[multiple] // prime
    return values


def truncated_context_constants(sigma: mp.mpf, cutoffs: tuple[int, ...]) -> dict[int, float]:
    """Compute 2 rho_Q^2 at the requested totient-series cutoffs."""
    if not cutoffs or min(cutoffs) < 2:
        raise ValueError("cutoffs must be integers at least 2")
    ordered = tuple(sorted(set(cutoffs)))
    phi = totients(ordered[-1])
    sigma_float = float(sigma)
    rho_q = 1.0
    results: dict[int, float] = {}
    next_index = 0
    for q in range(2, ordered[-1] + 1):
        rho_q += phi[q] / q**sigma_float
        if q == ordered[next_index]:
            results[q] = 2.0 * rho_q * rho_q
            next_index += 1
            if next_index == len(ordered):
                break
    return results


def exact_constants(sigma: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]:
    """Return alpha, correction exponent, K_C, and the scale coefficient."""
    alpha = sigma - 1
    correction_exponent = 3 - sigma
    k_c = mp.power(2, sigma + 2) / (sigma - 1)
    scale_coefficient = mp.power(k_c, 1 / alpha)
    return alpha, correction_exponent, k_c, scale_coefficient


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-cutoff",
        type=int,
        default=DEFAULT_CUTOFFS[-1],
        help="largest totient-series cutoff (default: 1000000)",
    )
    args = parser.parse_args()
    cutoffs = tuple(q for q in DEFAULT_CUTOFFS if q <= args.max_cutoff)
    if not cutoffs or cutoffs[-1] != args.max_cutoff:
        cutoffs = (*cutoffs, args.max_cutoff)

    sigma = critical_exponent()
    alpha, correction_exponent, k_c, scale_coefficient = exact_constants(sigma)
    approximations = truncated_context_constants(sigma, cutoffs)

    print(f"sigma_0 = {mp.nstr(sigma, 17)}")
    print(f"alpha = sigma_0 - 1 = {mp.nstr(alpha, 17)}")
    print(f"3 - sigma_0 = {mp.nstr(correction_exponent, 17)}")
    print(f"b_C = 8 (exact)")
    print(f"K_C = {mp.nstr(k_c, 17)}")
    print(
        "a_n coefficient in a_n = coefficient * n^(1/alpha): "
        f"{mp.nstr(scale_coefficient, 17)}"
    )
    print("truncated checks 2 * rho_Q^2:")
    for cutoff, value in approximations.items():
        print(f"  Q={cutoff:>7d}: {value:.10f}")


if __name__ == "__main__":
    main()
