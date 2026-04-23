#!/usr/bin/env python3
from __future__ import annotations

from fractions import Fraction


J = 3


def log_bounds(q: Fraction) -> tuple[Fraction, Fraction, Fraction]:
    u = Fraction(q - 1, q + 1)
    partial = sum(
        Fraction(2) * u ** (2 * j + 1) / Fraction(2 * j + 1, 1)
        for j in range(J + 1)
    )
    remainder = (
        Fraction(2) * u ** (2 * J + 3) / (Fraction(2 * J + 3, 1) * (1 - u * u))
    )
    return u, partial, partial + remainder


def weighted_interval(coeff: Fraction, lo: Fraction, hi: Fraction) -> tuple[Fraction, Fraction]:
    if coeff >= 0:
        return coeff * lo, coeff * hi
    return coeff * hi, coeff * lo


def fmt(q: Fraction) -> str:
    return f"{q.numerator}/{q.denominator}"


def print_term_block(name: str, terms: list[tuple[str, Fraction, Fraction]]) -> tuple[Fraction, Fraction]:
    total_lo = Fraction(0, 1)
    total_hi = Fraction(0, 1)
    print(f"{name} termwise certificates")
    for label, coeff, q in terms:
        u, log_lo, log_hi = log_bounds(q)
        contrib_lo, contrib_hi = weighted_interval(coeff, log_lo, log_hi)
        total_lo += contrib_lo
        total_hi += contrib_hi
        print(f"  {label}")
        print(f"    q = {fmt(q)}")
        print(f"    u = {fmt(u)}")
        print(f"    coefficient = {fmt(coeff)}")
        print(f"    log lower = {fmt(log_lo)}")
        print(f"    log upper = {fmt(log_hi)}")
        print(f"    weighted lower = {fmt(contrib_lo)}")
        print(f"    weighted upper = {fmt(contrib_hi)}")
    print(f"  finite-sum lower = {fmt(total_lo)}")
    print(f"  finite-sum upper = {fmt(total_hi)}")
    print()
    return total_lo, total_hi


def check_window(lo: Fraction, hi: Fraction, left: Fraction, right: Fraction, label: str) -> None:
    if not (left < lo and hi < right):
        raise SystemExit(f"{label} interval is not contained in the claimed window")


E7_TERMS = [
    ("-(1/2) log(2)", Fraction(-1, 2), Fraction(2, 1)),
    ("+(1/6) log(32/31)", Fraction(1, 6), Fraction(32, 31)),
    ("+(1/10) log(512/511)", Fraction(1, 10), Fraction(512, 511)),
    ("+(1/14) log(8192/8191)", Fraction(1, 14), Fraction(8192, 8191)),
]

R15_TERMS = [
    ("-log(3/2)", Fraction(-1, 1), Fraction(3, 2)),
    ("-(1/2) log(8/5)", Fraction(-1, 2), Fraction(8, 5)),
    ("-(1/3) log(4/3)", Fraction(-1, 3), Fraction(4, 3)),
    ("+(1/5) log(33/32)", Fraction(1, 5), Fraction(33, 32)),
    ("+(1/3) log(32/31)", Fraction(1, 3), Fraction(32, 31)),
    ("+(1/7) log(129/128)", Fraction(1, 7), Fraction(129, 128)),
    ("+(1/10) log((512*1024)/(511*1025))", Fraction(1, 10), Fraction(512 * 1024, 511 * 1025)),
    ("+(1/11) log(2049/2048)", Fraction(1, 11), Fraction(2049, 2048)),
    ("+(1/13) log(8193/8192)", Fraction(1, 13), Fraction(8193, 8192)),
    ("+(1/14) log((8192*16384)/(8191*16385))", Fraction(1, 14), Fraction(8192 * 16384, 8191 * 16385)),
    ("+(1/15) log(16384/16383)", Fraction(1, 15), Fraction(16384, 16383)),
]


def main() -> None:
    e7_lo, e7_hi = print_term_block("E7", E7_TERMS)
    r15_lo, r15_hi = print_term_block("R15", R15_TERMS)

    theta_eps = Fraction(1, 1105920)
    theta_rho = Fraction(9, 524288)

    pi_eps_lo = e7_lo - theta_eps
    pi_eps_hi = e7_hi + theta_eps
    pi_rho_lo = r15_lo - theta_rho
    pi_rho_hi = r15_hi + theta_rho

    print("Total certificates")
    print(f"  E7 lower = {fmt(e7_lo)}")
    print(f"  E7 upper = {fmt(e7_hi)}")
    print(f"  Pi_epsilon lower = {fmt(pi_eps_lo)}")
    print(f"  Pi_epsilon upper = {fmt(pi_eps_hi)}")
    print(f"  R15 lower = {fmt(r15_lo)}")
    print(f"  R15 upper = {fmt(r15_hi)}")
    print(f"  Pi_rho lower = {fmt(pi_rho_lo)}")
    print(f"  Pi_rho upper = {fmt(pi_rho_hi)}")

    e7_left = Fraction(-341079, 10**6)
    e7_right = Fraction(-341071, 10**6)
    r15_left = Fraction(-718352, 10**6)
    r15_right = Fraction(-718351, 10**6)

    check_window(
        e7_lo,
        e7_hi,
        e7_left,
        e7_right,
        "E7",
    )
    check_window(
        r15_lo,
        r15_hi,
        r15_left,
        r15_right,
        "R15",
    )
    check_window(
        pi_eps_lo,
        pi_eps_hi,
        e7_left - theta_eps,
        e7_right + theta_eps,
        "Pi_epsilon sharp",
    )
    check_window(
        pi_rho_lo,
        pi_rho_hi,
        r15_left - theta_rho,
        r15_right + theta_rho,
        "Pi_rho sharp",
    )
    print("  sharp manuscript windows verified")

    check_window(
        pi_eps_lo,
        pi_eps_hi,
        Fraction(-342, 1000),
        Fraction(-341, 1000),
        "Pi_epsilon",
    )
    check_window(
        pi_rho_lo,
        pi_rho_hi,
        Fraction(-719, 1000),
        Fraction(-718, 1000),
        "Pi_rho",
    )
    print("  coarse windows verified")


if __name__ == "__main__":
    main()
