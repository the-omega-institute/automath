#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent check of the correction to Dushistova's leading coefficient.

The paper asserts that a published constant is wrong:

    Z_n(s) ~ C * n^{-s},   with   C = 2 R_s^2   (this paper)
                                  C = R_s + 2 R_s^2   (Dushistova 2007, Lemma 7)

where R_s = zeta(s-1)/zeta(s). At the arithmetic critical point sigma_0, defined by
R_{sigma_0} = 2, these read 8 and 10 respectively.

Of the twenty-five artifacts in this directory none touches this claim; the only mentions of
Dushistova are in prose and oracle reports. Asserting that a published coefficient is wrong
is the sharpest thing in the abstract and a referee will go straight at it, so it deserves a
computation.

    Z_n(s) = sum over (a_1,...,a_r) with a_r >= 2 and sum a_i = n  of  K(a)^{-s},

K being the continuant. The paper states the approach rate is n^{-1}, so the finite-n values
are extrapolated with that rate rather than read off directly - a raw value at reachable n
would sit between 8 and 10 and settle nothing.

I have twice claimed a constant in this paper was wrong and been wrong both times. The
controls here are therefore deliberately heavy.
"""
import sys
from mpmath import mp, zeta, findroot

mp.dps = 30


def R(s):
    return zeta(s - 1) / zeta(s)


def continuant_sum(n, s):
    """Z_n(s), by recursion over compositions with last part >= 2."""
    total = mp.mpf(0)

    def rec(rem, kprev, kcur):
        # kprev = K(a_1..a_{r-1}), kcur = K(a_1..a_r)
        nonlocal total
        if rem == 0:
            return
        for a in range(1, rem + 1):
            k = a * kcur + kprev
            left = rem - a
            if left == 0:
                if a >= 2:
                    total += mp.mpf(k) ** (-s)
            else:
                rec(left, kcur, k)

    rec(n, mp.mpf(0), mp.mpf(1))     # K_{-1} = 0, K_0 = 1
    return total


def control_continuant(nmax=9):
    """K(a_1..a_r) must be the denominator of the continued fraction [0;a_1,...,a_r].

    The first version of this script had K_{-1} and K_0 swapped, so every continuant came
    out as 1 for a single-digit word instead of a. Nothing else in the script noticed: the
    critical point, the totient identity and the two-expansion count all still passed, and
    the output was off by three orders of magnitude in a way that looked like the paper
    being wrong. A control has to touch the object actually in question.
    """
    from fractions import Fraction as Fr

    def K(a):
        km1, k0 = 0, 1
        for x in a:
            km1, k0 = k0, x * k0 + km1
        return k0

    def denom(a):
        v = Fr(0)
        for x in reversed(a):
            v = Fr(1, x + v.numerator // v.denominator) if False else Fr(1) / (x + v)
        return v.denominator

    from itertools import product
    bad = 0
    for r in range(1, 5):
        for a in product(range(1, nmax + 1), repeat=r):
            if K(a) != denom(a):
                bad += 1
    return bad == 0


def control_totient_series(s, qmax=200000):
    """1 + sum_{q>=2} phi(q) q^{-s} = zeta(s-1)/zeta(s), the proof's own identity."""
    phi = list(range(qmax + 1))
    for p in range(2, qmax + 1):
        if phi[p] == p:
            for m in range(p, qmax + 1, p):
                phi[m] -= phi[m] // p
    tot = mp.mpf(1)
    for q in range(2, qmax + 1):
        tot += mp.mpf(phi[q]) * mp.mpf(q) ** (-s)
    return tot


def control_two_expansions(nmax=12):
    """Every canonical word of digit sum m > 1 has exactly two positive expansions."""
    def comps(n):
        if n == 0:
            yield ()
            return
        for a in range(1, n + 1):
            for rest in comps(n - a):
                yield (a,) + rest

    ok = True
    for m in range(2, nmax + 1):
        canon = [c for c in comps(m) if c and c[-1] >= 2]
        allpos = [c for c in comps(m) if c]
        if len(allpos) != 2 * len(canon):
            ok = False
            print(f"    MISMATCH m={m}: {len(allpos)} positive vs {len(canon)} canonical")
    return ok


def main():
    print("CONTROL 1  the critical point sigma_0 with R(sigma_0) = 2")
    s0 = findroot(lambda s: R(s) - 2, mp.mpf("2.45"))
    print(f"    sigma_0 = {mp.nstr(s0, 12)}   R(sigma_0) = {mp.nstr(R(s0), 12)}")
    ok1 = abs(R(s0) - 2) < mp.mpf("1e-20")
    print(f"  -> {'PASS' if ok1 else 'FAIL'}\n")

    print("CONTROL 2  the continuant recursion is the continued-fraction denominator")
    okK = control_continuant()
    print(f"    all words over digits 1..9 of length <= 4: {okK}")
    print(f"  -> {'PASS' if okK else 'FAIL'}\n")

    print("CONTROL 3  the totient identity used in the proof")
    lhs = control_totient_series(s0)
    print(f"    1 + sum phi(q) q^-s = {mp.nstr(lhs, 10)}   R(s) = {mp.nstr(R(s0), 10)}")
    ok2 = abs(lhs - R(s0)) < mp.mpf("0.01")
    print(f"    (truncated series, so agreement to a few digits is the expectation)")
    print(f"  -> {'PASS' if ok2 else 'FAIL'}\n")

    print("CONTROL 4  every canonical word of digit sum m>1 has exactly two expansions")
    ok3 = control_two_expansions()
    print(f"    checked m = 2..12: {ok3}")
    print(f"  -> {'PASS' if ok3 else 'FAIL'}\n")

    if not (ok1 and okK and ok2 and ok3):
        print("Controls failed. No conclusion about the coefficient.")
        return 1

    paper = 2 * R(s0) ** 2
    dush = R(s0) + 2 * R(s0) ** 2
    print(f"CLAIM  n^s Z_n(s) -> {mp.nstr(paper, 8)} (this paper) "
          f"or {mp.nstr(dush, 8)} (Dushistova)\n")

    rows = []
    for n in range(4, 23):
        z = continuant_sum(n, s0)
        val = mp.mpf(n) ** s0 * z
        rows.append((n, val))
        if n >= 15:
            print(f"    n={n:3d}   n^s Z_n = {mp.nstr(val, 10)}")

    print("\n    Richardson extrapolation at the paper's stated n^{-1} rate:")
    for i in range(len(rows) - 1):
        n1, v1 = rows[i]
        n2, v2 = rows[i + 1]
        ext = (n2 * v2 - n1 * v1) / (n2 - n1)
        if n2 >= 17:
            print(f"        from n={n1},{n2}:  {mp.nstr(ext, 10)}")
    n1, v1 = rows[-2]
    n2, v2 = rows[-1]
    final = (n2 * v2 - n1 * v1) / (n2 - n1)
    dp, dd = abs(final - paper), abs(final - dush)
    print(f"\n    extrapolated limit {mp.nstr(final, 10)}")
    print(f"        distance to {mp.nstr(paper, 6)} (paper)      : {mp.nstr(dp, 6)}")
    print(f"        distance to {mp.nstr(dush, 6)} (Dushistova) : {mp.nstr(dd, 6)}")
    verdict = "paper" if dp < dd else "Dushistova"
    print(f"    -> the data favour: {verdict}")
    return 0 if verdict == "paper" else 1


if __name__ == "__main__":
    sys.exit(main())
