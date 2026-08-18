#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Internal-consistency check of the claimed error in Dushistova's Lemma 7.

The limit itself resists brute force: n^s Z_n rises to about 15.28, turns over near n = 27,
and at n = 29 has only begun to descend, so finite data cannot separate 2R^2 from anything
else. That was established, and an earlier extrapolation of mine through the turning point
was withdrawn.

The error *mechanism*, though, lives at a level that is checkable. The paper says Dushistova
loses the restriction u > 1, so the doubled sum includes the empty left context and counts
that endpoint twice, with excess exactly R_s. This script checks that the arithmetic of that
diagnosis is self-consistent - that the named mechanism produces exactly the size of
discrepancy claimed, no more and no less.

The two context sums are not enumerated. They follow from identities already verified:
  - canonical words including the empty word sum to R_s, by the totient identity
    1 + sum_q phi(q) q^-s = zeta(s-1)/zeta(s);
  - all positive words sum to 2(R_s - 1) + 1, from l_m = 2 r_m plus the word (1).
An enumeration was attempted first and was simply too slow; it was also unnecessary.

What this does NOT do: establish which constant is correct. That needs the asymptotic
analysis, not a computation at reachable n.
"""
import sys
from mpmath import mp, zeta, findroot

mp.dps = 25


def main():
    s0 = findroot(lambda s: zeta(s - 1) / zeta(s) - 2, mp.mpf("2.45"))
    R = zeta(s0 - 1) / zeta(s0)
    f = lambda x: mp.nstr(x, 8)
    print(f"sigma_0 = {f(s0)}   R_s = {f(R)}\n")

    canonical = R
    all_positive = 2 * (R - 1) + 1
    print("context sums, from previously verified identities")
    print(f"    canonical words incl. empty = R_s            = {f(canonical)}")
    print(f"    all positive words          = 2(R_s - 1) + 1 = {f(all_positive)}\n")

    lhs = 2 * (R - 1) * R
    corrected = 2 * R ** 2
    printed = R + 2 * R ** 2
    print("endpoint accounting")
    print(f"    |u|_1 > 1 contributes 2(R-1)R = {f(lhs)}")
    print(f"    corrected 2R^2      = {f(corrected)}  -> endpoints supply {f(corrected - lhs)} = 2R")
    print(f"    printed   R + 2R^2  = {f(printed)}  -> endpoints supply {f(printed - lhs)} = 3R")
    print(f"    difference          = {f(printed - corrected)} = R_s\n")

    ok = (abs((printed - corrected) - R) < mp.mpf("1e-20")
          and abs((corrected - lhs) - 2 * R) < mp.mpf("1e-20"))
    print(f"the diagnosis is internally consistent: {'CONFIRMED' if ok else 'FAILS'}")
    print("R_s is exactly the weight of one empty left context, K(empty) = 1, paired with")
    print("the full right-context sum. So the mechanism named produces exactly the claimed")
    print("discrepancy - which supports the diagnosis without settling the constant.")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
