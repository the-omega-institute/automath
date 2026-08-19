#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Verify the multiplication-delay lower bound, which is what this paper actually is.

The referee assessment was explicit: "The referee will treat the multiplication-delay theorem
as the paper. The ring structure will be treated as notation and motivation." I had told that
referee I had not verified this theorem. This script does.

THEOREM. In the most-significant-digit-first convention, if a machine at effective resolution
n reads padded synchronous inputs and, after position i is read, every output coordinate at
position at least i + delta_n is irrevocably determined, and if it computes the stable product
for every pair in X_n x X_n, then delta_n >= n - 1 for every n >= 3.

The proof exhibits c = Z(F_{n+1}), c' = Z(F_{n+1} + 1), d = Z(F_{n+1}). Four things must hold
and all are checked here for n = 3..24:

  1. c, c', d are admissible words of X_n;
  2. c and c' agree at every position except position 1, so the two synchronous input streams
     differ only there;
  3. the stable products are exact with no reduction, Val(u) = F_{n+1}^2 and
     Val(u') = (F_{n+1}+1) F_{n+1} - this is a product in (X_inf, plus, times), isomorphic to
     the naturals, so no modular reduction enters;
  4. the two output Zeckendorf words differ at some position k >= n.

Given 4, agreement at every k >= 2 + delta_n forces 2 + delta_n > n, hence delta_n >= n-1.

The supporting lemma - an admissible word supported on positions 1..n-1 has value at most
F_{n+1} - 1 - is re-checked exhaustively for n = 3..19.
"""
import sys
from itertools import product

FIB = [0, 1, 1]
while len(FIB) < 200:
    FIB.append(FIB[-1] + FIB[-2])


def Z(n):
    """Zeckendorf support as a set of positions j, where position j carries weight F_{j+1}."""
    out = set()
    if n == 0:
        return out
    k = 2
    while FIB[k + 1] <= n:
        k += 1
    r = n
    while r > 0:
        while FIB[k] > r:
            k -= 1
        out.add(k - 1)
        r -= FIB[k]
        k -= 1
    return out


def val(S):
    return sum(FIB[j + 1] for j in S)


def admissible(S):
    return all((j + 1) not in S for j in S)


def main():
    print("witness check, n = 3..24")
    ok = True
    for n in range(3, 25):
        c, cp, d = Z(FIB[n + 1]), Z(FIB[n + 1] + 1), Z(FIB[n + 1])
        in_Xn = all(admissible(S) and (not S or max(S) <= n) for S in (c, cp, d))
        agree = (c ^ cp) == {1}
        u, up = Z(FIB[n + 1] ** 2), Z((FIB[n + 1] + 1) * FIB[n + 1])
        exact = val(u) == FIB[n + 1] ** 2 and val(up) == (FIB[n + 1] + 1) * FIB[n + 1]
        differ_high = any(k >= n for k in (u ^ up))
        good = in_Xn and agree and exact and differ_high
        ok &= good
        if n <= 6 or n >= 23:
            print(f"    n={n:2d}: admissible {in_Xn}, differ only at position 1 {agree}, "
                  f"values exact {exact}, outputs differ at some k>=n {differ_high}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")

    print("supporting lemma, n = 3..19")
    bad = 0
    for n in range(3, 20):
        best = 0
        for bits in product((0, 1), repeat=n - 1):
            S = {j + 1 for j, b in enumerate(bits) if b}
            if admissible(S):
                best = max(best, val(S))
        if best != FIB[n + 1] - 1:
            bad += 1
    print(f"    admissible words on positions 1..n-1 attain exactly F_(n+1)-1: "
          f"{bad} violations")
    print(f"  -> {'PASS' if bad == 0 else 'FAIL'}\n")

    print("Outputs must agree at every k >= 2 + delta_n; they differ at some k >= n;")
    print("therefore 2 + delta_n > n, that is delta_n >= n - 1.")
    return 0 if (ok and bad == 0) else 1


if __name__ == "__main__":
    sys.exit(main())
