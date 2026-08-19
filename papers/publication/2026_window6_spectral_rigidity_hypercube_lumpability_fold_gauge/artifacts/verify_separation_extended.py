#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Push the residual-separation certificate well past the Oracle's m = 1000.

The Oracle's argument (oracle_sprint_TWOSTAR_r1.md) leaves exactly one gap: the p-adic
Subspace Theorem gives injectivity of Phi_m for all sufficiently large m, but the cutoff is
ineffective, so a finite and currently unlocated interval above its certified range could in
principle contain a failure. Nothing can close that gap except an effective bound - but every
additional m that is certified shrinks the interval where a failure could hide.

The certificate itself is cheap and exact. For each signed power p in {+-2^i : i < m} the
residual set is

    C_m(p) = { p - A h - B (floor(h/phi) + eps) : |.| < L },  A = F_{m+1}, B = F_m, L = F_{m+2},

with eps in {0} for h = 0 and {0,1} otherwise, and only the handful of h near p/phi^m
contributing. If the C_m(p) are pairwise disjoint then Phi_m is injective. That implication
was verified independently in verify_oracle_sawtooth_reduction.py, including the check that
the criterion never fires where Phi_m actually fails to be injective.

Disjointness is tested here by inserting every residual into one dictionary per m and looking
for a repeat, which is O(m) per m rather than the O(m^2) of pairwise set intersection. All
arithmetic is exact integer arithmetic; floor(h/phi) is (isqrt(5h^2) - h)//2 for h >= 0.

Run with a single integer argument to set the upper limit.
"""
import sys
from math import isqrt

FIB = [0, 1, 1]


def extend_fib(n):
    while len(FIB) <= n + 2:
        FIB.append(FIB[-1] + FIB[-2])


def floor_div_phi(h):
    if h >= 0:
        return (isqrt(5 * h * h) - h) // 2
    return -floor_div_phi(-h) - 1


def separated(m):
    """True if the residual sets are pairwise disjoint. Returns (ok, witness)."""
    A, B, L = FIB[m + 1], FIB[m], FIB[m + 2]
    seen = {}
    for i in range(m):
        for p in (1 << i, -(1 << i)):
            centre = p // (A + B)
            for h in range(centre - 3, centre + 4):
                base = A * h + B * floor_div_phi(h)
                for eps in ((0,) if h == 0 else (0, 1)):
                    c = p - base - B * eps
                    if -L < c < L:
                        prev = seen.get(c)
                        if prev is not None and prev != p:
                            return False, (prev, p, c)
                        seen[c] = p
    return True, None


def main():
    top = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
    extend_fib(top)
    print("Residual separation certificate, exact integer arithmetic")
    print("m = 13 .. %d\n" % top)
    failures = []
    for m in range(13, top + 1):
        ok, wit = separated(m)
        if not ok:
            failures.append((m, wit))
        if m % 500 == 0:
            print("    ... through m = %d, %d failures so far" % (m, len(failures)))
    print()
    if failures:
        print("    FAILURES: %d" % len(failures))
        for m, w in failures[:10]:
            print("        m=%d: powers %s and %s share residual %s" % (m, w[0], w[1], w[2]))
    else:
        print("    all %d values separated, so Phi_m is injective for every 13 <= m <= %d"
              % (top - 12, top))
    print()
    print("    The gap that remains is above m = %d, and it is a gap in effectivity," % top)
    print("    not in computation: no finite range can close it.")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
