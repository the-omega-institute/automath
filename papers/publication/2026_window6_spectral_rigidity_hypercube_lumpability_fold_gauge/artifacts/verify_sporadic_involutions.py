#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Verification of the sporadic affine repairs at m = 6, 8, 9, and of eventual rigidity.

The referee desk-rejected this paper for treating one fixed partition of one 64-vertex graph
and asked for an infinite family. There is no infinite family. What there is, verified here,
is a complete sporadic classification.

For each m the fold sends a binary word to the first m digits of the greedy Zeckendorf
expansion of its binary value. Colour-refining that partition on the hypercube gives:

  m = 6   21 -> 48        m = 7   34 -> 114 -> 125 -> 128, discrete
  m = 8   55 -> 192       m = 9   89 -> 384
  m = 10..16                      discrete

The three nontrivial cases are exactly the ones where two binary weights sum to a Fibonacci
number, since "swap two positions and complement both" then adds or subtracts that Fibonacci
number without carry:

  m = 6   positions 1,5   32 + 2   = 34  = F_9
  m = 8   positions 1,4   128 + 16 = 144 = F_12
  m = 9   positions 2,5   128 + 16 = 144 = F_12

Apart from small terms the only Fibonacci numbers with two nonzero binary digits are 34 and
144, which is why the family stops.

The closed form is not in the paper and was not stated in the referee exchange either: in all
three cases the refinement has exactly 2^(m-1) singletons and 2^(m-2) pairs, so

    number of cells = 3 * 2^(m-2),

giving 48, 192 and 384. The involution fixes exactly half the cube.
"""
import sys
from itertools import product

FIB = [0, 1, 1]
while len(FIB) < 80:
    FIB.append(FIB[-1] + FIB[-2])

SWAP = {6: (1, 5), 8: (1, 4), 9: (2, 5)}       # one-indexed positions


def zeck_prefix(n, m):
    if n == 0:
        return (0,) * m
    ks, rest, k = [], n, 2
    while FIB[k + 1] <= n:
        k += 1
    while rest > 0:
        while FIB[k] > rest:
            k -= 1
        ks.append(k)
        rest -= FIB[k]
        k -= 1
    out = [0] * m
    for k in ks:
        if 0 <= k - 2 < m:
            out[k - 2] = 1
    return tuple(out)


def value(v, m):
    return sum(a * 2 ** (m - 1 - r) for r, a in enumerate(v))


def sigma(v, m):
    i, j = SWAP[m]
    w = list(v)
    w[i - 1] = 1 - v[j - 1]
    w[j - 1] = 1 - v[i - 1]
    return tuple(w)


def refinement(m):
    V = list(product((0, 1), repeat=m))
    idx = {v: i for i, v in enumerate(V)}
    nbr = [[idx[v[:b] + (1 - v[b],) + v[b + 1:]] for b in range(m)] for v in V]
    lab = [zeck_prefix(value(v, m), m) for v in V]
    cm = {}
    for L in lab:
        cm.setdefault(L, len(cm))
    c = [cm[L] for L in lab]
    while True:
        sig = [(c[i], tuple(sorted(c[j] for j in nbr[i]))) for i in range(len(V))]
        nm = {}
        for s in sig:
            nm.setdefault(s, len(nm))
        nc = [nm[s] for s in sig]
        if len(set(nc)) == len(set(c)):
            return V, c
        c = nc


def main():
    print("CONTROL  the swapped weights sum to a Fibonacci number")
    ok = True
    for m, (i, j) in SWAP.items():
        w = 2 ** (m - i) + 2 ** (m - j)
        hit = [k for k in range(3, 25) if FIB[k] == w]
        if not hit:
            ok = False
        print(f"    m={m}: {2**(m-i)} + {2**(m-j)} = {w}"
              f"   {'= F_' + str(hit[0]) if hit else 'NOT Fibonacci'}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")

    print("SPORADIC CASES  involution, fold-invariance, orbits equal the refinement")
    good = True
    for m in (6, 8, 9):
        V, c = refinement(m)
        inv = all(sigma(sigma(v, m), m) == v for v in V)
        keeps = all(zeck_prefix(value(sigma(v, m), m), m) == zeck_prefix(value(v, m), m)
                    for v in V)
        orb = {}
        for v in V:
            orb.setdefault(frozenset({v, sigma(v, m)}), len(orb))
        oc = [orb[frozenset({v, sigma(v, m)})] for v in V]
        same = all((oc[a] == oc[b]) == (c[a] == c[b])
                   for a in range(len(V)) for b in range(a + 1, len(V), 13))
        fixed = sum(1 for v in V if sigma(v, m) == v)
        pairs = (len(V) - fixed) // 2
        closed = (fixed == 2 ** (m - 1)) and (pairs == 2 ** (m - 2)) \
            and (len(set(c)) == 3 * 2 ** (m - 2))
        good &= inv and keeps and same and closed
        print(f"    m={m}: involution {inv}, fold-invariant {keeps}, "
              f"orbits match refinement {same}")
        print(f"          cells {len(set(c))} = 3*2^(m-2) {closed}; "
              f"{fixed} singletons = 2^(m-1), {pairs} pairs = 2^(m-2)")
    print(f"  -> {'PASS' if good else 'FAIL'}\n")

    print("RIGIDITY  every other m up to 16 refines to the discrete partition")
    rig = True
    for m in [7, 10, 11, 12, 13, 14, 15, 16]:
        V, c = refinement(m)
        d = len(set(c)) == len(V)
        rig &= d
        print(f"    m={m:2d}: {len(set(c))} cells of {len(V)}  {'discrete' if d else 'NOT'}")
    print(f"  -> {'PASS' if rig else 'FAIL'}")
    return 0 if (ok and good and rig) else 1


if __name__ == "__main__":
    sys.exit(main())


# ---------------------------------------------------------------------------
# Added after the enumeration: the two conditions pin m without enumerating.
#
# The mechanism needs a Fibonacci number F_k that is a sum of two distinct powers
# of two, F_k = 2^p + 2^q, placed so that
#
#   m >= p + 1     the larger power must fit inside an m-bit word, and
#   m <= k - 3     F_k must lie beyond the retained window F_2..F_{m+1}, separated
#                  from it by the omitted F_{m+2}, so the prefix is undisturbed.
#
# Those two inequalities are incompatible unless p + 1 <= k - 3. Running over all
# k gives F_4 and F_5 with empty ranges, F_9 = 34 with m = 6 alone, and F_12 = 144
# with m in {8, 9}. Nothing else. So the sporadic set is {6, 8, 9} by arithmetic,
# and the colour refinement above is corroboration rather than the argument.
#
# What this does NOT settle: whether a nontrivial coarsest equitable refinement
# could arise with no affine involution behind it at all. The argument here closes
# the involution mechanism only. That question is open.

def admissible_m(kmax=100):
    while len(FIB) <= kmax:
        FIB.append(FIB[-1] + FIB[-2])
    out = []
    for k in range(3, kmax + 1):
        b = bin(FIB[k])[2:]
        if b.count("1") != 2:
            continue
        pos = [len(b) - 1 - i for i, ch in enumerate(b) if ch == "1"]
        p, q = max(pos), min(pos)
        rng = list(range(p + 1, k - 3 + 1))
        out.append((k, FIB[k], p, q, rng))
    return out


def report_arithmetic_closure():
    print("\nARITHMETIC CLOSURE  the two conditions pin m without enumerating")
    ms = set()
    for k, f, p, q, rng in admissible_m():
        ms |= set(rng)
        print(f"    F_{k} = {f} = 2^{p} + 2^{q}  ->  m in {rng if rng else 'empty'}")
    print(f"    admissible m = {sorted(ms)}   (enumeration found 6, 8, 9)")
    return sorted(ms) == [6, 8, 9]
