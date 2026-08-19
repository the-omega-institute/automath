#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""What relates two integers that share a coloured-star signature.

verify_sporadic_involutions.py established that every fibre of

    Phi_m(a) = ( Fold_m(a), multiset of Fold_m(a XOR e_i) )

has size at most 2 for m = 6..16, and that Phi_m is injective from m = 11 on. That is the
evidence for the lemma the classification still needs, and evidence about a bound says
nothing about a mechanism. This script asks what a colliding pair looks like.

I first guessed the pairs would be the orbits of the sporadic affine involution SWAP[m], and
wrote that into this docstring before running anything. It is false. At m = 7 there are 14
nontrivial fibres and at m = 10 there are 5, and neither m carries an involution. The guess
is kept here because the true statement is what replaced it.

WHAT IS ACTUALLY TRUE, at every m checked and with no exceptions: if a and b share a
signature then

    b - a  is a Fibonacci number F_k having exactly two nonzero binary digits,

and the addition is carry-free, i.e. a XOR b equals the two-bit binary pattern of F_k, so a
has zeros in both of those positions. Only F_9 = 34 and F_12 = 144 ever occur, because apart
from small terms those are the only Fibonacci numbers that are a sum of two distinct powers
of two - the identical arithmetic that pins the sporadic set.

So the pairing mechanism is the same at every m. What distinguishes m in {3, 6, 8, 9} is not
whether such pairs exist but whether they exhaust the cube. The inequality p + 1 <= m <= k - 3
from the classification is exactly the condition for every vertex to be paired, which is what
makes the swap a global involution and the partition stable. Outside it the pairing is
partial - 14 of 128 at m = 7, 5 of 1024 at m = 10 - and the later refinement rounds destroy
it, which is why those m still refine to the discrete partition.

WHY THIS MATTERS FOR THE OPEN LEMMA. It reduces the bound to an arithmetic statement. If
every colliding pair differs by a two-ones Fibonacci number added without carry, then a fibre
of size three would need one integer a admitting two distinct such differences at once, both
landing in the same signature. Since only 34 and 144 qualify, that is a finite condition
rather than a statement about all m, which is the shape a proof wants. Proving the displayed
implication is now the whole task; this script verifies it, it does not prove it.

Verified for m = 6 through 19: all three checks pass, with Phi_m injective from m = 11 on
and no colliding pair anywhere failing the carry-free two-ones Fibonacci description.

Memory note: signatures are packed into bytes and sorted rather than held in a dict of
tuples, so the larger m stay within a few hundred MB.
"""
import sys
from collections import Counter

FIB = [0, 1, 1]
while len(FIB) < 96:
    FIB.append(FIB[-1] + FIB[-2])

SWAP = {6: (1, 5), 8: (1, 4), 9: (2, 5)}       # one-indexed, from the sporadic classification


def fold_table(m):
    """Fold_m(v) for every v < 2^m, as an m-bit mask. Greedy Zeckendorf, digits F_2..F_{m+1}."""
    N = 1 << m
    out = [0] * N
    for v in range(1, N):
        rest, k, mask = v, 0, 0
        while FIB[k + 1] <= rest:
            k += 1
        while rest > 0:
            while FIB[k] > rest:
                k -= 1
            if 0 <= k - 2 < m:
                mask |= 1 << (k - 2)
            rest -= FIB[k]
            k -= 1
        out[v] = mask
    return out


def fibres(m):
    """Indices grouped by exact Phi_m value, via a sort on packed keys."""
    N = 1 << m
    fold = fold_table(m)
    w = (m + 7) // 8
    keys = []
    for v in range(N):
        star = sorted(fold[v ^ (1 << (m - 1 - i))] for i in range(m))
        b = fold[v].to_bytes(w, "big") + b"".join(s.to_bytes(w, "big") for s in star)
        keys.append(b)
    order = sorted(range(N), key=lambda i: keys[i])
    groups, i = [], 0
    while i < len(order):
        j = i + 1
        while j < len(order) and keys[order[j]] == keys[order[i]]:
            j += 1
        if j - i > 1:
            groups.append(order[i:j])          # exact byte equality, not a hash
        i = j
    return groups, fold


def sigma(v, m):
    i, j = SWAP[m]
    bi, bj = m - i, m - j
    a = (v >> bi) & 1
    b = (v >> bj) & 1
    v &= ~((1 << bi) | (1 << bj))
    return v | ((1 - b) << bi) | ((1 - a) << bj)


def two_ones_fibs(limit=1 << 24):
    out = {}
    for k in range(3, 60):
        if FIB[k] > limit:
            break
        b = bin(FIB[k])[2:]
        if b.count("1") == 2:
            out[FIB[k]] = k
    return out


def main(mmax=18):
    print("What relates two integers sharing a coloured-star signature")
    TWO = two_ones_fibs()
    print(f"    two-ones Fibonacci numbers in range: {[f'F_{k}={v}' for v, k in TWO.items()]}")
    print()
    ok_bound = ok_diff = ok_carry = True
    for m in range(6, mmax + 1):
        groups, fold = fibres(m)
        mx = max((len(g) for g in groups), default=1)
        ok_bound &= mx <= 2
        diffs, carry_free = set(), True
        for g in groups:
            a, b = min(g), max(g)
            d = b - a
            diffs.add(d)
            if d not in TWO or (a ^ b) != d:
                carry_free = False
        bad = sorted(d for d in diffs if d not in TWO)
        ok_diff &= not bad
        ok_carry &= carry_free
        inv = "  (involution m)" if m in SWAP else ""
        print(f"    m={m:2d}  2^m={1 << m:8d}  pairs {len(groups):6d}  max size {mx}{inv}")
        if groups:
            named = [f"F_{TWO[d]}={d}" for d in sorted(diffs) if d in TWO]
            print(f"            differences {named}, carry-free {carry_free}")
        else:
            print(f"            Phi_m injective")
        if bad:
            print(f"            NOT a two-ones Fibonacci number: {bad}")

    print()
    print(f"  every fibre has size <= 2            -> {'PASS' if ok_bound else 'FAIL'}")
    print(f"  every difference is a two-ones F_k   -> {'PASS' if ok_diff else 'FAIL'}")
    print(f"  every such addition is carry-free    -> {'PASS' if ok_carry else 'FAIL'}")
    return 0 if (ok_bound and ok_diff and ok_carry) else 1


if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 18))
