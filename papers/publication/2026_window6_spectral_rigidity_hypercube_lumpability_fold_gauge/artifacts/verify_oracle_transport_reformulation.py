#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent check of the Oracle's matching-free transport reformulation.

Transcript: oracle_sprint_TWOSTAR_r2.md, task 2baffd6b. It was saved unreviewed; this is the
review.

Why it matters. At t438 I found my own follow-up question circular: the two-coordinate shape
of the u_i follows from D already having the carry-free two-power form, so proving it cannot
establish what D is. This reformulation is built to avoid that. Nothing in it presupposes the
shape of D.

Setup. R_m(n) is the numerical fold. With T(r) the breakpoints, R_m(T(r) + y) = y for
0 <= y < T(r+1) - T(r). For a vertex n and a colour y,

    E_y(n) = { (n XOR 2^i) - y : R_m(n XOR 2^i) = y },

a set of breakpoints. The star equality is |E_y(a)| = |E_y(b)| for every y.

Claims checked here, on every actual collision at m = 6..10:

  (P) transport <=> decomposition: E_y(a) = C_y + L_y and E_y(b) = C_y + (L_y + D), disjointly
  (2) sum_y |C_y| = 2 and sum_y |L_y| = m - 2
  (6) residue conservation: |E_y(a) cap (c + DZ)| = |E_y(b) cap (c + DZ)| for every c mod D
  (8) the D-chain criterion S_k in {0,1} and S_k <= A_k, with S_k the prefix imbalance
  (9) the forced construction L_k = S_k, C_k = A_k - S_k really does reproduce (P)
  and finally that the matching induced by the construction is VALID and has exactly two
  u_i = -D, which is the step that makes the argument non-circular: D = p_i - q_{pi(i)} is
  then a difference of two powers of two as a CONSEQUENCE, not an assumption.

Discriminating control. Claims that hold on collisions are worthless if they also hold on
non-collisions. Every check is therefore repeated on pairs (a, b) that share a fold value but
have DIFFERENT stars, i.e. are not collisions. The criterion must fail there. Without that
control, a criterion that is simply always true would pass everything above.
"""
import sys
from itertools import permutations

FIB = [0, 1, 1]
while len(FIB) < 120:
    FIB.append(FIB[-1] + FIB[-2])


def zeck_digits(n):
    if n == 0:
        return set()
    k = 2
    while FIB[k + 1] <= n:
        k += 1
    out, rest = set(), n
    while rest > 0:
        while FIB[k] > rest:
            k -= 1
        out.add(k)
        rest -= FIB[k]
        k -= 1
    return out


def fold_value(n, m):
    return sum(FIB[k] for k in zeck_digits(n) if 2 <= k <= m + 1)


def E(n, m, fold):
    """colour -> set of breakpoint bases of the neighbours of that colour."""
    out = {}
    for i in range(m):
        nb = n ^ (1 << i)
        y = fold[nb]
        out.setdefault(y, set()).add(nb - y)
    return out


def collisions_and_controls(m):
    N = 1 << m
    fold = [fold_value(n, m) for n in range(N)]
    star = {}
    for n in range(N):
        s = tuple(sorted(fold[n ^ (1 << i)] for i in range(m)))
        star.setdefault((fold[n], s), []).append(n)
    cols = []
    for g in star.values():
        for x in range(len(g)):
            for y in range(x + 1, len(g)):
                cols.append((g[x], g[y]))
    # controls: same fold value, different star
    byfold = {}
    for n in range(N):
        byfold.setdefault(fold[n], []).append(n)
    ctrl = []
    for v, g in byfold.items():
        for x in range(len(g)):
            for y in range(x + 1, len(g)):
                a, b = g[x], g[y]
                sa = tuple(sorted(fold[a ^ (1 << i)] for i in range(m)))
                sb = tuple(sorted(fold[b ^ (1 << i)] for i in range(m)))
                if sa != sb:
                    ctrl.append((a, b))
    return cols, ctrl, fold


def residue_conservation(Ea, Eb, D):
    for y in set(Ea) | set(Eb):
        A, B = Ea.get(y, set()), Eb.get(y, set())
        ca, cb = {}, {}
        for z in A:
            ca[z % D] = ca.get(z % D, 0) + 1
        for z in B:
            cb[z % D] = cb.get(z % D, 0) + 1
        if ca != cb:
            return False
    return True


def chain_transport(Ea, Eb, D):
    """Apply criterion (8) and construction (9). Returns (ok, C, L) with C, L dicts y->set."""
    C, L = {}, {}
    for y in set(Ea) | set(Eb):
        A, B = Ea.get(y, set()), Eb.get(y, set())
        if len(A) != len(B):
            return False, None, None
        Cy, Ly = set(), set()
        for c in range(D):
            ks = sorted({(z - c) // D for z in A if z % D == c} |
                        {(z - c) // D for z in B if z % D == c})
            if not ks:
                continue
            S = 0
            for k in range(min(ks), max(ks) + 1):
                Ak = 1 if (c + k * D) in A else 0
                Bk = 1 if (c + k * D) in B else 0
                S += Ak - Bk
                if S not in (0, 1) or S > Ak:
                    return False, None, None
                if S == 1:
                    Ly.add(c + k * D)
                elif Ak == 1:
                    Cy.add(c + k * D)
            if S != 0:
                return False, None, None
        # verify the decomposition actually holds
        if Cy | Ly != A or (Cy & Ly):
            return False, None, None
        if Cy | {z + D for z in Ly} != B or (Cy & {z + D for z in Ly}):
            return False, None, None
        C[y], L[y] = Cy, Ly
    return True, C, L


def induced_matching_is_valid(a, b, m, fold, C, L, D):
    """Build the matching from the construction and check validity plus the u-shape."""
    pi = {}
    used = set()
    for y in C:
        for z in C[y]:
            src, tgt = z + y, z + y          # same actual integer
            i = (src ^ a).bit_length() - 1
            j = (tgt ^ b).bit_length() - 1
            if src ^ a != 1 << i or tgt ^ b != 1 << j or j in used:
                return False, None
            pi[i] = j
            used.add(j)
        for z in L[y]:
            src, tgt = z + y, z + D + y
            i = (src ^ a).bit_length() - 1
            j = (tgt ^ b).bit_length() - 1
            if src ^ a != 1 << i or tgt ^ b != 1 << j or j in used:
                return False, None
            pi[i] = j
            used.add(j)
    if len(pi) != m:
        return False, None
    if any(fold[a ^ (1 << i)] != fold[b ^ (1 << pi[i])] for i in range(m)):
        return False, None
    p = [(1 - 2 * ((a >> i) & 1)) * 2 ** i for i in range(m)]
    q = [(1 - 2 * ((b >> j) & 1)) * 2 ** j for j in range(m)]
    u = [q[pi[i]] - p[i] for i in range(m)]
    return True, u


def main():
    print("Check of the transport reformulation, oracle_sprint_TWOSTAR_r2.md\n")
    ok_all = True
    ctrl_all_fail = True
    for m in (6, 7, 8, 9, 10):
        cols, ctrl, fold = collisions_and_controls(m)
        nres = nchain = nvalid = nshape = 0
        for a, b in cols:
            if a > b:
                a, b = b, a
            D = b - a
            Ea, Eb = E(a, m, fold), E(b, m, fold)
            if residue_conservation(Ea, Eb, D):
                nres += 1
            good, C, L = chain_transport(Ea, Eb, D)
            if not good:
                continue
            nchain += 1
            if sum(len(v) for v in C.values()) == 2 and \
               sum(len(v) for v in L.values()) == m - 2:
                nshape += 1
            valid, u = induced_matching_is_valid(a, b, m, fold, C, L, D)
            if valid and sorted(v for v in u if v != 0) == [-D, -D]:
                nvalid += 1
        n = len(cols)
        print("    m=%2d  %3d collisions" % (m, n))
        print("          (6) residue conservation        : %d/%d" % (nres, n))
        print("          (8) chain criterion holds       : %d/%d" % (nchain, n))
        print("          (2) |C|=2 and |L|=m-2           : %d/%d" % (nshape, n))
        print("          induced matching valid, u shape : %d/%d" % (nvalid, n))
        ok_all &= (nres == n == nchain == nshape == nvalid)

        # discriminating control
        bad = 0
        for a, b in ctrl:
            if a > b:
                a, b = b, a
            D = b - a
            if D == 0:
                continue
            g, _, _ = chain_transport(E(a, m, fold), E(b, m, fold), D)
            if g:
                bad += 1
        print("          CONTROL non-collisions passing  : %d/%d  %s"
              % (bad, len(ctrl), "(must be 0)" if bad == 0 else "<-- criterion is vacuous"))
        ctrl_all_fail &= (bad == 0)

    print()
    print("SUMMARY", {"all claims hold on collisions": ok_all,
                      "criterion rejects non-collisions": ctrl_all_fail})
    return 0 if (ok_all and ctrl_all_fail) else 1


if __name__ == "__main__":
    sys.exit(main())
