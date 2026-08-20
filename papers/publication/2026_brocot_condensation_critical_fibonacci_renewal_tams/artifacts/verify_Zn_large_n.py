#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Push Z_n(sigma_0) far enough to identify the convergence rate.

t457 left the paper's headline unresolved. Three scripts fail to reproduce b_C = 8; the
measured level is around 14 and still rising; and the two extrapolation fits disagree (16.89
against 20.38), which means the convergence RATE is unidentified. With an unidentified rate no
limit can be read off, so nothing can be concluded either way. The only way through is larger n.

The existing computation enumerates all 2^(n-1) compositions and dies around n = 22. This one
uses the Stern-Brocot structure instead.

Writing (u, v) = (K_{r-1}, K_r) for the continuant pair of a word, there are exactly two moves,
each consuming one unit of digit sum:

    A   start a new digit:        (u, v) -> (v, u + v)
    B   extend the current digit: (u, v) -> (u, u + v)

Every word of digit sum n is a unique length-n sequence of moves, which is the Stern-Brocot
bijection. A word is canonical, meaning its last digit is at least 2, exactly when its final
move is B, since a digit only exceeds 1 by being extended.

That is still 2^n paths, so the sum is truncated on v. This is safe because the truncation
error is bounded rigorously rather than assumed small: a pair dropped at step t with value v
has exactly 2^(n-t-1) descendants at step n, and every one of them has continuant at least v,
so its total contribution is at most 2^(n-t-1) * v^(-s). Those bounds are accumulated and
reported alongside the answer. If the reported bound is not far below the answer, the run says
so and the number is not used.

Exact integers throughout for the continuants; the final power sum is 50-digit decimal.
"""
import sys

from mpmath import mp, mpf

mp.dps = 50
SIGMA0 = mpf("2.4787507857339602606714872614")


def Zn(n, s=SIGMA0, vmax=200000):
    """Returns (Z_n, rigorous_error_bound, distinct_keys).

    States carry MULTIPLICITY. The continuant pair does not identify the word: at n = 5 the
    words (1,4) and (5) both have pair (1,5) and both end with move B, so a set-based walk
    silently merges them. That halved the sum and would have produced a false agreement with
    the paper -- brute force at n = 4..7 caught it, giving exactly 2x the set-based walk.

    Move B is also forbidden before the first digit exists, since from the empty word (0,1) it
    maps (0,1) -> (0,1), a self-loop leaking earlier levels into level n.
    """
    from collections import defaultdict
    states = {(0, 1, False): 1}
    started = False
    err = mpf(0)
    for t in range(n):
        nxt = defaultdict(int)
        remaining = n - t - 1
        for (u, v, _), mult in states.items():
            moves = (((v, u + v), False),) if not started else                     (((v, u + v), False), ((u, u + v), True))
            for (a, b), isB in moves:
                if b <= vmax:
                    nxt[(a, b, isB)] += mult
                else:
                    err += mult * mpf(2) ** remaining * mpf(b) ** (-s)
        states = nxt
        started = True
    total = mpf(0)
    for (u, v, isB), mult in states.items():
        if isB:
            total += mult * mpf(v) ** (-s)
    return total, err, len(states)


SAFE_TOP, SAFE_VMAX = 22, 20000


def main():
    """Defaults are deliberately small.

    Run bare, this script now stops at n = 22 with vmax = 20000, which finishes in seconds in
    a few hundred MB. The previous defaults of n = 34 and vmax = 200000 consumed 4.4 GB and
    drove the machine to 0.35 GB free with hard faults above 5000/sec; that happened when an
    agent was told to run every script in this directory and dutifully ran this one. The cost
    is real and the warning that used to sit only in a comment at the end of the file was not
    seen in time.

    Pass explicit arguments to go further, e.g. `verify_Zn_large_n.py 26 60000`, and watch
    memory while it runs. n = 24 at vmax = 60000 is comfortable; n = 30 at vmax = 400000 is
    not.
    """
    top = int(sys.argv[1]) if len(sys.argv) > 1 else SAFE_TOP
    vmax = int(sys.argv[2]) if len(sys.argv) > 2 else SAFE_VMAX
    if len(sys.argv) <= 1:
        print("running with safe defaults n <= %d, vmax = %d; pass arguments to go further"
              % (SAFE_TOP, SAFE_VMAX))
        print()
    print("Z_n(sigma_0) by Stern-Brocot walk, truncated at v <= %d" % vmax)
    print("sigma_0 = %s\n" % mp.nstr(SIGMA0, 20))
    print("     n        n^s Z_n      error bound   ratio    states")
    prev = None
    vals = []
    for n in range(12, top + 1):
        z, err, k = Zn(n, vmax=vmax)
        val = mpf(n) ** SIGMA0 * z
        ebound = mpf(n) ** SIGMA0 * err
        rel = ebound / val if val else mpf(1)
        vals.append((n, val))
        flag = "" if rel < mpf("1e-3") else "   <-- error bound too large, value unusable"
        d = "" if prev is None else "  d=%s" % mp.nstr(val - prev, 4)
        print("    %2d   %s   %s   %s   %d%s%s"
              % (n, mp.nstr(val, 10), mp.nstr(ebound, 4), mp.nstr(rel, 3), k, d, flag))
        prev = val

    print("\n  increments and their ratios, to identify the rate:")
    for i in range(2, len(vals)):
        n0, v0 = vals[i - 2]
        n1, v1 = vals[i - 1]
        n2, v2 = vals[i]
        d1, d2 = v1 - v0, v2 - v1
        if d1:
            print("    n=%2d  increment %s  ratio %s" % (n2, mp.nstr(d2, 6), mp.nstr(d2 / d1, 6)))

    print("\n  If the ratios approach a constant below 1 the tail is geometric and the limit")
    print("  can be summed. If they approach 1 the decay is polynomial and the exponent must")
    print("  be fitted before any limit is claimed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())


# ---------------------------------------------------------------------------
# WHERE THIS METHOD STOPS, AND WHY THE OBVIOUS TIGHTENING FAILS.
#
# Reached in practice: n = 24 with vmax = 60000, error ratio 1e-7, comfortably. Attempting
# n = 30 with vmax = 400000 took roughly 3 GB and had to be killed under the memory rule. So
# the walk buys a few values beyond the n = 22 ceiling of the plain enumeration, not the
# order of magnitude that identifying the convergence rate needs.
#
# The binding constraint is the truncation bound, which is
#
#     contribution of a pair dropped at step t  <=  2^(n-t-1) * v^(-s).
#
# It is very lossy, because almost all of those 2^(n-t-1) descendants have continuants far
# larger than v. The natural fix is to replace v by a growth lower bound: if a descendant k
# steps on had continuant at least v * g^k for some g > 1, the bound would become
# v^(-s) * sum_k (2 g^(-s))^k, which converges as soon as g^s > 2 and would let vmax be small.
#
# That fix does not work here, and the reason is worth recording. Continuant growth along this
# walk is NOT geometric in the worst case. Move B sends (u, v) to (u, u+v), leaving u
# unchanged, so from (1, v) repeated B gives (1, v+1), (1, v+2), ... - the words (1, a) with a
# increasing. Along that branch v grows LINEARLY, not geometrically, so no g > 1 exists and
# the geometric bound is unavailable. Any real improvement has to treat that branch separately
# rather than bound it uniformly.
#
# Identifying the rate therefore needs a different instrument: a transfer-operator or
# Gauss-map spectral treatment, where the subleading eigenvalue gives the rate directly
# instead of being read off finite differences. That is beyond what this script attempts, and
# the honest status is that the rate remains unidentified and the constant unresolved.
