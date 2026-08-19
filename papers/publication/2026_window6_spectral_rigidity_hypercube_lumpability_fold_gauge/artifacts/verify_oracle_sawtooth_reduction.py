#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent check of the Oracle's sawtooth reduction for the two-star lemma.

The Oracle (ChatGPT Pro, task 22e20d2a, transcript in oracle_sprint_TWOSTAR_r1.md) did not
prove the lemma for every m. It supplied a reduction plus an ineffective asymptotic result,
and claimed an exact certificate over a finite range. Nothing here is taken on trust; the
checkable parts are re-derived against my own fold implementation.

Its claims, in the order they carry weight:

  (a) The numbers whose Zeckendorf expansions vanish in positions F_2..F_{m+1} are exactly
      T_m(r) = F_{m+1} r + F_m floor((r+1)/phi), r >= 0.
  (b) Consecutive gaps satisfy T_m(r+1) - T_m(r) in {F_{m+1}, F_{m+2}}.
  (c) The fold is the sawtooth remainder: if T_m(r) <= n < T_m(r+1) then f_m(n) = n - T_m(r).
  (d) Edge residual lemma: flipping bit i changes the value by a signed power p, and the
      resulting fold difference lies in an explicit set C_m(p) of at most eight integers.
  (e) Residual separation: if the C_m(p) are pairwise disjoint over the signed powers, then
      Phi_m is injective.
  (f) That disjointness holds for every 13 <= m <= 1000, and at m = 12 the only residual
      ambiguities are 16 against -128 and -16 against 128, coming from 144 = 128 + 16.

(a), (b), (c), (d) and (f) are finite statements and are checked directly. (e) is an
implication, checked in the direction that matters: wherever the criterion fires, injectivity
must actually hold. The criterion is strictly stronger than the lemma, since it gives outright
injectivity, so it cannot fire at m = 6, 8, 9 where Phi_m provably is not injective; the check
confirms it declines there rather than giving a false positive.

All arithmetic is exact. floor(h/phi) is computed as (isqrt(5 h^2) - h)//2 for h >= 0, which
is floor(h (sqrt5 - 1)/2), with floor(-h/phi) = -floor(h/phi) - 1 for h > 0.
"""
import sys
from math import isqrt

FIB = [0, 1, 1]
while len(FIB) < 2100:
    FIB.append(FIB[-1] + FIB[-2])


def floor_div_phi(h):
    """floor(h / phi), exactly, for any integer h."""
    if h >= 0:
        return (isqrt(5 * h * h) - h) // 2
    return -floor_div_phi(-h) - 1


def T(m, r):
    return FIB[m + 1] * r + FIB[m] * floor_div_phi(r + 1)


def zeck_digits(n):
    """Greedy Zeckendorf expansion of n, as the set of indices k with F_k used."""
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
    """Numerical value of the retained prefix: the digits F_2..F_{m+1} of n."""
    return sum(FIB[k] for k in zeck_digits(n) if 2 <= k <= m + 1)


def is_tail(n, m):
    return not any(2 <= k <= m + 1 for k in zeck_digits(n))


def check_sawtooth(mlist, rmax=400):
    ok_a = ok_b = ok_c = True

    print("(a) T_m(r) enumerates exactly the numbers with no digits in F_2..F_{m+1}")
    for m in mlist:
        vals = [T(m, r) for r in range(rmax)]
        if vals != sorted(vals) or len(set(vals)) != len(vals):
            ok_a = False
            print("    m=%d: NOT strictly increasing" % m)
        for v in vals[:200]:
            if not is_tail(v, m):
                ok_a = False
                print("    m=%d: T_m produced %d, which has a low digit" % (m, v))
                break
        hi = vals[150]
        tails = [n for n in range(hi) if is_tail(n, m)]
        if tails != vals[:len(tails)]:
            ok_a = False
            print("    m=%d: T_m misses a tail number below %d" % (m, hi))
    print("  -> %s" % ("PASS" if ok_a else "FAIL"))

    print("(b) consecutive gaps lie in {F_{m+1}, F_{m+2}}")
    for m in mlist:
        gaps = {T(m, r + 1) - T(m, r) for r in range(rmax - 1)}
        if not gaps <= {FIB[m + 1], FIB[m + 2]}:
            ok_b = False
            print("    m=%d: gaps %s outside {%d, %d}"
                  % (m, sorted(gaps), FIB[m + 1], FIB[m + 2]))
    print("  -> %s" % ("PASS" if ok_b else "FAIL"))

    print("(c) the fold is the sawtooth remainder n - T_m(r)")
    for m in mlist:
        top = min(1 << m, T(m, 120))
        r = 0
        for n in range(top):
            while T(m, r + 1) <= n:
                r += 1
            if n - T(m, r) != fold_value(n, m):
                ok_c = False
                print("    m=%d n=%d: sawtooth %d vs fold %d"
                      % (m, n, n - T(m, r), fold_value(n, m)))
                break
    print("  -> %s" % ("PASS" if ok_c else "FAIL"))
    return ok_a and ok_b and ok_c


def residuals(m, p):
    """C_m(p) as defined in the transcript: p - A h - B (floor(h/phi) + eps), |.| < L."""
    A, B, L = FIB[m + 1], FIB[m], FIB[m + 2]
    out = set()
    centre = p // (A + B)
    for h in range(centre - 4, centre + 5):
        base = A * h + B * floor_div_phi(h)
        for eps in ((0,) if h == 0 else (0, 1)):
            c = p - base - B * eps
            if abs(c) < L:
                out.add(c)
    return out


def check_edge_lemma(mlist, samples=3000):
    print("(d) edge residual lemma: every fold difference across an edge lies in C_m(p)")
    ok = True
    for m in mlist:
        N = 1 << m
        step = max(1, N // samples)
        cache = {}
        for i in range(m):
            cache[2 ** i] = residuals(m, 2 ** i)
            cache[-(2 ** i)] = residuals(m, -(2 ** i))
        bad = 0
        for n in range(0, N, step):
            fn = fold_value(n, m)
            for i in range(m):
                p = (1 - 2 * ((n >> i) & 1)) * (2 ** i)
                if n + p < 0:
                    continue
                d = fold_value(n + p, m) - fn
                if d not in cache[p]:
                    ok = False
                    bad += 1
                    if bad <= 2:
                        print("    m=%d n=%d p=%d: difference %d not in C_m(p)"
                              % (m, n, p, d))
        print("    m=%2d  checked %d vertices, %d violations" % (m, len(range(0, N, step)), bad))
    print("  -> %s" % ("PASS" if ok else "FAIL"))
    return ok


def separation_fires(m):
    P = [s * (2 ** i) for i in range(m) for s in (1, -1)]
    sets = {p: residuals(m, p) for p in P}
    for a in range(len(P)):
        for b in range(a + 1, len(P)):
            if sets[P[a]] & sets[P[b]]:
                return False, (P[a], P[b])
    return True, None


def phi_injective(m):
    N = 1 << m
    fold = [fold_value(n, m) for n in range(N)]
    seen = set()
    for n in range(N):
        star = tuple(sorted(fold[n ^ (1 << i)] for i in range(m)))
        key = (fold[n], star)
        if key in seen:
            return False
        seen.add(key)
    return True


def check_criterion(direct_upto=16):
    print("(e) wherever separation fires, Phi_m really is injective")
    ok = True
    for m in range(6, direct_upto + 1):
        fires, wit = separation_fires(m)
        inj = phi_injective(m)
        if fires and not inj:
            ok = False
            print("    m=%d: criterion FIRED but Phi_m is not injective" % m)
        tag = "fires" if fires else ("declines (%s vs %s)" % (wit[0], wit[1]))
        print("    m=%2d  separation %-30s Phi_m injective: %s" % (m, tag, inj))
    print("  -> %s" % ("PASS" if ok else "FAIL"))

    print("(f) separation holds for 13 <= m <= 1000, and declines at m=12")
    f12, w12 = separation_fires(12)
    print("    m=12: fires=%s  ambiguity=%s" % (f12, w12))
    bad = []
    for m in range(13, 1001):
        f, w = separation_fires(m)
        if not f:
            bad.append((m, w))
    if bad:
        print("    m=13..1000: %d FAILURES, first %s" % (len(bad), bad[:3]))
    else:
        print("    m=13..1000: all separated (988 values)")
    return ok, (not bad), f12


def main():
    a = check_sawtooth([6, 7, 8, 9, 10, 11, 12, 13, 14])
    print()
    d = check_edge_lemma([6, 8, 9, 11, 13, 15])
    print()
    e, f, f12 = check_criterion()
    print()
    print("SUMMARY", {"sawtooth a,b,c": a, "edge residual lemma d": d,
                      "criterion sound e": e, "separated 13..1000 f": f,
                      "declines at m=12": not f12})
    return 0 if (a and d and e and f and not f12) else 1


if __name__ == "__main__":
    sys.exit(main())
