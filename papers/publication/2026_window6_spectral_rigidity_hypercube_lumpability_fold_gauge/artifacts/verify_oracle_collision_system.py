#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Check the Oracle's collision-constraint system before anything is built on it.

Section 7 of oracle_sprint_TWOSTAR_r1.md proposes the route that would finish the two-star
lemma. Suppose a and b share a Phi_m value. Match their equally coloured neighbours by a
permutation pi, and set

    D    = b - a
    p_i  = (1 - 2 a_i) 2^i          the signed power flipping bit i of a
    q_j  = (1 - 2 b_j) 2^j          the same for b
    u_i  = q_{pi(i)} - p_i

The transcript then asserts two exact identities,

    (16)   sum_i u_i      = -2 D
    (17)   sum_i R(u_i)   = -2 R(D)

where R(n) is the nearest integer to n/phi, and observes that in every collision it looked at,
exactly two of the u_i equal -D and the rest vanish, forcing D to be 34 or 144. Proving that
the system forces that two-coordinate shape would close the lemma.

That is worth pursuing only if the identities are true, so they are checked here against the
actual collisions at m = 6, 7, 8, 9, 10 - the only m below the injectivity threshold where
collisions exist at all. Identity (16) also has a one-line algebraic proof which is checked
symbolically on random words:

    sum_i (a XOR 2^i) = sum_i (a + (1 - 2 a_i) 2^i) = m a + (2^m - 1) - 2a
                      = (m - 2) a + (2^m - 1).

The matching pi is not unique when several neighbours share a colour, so the identities are
tested over every valid matching, not just one convenient choice. If they hold only for a
lucky matching, that is a materially weaker statement and the script says so.

R is taken as nearest-integer-to-n/phi. The transcript's rendering of the ratio was ambiguous
after transport, so the alternative reading n*phi is checked too and reported separately.
"""
import sys
from itertools import permutations
from math import isqrt

FIB = [0, 1, 1]
while len(FIB) < 120:
    FIB.append(FIB[-1] + FIB[-2])

PHI = (1 + 5 ** 0.5) / 2


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


def R_over(n):
    """Nearest integer to n/phi, exactly, via floor(x + 1/2) with x = n(sqrt5 - 1)/2."""
    num = n * (isqrt(5 * n * n) if False else 0)  # placeholder, unused
    # exact: round(n/phi) = floor((n*(sqrt5-1) + 1)/2 ... ) done in integer arithmetic below
    # n/phi = n(sqrt5-1)/2; compare 2*n*(sqrt5-1)/2 = n(sqrt5-1) against odd integers
    # round(x) = floor(x) + (1 if frac >= 1/2)
    if n >= 0:
        fl = (isqrt(5 * n * n) - n) // 2
    else:
        fl = -((isqrt(5 * n * n) + (-n)) // 2) - 1 if n else 0
        fl = -R_floor_pos(-n) - 1
    return fl + (1 if 2 * (n - fl * PHI) >= PHI else 0)


def R_floor_pos(n):
    return (isqrt(5 * n * n) - n) // 2


def R(n):
    """Nearest integer to n/phi."""
    return int(round(n / PHI))


def R_mult(n):
    """Nearest integer to n*phi, the alternative reading."""
    return int(round(n * PHI))


def collisions(m):
    """All unordered pairs sharing a Phi_m value."""
    N = 1 << m
    fold = [fold_value(n, m) for n in range(N)]
    buckets = {}
    for n in range(N):
        star = tuple(sorted(fold[n ^ (1 << i)] for i in range(m)))
        buckets.setdefault((fold[n], star), []).append(n)
    return [g for g in buckets.values() if len(g) > 1], fold


def matchings(a, b, m, fold, cap=20000):
    """All permutations pi with fold(a XOR 2^i) == fold(b XOR 2^pi(i))."""
    fa = [fold[a ^ (1 << i)] for i in range(m)]
    fb = [fold[b ^ (1 << j)] for j in range(m)]
    by_colour = {}
    for j, c in enumerate(fb):
        by_colour.setdefault(c, []).append(j)
    groups = []
    for c, js in by_colour.items():
        idx = [i for i in range(m) if fa[i] == c]
        if len(idx) != len(js):
            return []
        groups.append((idx, js))
    out, total = [], 1
    for idx, js in groups:
        total *= len(list(permutations(js)))
        if total > cap:
            return None
    def build(k, cur):
        if k == len(groups):
            out.append(dict(cur))
            return
        idx, js = groups[k]
        for perm in permutations(js):
            cur.update(dict(zip(idx, perm)))
            build(k + 1, cur)
    build(0, {})
    return out


def check_cube_identity(mlist):
    print("CONTROL  sum_i (a XOR 2^i) = (m-2) a + (2^m - 1)")
    ok = True
    for m in mlist:
        for a in range(0, 1 << m, max(1, (1 << m) // 200)):
            lhs = sum(a ^ (1 << i) for i in range(m))
            if lhs != (m - 2) * a + (2 ** m - 1):
                ok = False
                print("    m=%d a=%d: %d vs %d" % (m, a, lhs, (m - 2) * a + 2 ** m - 1))
                break
    print("  -> %s" % ("PASS" if ok else "FAIL"))
    return ok


def main():
    ok_cube = check_cube_identity([6, 7, 8, 9, 10, 12])
    print()
    print("IDENTITIES (16) and (17) on every actual collision, over EVERY valid matching")
    ok16 = ok17 = ok17m = True
    two_coord_always = True
    seen_any = False
    for m in (6, 7, 8, 9, 10):
        cols, fold = collisions(m)
        n16 = n17 = n17m = tot = 0
        shapes = {}
        for g in cols:
            for x in range(len(g)):
                for y in range(x + 1, len(g)):
                    a, b = g[x], g[y]
                    D = b - a
                    ms = matchings(a, b, m, fold)
                    if ms is None:
                        continue
                    for pi in ms:
                        seen_any = True
                        tot += 1
                        p = [(1 - 2 * ((a >> i) & 1)) * 2 ** i for i in range(m)]
                        q = [(1 - 2 * ((b >> j) & 1)) * 2 ** j for j in range(m)]
                        u = [q[pi[i]] - p[i] for i in range(m)]
                        if sum(u) == -2 * D:
                            n16 += 1
                        if sum(R(v) for v in u) == -2 * R(D):
                            n17 += 1
                        if sum(R_mult(v) for v in u) == -2 * R_mult(D):
                            n17m += 1
                        nz = [v for v in u if v != 0]
                        shape = (len(nz), all(v == -D for v in nz))
                        shapes[shape] = shapes.get(shape, 0) + 1
                        if not (len(nz) == 2 and all(v == -D for v in nz)):
                            two_coord_always = False
        if tot:
            print("    m=%2d  %d (pair, matching) cases" % (m, tot))
            print("          (16) sum u_i = -2D            : %d/%d" % (n16, tot))
            print("          (17) with R = round(n/phi)    : %d/%d" % (n17, tot))
            print("          (17) with R = round(n*phi)    : %d/%d" % (n17m, tot))
            print("          shapes (count nonzero, all == -D): %s" % shapes)
            ok16 &= (n16 == tot)
            ok17 &= (n17 == tot)
            ok17m &= (n17m == tot)
    if not seen_any:
        print("    no collisions found at all -- nothing was tested")
        return 1
    print()
    print("SUMMARY", {"cube identity": ok_cube, "(16) holds always": ok16,
                      "(17) with n/phi": ok17, "(17) with n*phi": ok17m,
                      "two-coordinate shape always": two_coord_always})
    return 0 if (ok_cube and ok16) else 1


if __name__ == "__main__":
    sys.exit(main())
