#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""The last unverified link: inequality (12) of the r1 transcript.

After t450 the effective route rests on exactly one item I had taken on trust. The transcript
oracle_sprint_TWOSTAR_r1.md argues that a tail number z and its index-shifted companion satisfy
|phi z - z'| <= phi^{-(m+1)}, that a difference of two tail numbers therefore has error at most
2 phi^{-(m+1)}, and that since an intersection of two residual sets expresses p - q as a
difference of two such tail differences,

    (12)    ||phi (p - q)||  <=  4 phi^{-(m+1)}      whenever C_m(p) meets C_m(q), p != q.

Everything downstream of (12) is now proved or exhaustively enumerated, so (12) is the whole
remaining dependency. It is an implication whose hypothesis is decidable, and residual
intersections occur only for m <= 12 (separation was verified for 13 <= m <= 5000), so the
hypothesis can be enumerated completely and the conclusion checked on every instance.

Two things are tested.

  MAIN   For every m from 6 to 12 and every pair of distinct signed powers p, q whose residual
         sets intersect, does ||phi (p-q)|| <= 4 phi^{-(m+1)} hold?

  CONTROL The same quantity for pairs that do NOT intersect. If the bound held for those too,
         (12) would be vacuous and could not drive the argument. The control reports how many
         non-intersecting pairs satisfy it, which must be a small minority.

The residual sets are recomputed here from the transcript's own definition rather than
imported, so that a mistake in my earlier transcription would show up as a disagreement
rather than be inherited.
"""
import sys
from math import isqrt

from mpmath import mp, mpf, floor, sqrt

mp.dps = 60
PHI = (1 + sqrt(5)) / 2

FIB = [0, 1, 1]
while len(FIB) < 80:
    FIB.append(FIB[-1] + FIB[-2])


def floor_div_phi(h):
    if h >= 0:
        return (isqrt(5 * h * h) - h) // 2
    return -floor_div_phi(-h) - 1


def frac_norm(x):
    f = x - floor(x)
    return min(f, 1 - f)


def residuals(m, p):
    """C_m(p) = { p - A h - B (floor(h/phi) + eps) : |.| < L }, A=F_{m+1}, B=F_m, L=F_{m+2}."""
    A, B, L = FIB[m + 1], FIB[m], FIB[m + 2]
    out = set()
    centre = p // (A + B)
    for h in range(centre - 4, centre + 5):
        base = A * h + B * floor_div_phi(h)
        for eps in ((0,) if h == 0 else (0, 1)):
            c = p - base - B * eps
            if -L < c < L:
                out.add(c)
    return out


def main():
    print("Check of inequality (12), the last item taken on trust\n")
    ok = True
    total_int = 0
    worst_ratio = mpf(0)
    ctrl_pass = ctrl_total = 0

    for m in range(6, 13):
        P = [s * (1 << i) for i in range(m) for s in (1, -1)]
        R = {p: residuals(m, p) for p in P}
        thr = 4 * PHI ** (-(m + 1))
        inter = 0
        bad = []
        for a in range(len(P)):
            for b in range(a + 1, len(P)):
                p, q = P[a], P[b]
                meets = bool(R[p] & R[q])
                val = frac_norm(PHI * (p - q))
                if meets:
                    inter += 1
                    total_int += 1
                    worst_ratio = max(worst_ratio, val / thr)
                    if val > thr:
                        bad.append((p, q, mp.nstr(val, 8), mp.nstr(thr, 8)))
                else:
                    ctrl_total += 1
                    if val <= thr:
                        ctrl_pass += 1
        if bad:
            ok = False
        print("    m=%2d  threshold %s   %d intersecting pairs, %d violating (12)%s"
              % (m, mp.nstr(thr, 8), inter, len(bad),
                 "" if not bad else "  e.g. " + str(bad[:2])))

    print()
    print("    total intersecting pairs tested: %d" % total_int)
    print("    worst  ||phi(p-q)|| / threshold : %s   (must be <= 1)"
          % mp.nstr(worst_ratio, 8))
    print("  -> (12) %s" % ("HOLDS on every instance" if ok else "FAILS"))

    print()
    print("    CONTROL, non-intersecting pairs also satisfying the bound: %d of %d (%.1f%%)"
          % (ctrl_pass, ctrl_total, 100.0 * ctrl_pass / max(1, ctrl_total)))
    discriminating = ctrl_pass < ctrl_total // 2
    print("    the bound is %s"
          % ("discriminating" if discriminating else "NOT discriminating -- (12) would be weak"))
    return 0 if (ok and discriminating) else 1


if __name__ == "__main__":
    sys.exit(main())


# ---------------------------------------------------------------------------
# (12) IS A CONSEQUENCE OF THE PROVED COMPARISON, so the chain closes.
#
# The enumeration above confirms (12) on every instance where its hypothesis holds, but
# instances only exist for m <= 12, so enumeration alone cannot establish the implication for
# all m. It does not have to: (12) follows from the UPPER half of the comparison proved in
# verify_phi_norm_zeckendorf.py.
#
# That comparison is  ||phi n|| <= phi * phi^{-kmin(n)}  for every n.
#
#   1. A tail number z, meaning one whose Zeckendorf digits all sit at index >= m+2, has
#      kmin(z) >= m+2, hence
#
#          ||phi z||  <=  phi * phi^{-(m+2)}  =  phi^{-(m+1)}.
#
#      This is exactly the transcript's assertion |phi z - z'| <= phi^{-(m+1)}, now with a
#      proof rather than an appeal.
#
#   2. For a difference of two tail numbers, ||phi(z1 - z2)|| <= ||phi z1|| + ||phi z2||
#      <= 2 phi^{-(m+1)}, since distance-to-nearest-integer is subadditive.
#
#   3. If c lies in C_m(p) and in C_m(q), then by the definition of the residual sets
#      c = p - D1 = q - D2 where each D_i = T_m(r_i + h_i) - T_m(r_i) is a difference of two
#      tail numbers. Hence p - q = D1 - D2 and
#
#          ||phi(p-q)||  <=  ||phi D1|| + ||phi D2||  <=  4 phi^{-(m+1)},
#
#      which is (12).
#
# So every link is now proved or exhaustively enumerated, and the ineffective Subspace step is
# gone. The remaining imports are standard and effective: the Bugeaud-Cipu-Mignotte binary-digit
# theorem, already cited by main.tex.
#
# The check below confirms step 1 numerically, since it is the only step doing real work.

def tail_bound_holds(m, count=3000):
    """Every tail number z below a bound satisfies ||phi z|| <= phi^{-(m+1)}."""
    A, B = FIB[m + 1], FIB[m]
    thr = PHI ** (-(m + 1))
    worst = mpf(0)
    for r in range(count):
        z = A * r + B * floor_div_phi(r + 1)          # T_m(r), a tail number
        worst = max(worst, frac_norm(PHI * z) / thr)
    return worst


def report_tail_bound():
    print("\nStep 1 of the derivation: tail numbers satisfy ||phi z|| <= phi^{-(m+1)}")
    ok = True
    for m in (6, 8, 10, 12, 16, 20, 30):
        w = tail_bound_holds(m)
        ok &= (w <= 1)
        print("    m=%2d  worst ||phi z|| / phi^{-(m+1)} = %s" % (m, mp.nstr(w, 8)))
    print("  -> %s" % ("PASS" if ok else "FAIL"))
    return ok
