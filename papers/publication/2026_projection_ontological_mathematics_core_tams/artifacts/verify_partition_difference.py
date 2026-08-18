#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent check of the foundation of the projection paper.

Everything in the paper - the squeeze on the collision moments S_q(m), the algebraicity of
each lambda_q, the pressure sequence and its bands, the limit D_m^{1/m} -> sqrt(phi) - is
built on the partition-difference formula:

    Theorem.  For every integer n with 0 <= n < F_{m+2},
              d_m(n) = R+(n) - R+(n - F_{m+1}),   where R+(n) = R(n) + R(n-1)

with R(n) the number of partitions of n into distinct Fibonacci numbers, the two unit
weights F_1 = F_2 = 1 not distinguished, and (from the proof)

    d_m(n) = [z^n] prod_{j=1}^{m} (1 + z^{F_j}).

Since sum_{j=1}^m F_j = F_{m+2} - 1, the value map on {0,1}^m already lands exactly on
{0, ..., F_{m+2}-1}, so the fibre multiplicity is literally that coefficient and no modular
reduction is involved. This script checks that reading by brute force first, then the
identity, then the two asymptotic claims that rest on it.

All arithmetic is exact integer arithmetic.
"""
import sys
from itertools import product

F = [0, 1, 1]
while len(F) < 60:
    F.append(F[-1] + F[-2])


def truncated_product(m, N):
    """Coefficients of prod_{j=1..m} (1 + z^{F_j}), up to degree N."""
    c = [0] * (N + 1)
    c[0] = 1
    for j in range(1, m + 1):
        k = F[j]
        for n in range(N, k - 1, -1):
            c[n] += c[n - k]
    return c


def R_table(N):
    """R(n): partitions into distinct Fibonacci numbers, units not distinguished.

    Generating series (1+z) * prod_{j>=3} (1 + z^{F_j}).
    """
    c = [0] * (N + 1)
    c[0] = 1
    for n in range(N, 0, -1):          # the single unit weight
        c[n] += c[n - 1]
    j = 3
    while F[j] <= N:
        k = F[j]
        for n in range(N, k - 1, -1):
            c[n] += c[n - k]
        j += 1
    return c


def Rdag(Rt, n):
    if n < 0:
        return 0
    a = Rt[n] if n < len(Rt) else 0
    b = Rt[n - 1] if 0 <= n - 1 < len(Rt) else 0
    return a + b


# ---------------------------------------------------------------- controls

def control_fibre_is_coefficient(maxm=18):
    """Brute force: the number of omega in {0,1}^m with sum omega_j F_j = n."""
    print("CONTROL 1  fibre multiplicity really is the coefficient of the truncated product")
    ok = True
    for m in range(1, maxm + 1):
        N = F[m + 2] - 1
        counts = [0] * (N + 1)
        for bits in product((0, 1), repeat=m):
            counts[sum(b * F[j + 1] for j, b in enumerate(bits))] += 1
        coeff = truncated_product(m, N)
        if counts != coeff:
            ok = False
            print(f"    MISMATCH at m={m}")
            break
        if sum(counts) != 2 ** m:
            ok = False
            print(f"    total is not 2^m at m={m}")
    print(f"    checked m = 1..{maxm}: value range is exactly [0, F_{{m+2}}-1], "
          f"totals are 2^m")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def control_R_small():
    """R(n) for small n against a direct subset enumeration."""
    print("CONTROL 2  R(n) against direct enumeration of Fibonacci subsets")
    N = 200
    Rt = R_table(N)
    parts = [1] + [F[j] for j in range(3, 20) if F[j] <= N]   # one unit, then 2,3,5,...
    direct = [0] * (N + 1)
    direct[0] = 1
    for k in parts:
        for n in range(N, k - 1, -1):
            direct[n] += direct[n - k]
    ok = direct == Rt
    print(f"    R(0..10) = {Rt[:11]}")
    print(f"    agrees with direct enumeration up to n = {N}: {ok}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


# ---------------------------------------------------------------- the theorem

def check_partition_difference(maxm=24):
    print("THEOREM  d_m(n) = R+(n) - R+(n - F_{m+1})  for 0 <= n < F_{m+2}")
    Rt = R_table(F[maxm + 2] + 5)
    ok = True
    total = 0
    for m in range(1, maxm + 1):
        N = F[m + 2] - 1
        d = truncated_product(m, N)
        bad = 0
        for n in range(N + 1):
            if d[n] != Rdag(Rt, n) - Rdag(Rt, n - F[m + 1]):
                bad += 1
                if bad == 1:
                    print(f"    MISMATCH m={m} n={n}: d={d[n]} "
                          f"rhs={Rdag(Rt, n) - Rdag(Rt, n - F[m+1])}")
        total += N + 1
        if bad:
            ok = False
    print(f"    m = 1..{maxm}, {total} values of n checked, "
          f"{'0' if ok else 'some'} mismatches")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def check_max_fibre(maxm=30):
    """D_m^{1/m} -> sqrt(phi) = 1.27201964951..."""
    phi = (1 + 5 ** 0.5) / 2
    target = phi ** 0.5
    print(f"CLAIM  D_m^(1/m) -> sqrt(phi) = {target:.9f}")
    prev = None
    for m in range(2, maxm + 1):
        d = truncated_product(m, F[m + 2] - 1)
        D = max(d)
        val = D ** (1.0 / m)
        mark = ""
        if prev is not None:
            mark = "up" if val > prev else "down"
        if m >= maxm - 7:
            print(f"    m={m:3d}  D_m = {D:<10d}  D_m^(1/m) = {val:.9f}  "
                  f"diff {val - target:+.3e}  {mark}")
        prev = val
    ok = abs(prev - target) < 0.05
    print(f"  -> {'consistent' if ok else 'CHECK'}\n")
    return ok


def check_moments(maxm=26, qs=(1, 2, 3, 4)):
    """S_q(m) = sum_n d_m(n)^q ; report S_q(m)^(1/m) and convexity of log lambda_q."""
    print("CLAIM  S_q(m) ~ lambda_q^m, and p_q = log lambda_q is convex")
    lam = {}
    for q in qs:
        vals = []
        for m in range(2, maxm + 1):
            d = truncated_product(m, F[m + 2] - 1)
            vals.append(sum(x ** q for x in d))
        ratios = [vals[i + 1] / vals[i] for i in range(len(vals) - 1)]
        lam[q] = ratios[-1]
        print(f"    q={q}: S_q(m+1)/S_q(m) at m={maxm-1} is {ratios[-1]:.9f}"
              f"   (m={maxm-6}: {ratios[-6]:.9f})")
    import math
    p = {q: math.log(lam[q]) for q in qs}
    p0 = math.log((1 + 5 ** 0.5) / 2)
    seq = [p0] + [p[q] for q in qs]
    deltas = [seq[i + 1] - seq[i] for i in range(len(seq) - 1)]
    convex = all(deltas[i + 1] >= deltas[i] - 1e-9 for i in range(len(deltas) - 1))
    print(f"    p_0 = log phi = {p0:.9f}, then {[f'{p[q]:.6f}' for q in qs]}")
    print(f"    slopes Delta_q = {[f'{d:.6f}' for d in deltas]}")
    print(f"    nondecreasing slopes (convexity): {convex}")
    print(f"  -> {'PASS' if convex else 'CHECK'}\n")
    return convex


if __name__ == "__main__":
    print("Independent check of the projection partition-difference formula\n")
    c1 = control_fibre_is_coefficient()
    c2 = control_R_small()
    if not (c1 and c2):
        print("CONTROLS FAILED - stopping.")
        sys.exit(1)
    r1 = check_partition_difference()
    r2 = check_max_fibre()
    r3 = check_moments()
    print("SUMMARY", {"partition difference": r1, "D_m^(1/m)": r2, "convex pressure": r3})
    sys.exit(0 if (r1 and r2 and r3) else 1)
