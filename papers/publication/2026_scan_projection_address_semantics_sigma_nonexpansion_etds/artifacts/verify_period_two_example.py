#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent check of the period-two example in scan_projection.

The paper's central negative claim is that the phase qualification cannot be removed: it
exhibits a period-two survivor whose pair-collision Poisson mean differs between the two
depth classes, so the collision count has no full-sequence weak limit under the natural
phase-free normalisation. Everything rests on this one worked example, so it is the thing
worth checking.

Claims checked, all from Section "A period-two survivor with two Poisson means":

  pi K = pi                with pi = (21,16,16,36)/89
  rho_s = sqrt(6^-s + 12^-s),  rho_1 = 1/2,  rho_2 = sqrt5/12
  h_{2,H} = -log(rho_2 / rho_1^2) = log(3/sqrt5)
  c_{2,0} = 953/2809,  c_{2,1} = 267/(338 sqrt5)      (approx 0.3393 and 0.3533)
  Poisson means 953/5618 alpha^2 and 267/(676 sqrt5) alpha^2, which are unequal

The decisive check is the last constant pair. Since the Poisson mean is
(alpha^2 / 2) times c_{2,phase}, the paper is asserting

  lim_{m -> infinity, m-1 = phase mod 2}  S_2(m) * (3/sqrt5)^(m-1)  =  c_{2,phase}

where S_2(m) is the Renyi power sum of the depth-m conditioned survivor law. That is
computed here directly and exactly, not from the paper's spectral formulas: writing mu_m
for the unnormalised law on safe prefixes,

  sum_x mu_m(x)^2 = (pi^(2))^T B_2^(m-1) 1        with (B_s)_ij = (K_ij)^s
  Z_m             = pi^T   B_1^(m-1) 1
  S_2(m)          = [sum_x mu_m(x)^2] / Z_m^2

so every quantity is a rational number until the final irrational normalisation.
"""
import argparse
import sys
from fractions import Fraction as Fr
from decimal import Decimal, getcontext

getcontext().prec = 60

# ---------------------------------------------------------------- the example

# Ambient chain on a, b, c, h.
K = [
    [Fr(0), Fr(1, 3), Fr(1, 3), Fr(1, 3)],
    [Fr(1, 2), Fr(0), Fr(0), Fr(1, 2)],
    [Fr(1, 4), Fr(0), Fr(0), Fr(3, 4)],
    [Fr(1, 4), Fr(1, 4), Fr(1, 4), Fr(1, 4)],
]
PI = [Fr(21, 89), Fr(16, 89), Fr(16, 89), Fr(36, 89)]

SAFE = [0, 1, 2]                      # a, b, c ; the hole is h


def killed(s):
    """B_s restricted to the safe states, entries (K_ij)^s."""
    return [[K[i][j] ** s for j in SAFE] for i in SAFE]


def matvec(M, v):
    return [sum(M[i][j] * v[j] for j in range(len(v))) for i in range(len(M))]


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def power_sum(s, m):
    """(pi^(s))^T B_s^(m-1) 1 : the unnormalised s-th power sum at depth m."""
    v = [Fr(1)] * len(SAFE)
    B = killed(s)
    for _ in range(m - 1):
        v = matvec(B, v)
    return dot([PI[i] ** s for i in SAFE], v)


def S2(m):
    """Renyi pair power sum of the depth-m conditioned survivor law."""
    return power_sum(2, m) / power_sum(1, m) ** 2


# ---------------------------------------------------------------- controls

def control_stationary():
    print("CONTROL 1  pi K = pi")
    got = [sum(PI[i] * K[i][j] for i in range(4)) for j in range(4)]
    ok = got == PI
    print(f"    pi K = {[str(x) for x in got]}")
    print(f"    pi   = {[str(x) for x in PI]}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def perron(B, iters=4000):
    """Perron eigenvalue by power iteration on the square of the matrix (period 2)."""
    v = [1.0] * len(B)
    Bf = [[float(x) for x in row] for row in B]
    lam = 0.0
    for _ in range(iters):
        w = [sum(Bf[i][j] * v[j] for j in range(len(v))) for i in range(len(Bf))]
        w = [sum(Bf[i][j] * w[j] for j in range(len(w))) for i in range(len(Bf))]
        n = max(abs(x) for x in w)
        v = [x / n for x in w]
        lam = n ** 0.5
    return lam


def control_perron():
    print("CONTROL 2  Perron eigenvalues rho_1 and rho_2")
    ok = True
    for s, name, want in ((1, "rho_1", 0.5), (2, "rho_2", 5 ** 0.5 / 12)):
        got = perron(killed(s))
        err = abs(got - want)
        if err > 1e-9:
            ok = False
        print(f"    {name}: computed {got:.12f}   paper {want:.12f}   |diff| {err:.2e}")
    # and the closed form rho_s = sqrt(6^-s + 12^-s)
    for s in (1, 2, 3):
        cf = (6.0 ** -s + 12.0 ** -s) ** 0.5
        got = perron(killed(s))
        print(f"    s={s}: power iteration {got:.12f}   sqrt(6^-s+12^-s) {cf:.12f}")
        if abs(got - cf) > 1e-9:
            ok = False
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def control_survival_is_a_probability(maxm=12):
    print("CONTROL 3  Z_m is a decreasing probability and S_2(m) is a valid power sum")
    ok, prev = True, Fr(2)
    for m in range(1, maxm + 1):
        Z = power_sum(1, m)
        s2 = S2(m)
        if not (0 < Z <= 1) or not (0 < s2 <= 1) or Z > prev:
            ok = False
            print(f"    PROBLEM at m={m}: Z={float(Z)} S2={float(s2)}")
        prev = Z
    print(f"    checked m = 1..{maxm}: survival decreasing in (0,1], S_2 in (0,1]")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


# ---------------------------------------------------------------- the claim

def check_two_constants(maxm=90):
    root5 = Decimal(5).sqrt()
    scale = Decimal(3) / root5                       # e^{h_{2,H}}
    c0 = Decimal(953) / Decimal(2809)
    c1 = Decimal(267) / (Decimal(338) * root5)
    print("THEOREM  S_2(m) * (3/sqrt5)^(m-1) -> c_{2,phase}, phase = (m-1) mod 2")
    print(f"    paper: c_20 = 953/2809      = {c0:.12f}")
    print(f"           c_21 = 267/(338*r5)  = {c1:.12f}")
    rows = {0: [], 1: []}
    for m in range(2, maxm + 1):
        val = Decimal(S2(m).numerator) / Decimal(S2(m).denominator) * scale ** (m - 1)
        rows[(m - 1) % 2].append((m, val))
    ok = True
    for phase, target in ((0, c0), (1, c1)):
        tail = rows[phase][-6:]
        print(f"    phase {phase}  (target {target:.12f})")
        for m, v in tail:
            print(f"        m={m:3d}   {v:.12f}   diff {v - target:+.3e}")
        # Convergence must be judged only while the error is above the arithmetic
        # floor; once it reaches the precision of the Decimal context it is rounding
        # noise and monotonicity is meaningless.
        FLOOR = Decimal("1e-50")
        meaningful = [(m, abs(v - target)) for m, v in rows[phase] if abs(v - target) > FLOOR]
        shrinking = all(meaningful[i + 1][1] <= meaningful[i][1]
                        for i in range(len(meaningful) - 1))
        final = abs(rows[phase][-1][1] - target)
        if meaningful:
            print(f"        error above the 1e-50 floor at m = "
                  f"{meaningful[0][0]}..{meaningful[-1][0]}, "
                  f"from {meaningful[0][1]:.3e} to {meaningful[-1][1]:.3e}, "
                  f"monotone: {shrinking}")
            ratios = [float(meaningful[i + 1][1] / meaningful[i][1])
                      for i in range(min(5, len(meaningful) - 1))]
            print(f"        successive error ratios: "
                  f"{', '.join(f'{r:.4f}' for r in ratios)}")
        print(f"        final error at m={rows[phase][-1][0]}: {final:.3e} "
              f"(arithmetic floor)")
        if not (shrinking and final < Decimal("1e-40")):
            ok = False
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def check_means_differ(negative_control=False):
    root5 = Decimal(5).sqrt()
    even_numerator = 954 if negative_control else 953
    if negative_control:
        print("NEGATIVE CONTROL  claimed even mean 953/5618 -> 954/5618")
    m0 = Decimal(even_numerator) / Decimal(5618)
    m1 = Decimal(267) / (Decimal(676) * root5)
    print("CLAIM  the two Poisson means are different")
    print(f"    even class  {even_numerator}/5618        = {m0:.12f}")
    print(f"    odd  class  267/(676 sqrt5) = {m1:.12f}")
    print(f"    ratio {m1 / m0:.9f}   difference {m1 - m0:+.9f}")
    # and each is half the corresponding c constant
    c0 = Decimal(953) / Decimal(2809)
    c1 = Decimal(267) / (Decimal(338) * root5)
    even_matches = abs(m0 - c0 / 2) < Decimal("1e-40")
    odd_matches = abs(m1 - c1 / 2) < Decimal("1e-40")
    constants_match = even_matches and odd_matches
    print(f"    mean_even = c_20 / 2 ? {even_matches}")
    print(f"    mean_odd  = c_21 / 2 ? {odd_matches}")
    print(f"    claimed means agree with derived constants: {constants_match}")
    ok = m0 != m1 and constants_match
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--negative-control",
        action="store_true",
        help="replace one claimed Poisson mean by an incorrect value",
    )
    args = parser.parse_args()

    print("Independent check of the scan_projection period-two example\n")
    c = [control_stationary(), control_perron(), control_survival_is_a_probability()]
    if not all(c):
        print("CONTROLS FAILED - stopping.")
        sys.exit(1)
    r = [check_two_constants(), check_means_differ(args.negative_control)]
    print("SUMMARY", {"controls": all(c), "two constants": r[0], "means differ": r[1]})
    sys.exit(0 if all(c + r) else 1)
