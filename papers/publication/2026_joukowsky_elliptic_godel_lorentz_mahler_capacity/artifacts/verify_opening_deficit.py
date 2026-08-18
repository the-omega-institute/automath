#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent check of the opening-deficit limit in the joukowsky note.

Claim (abstract, and the opening half of the collapsed-fiber theorem). For every member of
the collapsed equality class, written d eta = (1+h) dm on the unit circle with
h(conj z) = -h(z) and |h| <= 1,

    lim_{s -> 0+}  ( s - I(J_{e^s *} eta) ) / (2 s)  =  (1/2) || h ||^2_{L^2(m)} ,

and the selection functional has sharp range [0, 1/2].

Here I is the lower-truncated logarithmic energy of Section 2 and J_r(z) = r z + r^{-1}/z.

The analytic route, which this script confirms numerically rather than assumes:
on |z| = |w| = 1,

    J_r(z) - J_r(w) = (z - w) ( r - r^{-1} conj(z w) ),

so log|J_r(z)-J_r(w)| splits into log|z-w| plus a term depending only on theta + phi. With
r = e^s the second factor expands as s - sum_n e^{-2ns} cos(n psi)/n. Conjugation-oddness
of h forces every Fourier coefficient of h to be purely imaginary, hat h_n = i b_n, and the
two pieces combine to

    s - I(J_{e^s *} eta) = sum_{n>=1} (b_n^2 / n) (1 - e^{-2 n s}),

whose quotient by 2s tends termwise to sum b_n^2 = (1/2) ||h||^2.

The script checks the factorisation pointwise, checks the energy against direct quadrature
rather than against that series, and then checks the limit.
"""
import cmath
import math
import sys

TWO_PI = 2.0 * math.pi


# ---------------------------------------------------------------- test members of the fiber

def h_sign(t):
    """h = sign(sin theta): the extreme member, |h| = 1 a.e."""
    s = math.sin(t)
    return 1.0 if s > 0 else (-1.0 if s < 0 else 0.0)


def h_sin(t):
    return math.sin(t)


def h_sin3(t):
    return math.sin(3.0 * t)


def h_mix(t):
    return 0.5 * math.sin(t) + 0.25 * math.sin(2.0 * t) - 0.125 * math.sin(5.0 * t)


def h_zero(t):
    return 0.0


MEMBERS = [
    ("h = 0 (Haar)", h_zero),
    ("h = sin", h_sin),
    ("h = sin 3t", h_sin3),
    ("h = mixed", h_mix),
    ("h = sign(sin) [extreme]", h_sign),
]


def l2_norm_sq(h, N=200000):
    """||h||^2 with respect to normalised Haar measure."""
    return sum(h(TWO_PI * k / N) ** 2 for k in range(N)) / N


def oddness_defect(h, N=4001):
    """max |h(-t) + h(t)| ; zero iff h is conjugation-odd."""
    return max(abs(h(-TWO_PI * k / N) + h(TWO_PI * k / N)) for k in range(N))


# ---------------------------------------------------------------- controls

def control_factorisation(trials=20000):
    """|J_r(z) - J_r(w)| = |z-w| * |r - r^{-1} conj(zw)| on the unit circle."""
    print("CONTROL 1  the Joukowsky difference factorisation on |z|=|w|=1")
    worst = 0.0
    state = 12345
    for _ in range(trials):
        state = (1103515245 * state + 12345) % (1 << 31)
        t = TWO_PI * state / (1 << 31)
        state = (1103515245 * state + 12345) % (1 << 31)
        p = TWO_PI * state / (1 << 31)
        state = (1103515245 * state + 12345) % (1 << 31)
        r = 1.0 + 3.0 * state / (1 << 31)
        z, w = cmath.exp(1j * t), cmath.exp(1j * p)
        lhs = abs((r * z + 1 / (r * z)) - (r * w + 1 / (r * w)))
        rhs = abs(z - w) * abs(r - (1 / r) * (z * w).conjugate())
        worst = max(worst, abs(lhs - rhs))
    print(f"    worst absolute discrepancy over {trials} random (theta,phi,r): {worst:.3e}")
    ok = worst < 1e-12
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def energy_direct(h, s, N=4096):
    """I(J_{e^s *} eta) by quadrature, using the factorisation but not the series.

    The smooth factor is integrated on a full 2-D grid. The log|z-w| factor is reduced to
    one dimension by the autocorrelation of h and integrated with the diagonal cell handled
    by the exact integral of log|2 sin(u/2)| over that cell.
    """
    r = math.exp(s)
    # --- smooth part: iint log|r - r^{-1} e^{-i(theta+phi)}| d eta d eta
    hv = [h(TWO_PI * k / N) for k in range(N)]
    wt = [1.0 + v for v in hv]
    acc = 0.0
    for i in range(N):
        ti = TWO_PI * i / N
        for j in range(N // 8):            # psi depends only on the sum; subsample phi
            tj = TWO_PI * (j * 8) / N
            psi = ti + tj
            val = 0.5 * math.log(r * r + 1.0 / (r * r) - 2.0 * math.cos(psi))
            acc += val * wt[i] * wt[(j * 8) % N]
    smooth = acc / (N * (N // 8))
    # --- singular part: int log(2|sin(u/2)|) R(u) dm(u), R the autocorrelation of h
    tot = 0.0
    for k in range(N):
        u = TWO_PI * k / N
        R = sum(hv[(i + k) % N] * hv[i] for i in range(N)) / N
        if k == 0:
            cell = TWO_PI / N
            # exact mean of log(2|sin(u/2)|) over (-cell/2, cell/2), small-u approximation
            lg = math.log(cell / 2.0) - 1.0
        else:
            lg = math.log(2.0 * abs(math.sin(u / 2.0)))
        tot += lg * R
    singular = tot / N
    return smooth + singular


def control_haar(s_values):
    """For h = 0 the pushforward is the ellipse equilibrium measure, so I = log r = s."""
    print("CONTROL 2  h = 0 gives I(J_{e^s *} m) = s  (ellipse capacity r)")
    ok = True
    for s in s_values:
        got = energy_direct(h_zero, s, N=1024)
        err = abs(got - s)
        if err > 5e-3:
            ok = False
        print(f"    s = {s:<9.5f}  I = {got: .6f}   s = {s:.6f}   |diff| = {err:.2e}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


# ---------------------------------------------------------------- the limit

def series_deficit(h, s, nmax=4000, N=8192):
    """s - I, via the closed form sum_n (b_n^2 / n)(1 - e^{-2ns})."""
    hv = [h(TWO_PI * k / N) for k in range(N)]
    total = 0.0
    for n in range(1, nmax + 1):
        b = -sum(hv[k] * math.sin(n * TWO_PI * k / N) for k in range(N)) / N
        # hat h_n = i b_n with b_n = -(1/2pi) int h sin(n t) dt ... sign is irrelevant here
        total += (b * b) / n * (1.0 - math.exp(-2.0 * n * s))
    return total


def check_member(name, h):
    target = 0.5 * l2_norm_sq(h)
    odd = oddness_defect(h)
    print(f"MEMBER  {name}")
    print(f"    conjugation-oddness defect: {odd:.2e}   (must be 0)")
    print(f"    (1/2)||h||^2 = {target:.9f}")
    rows = []
    for s in (0.1, 0.03, 0.01, 0.003, 0.001):
        q = series_deficit(h, s) / (2.0 * s)
        rows.append((s, q))
        print(f"    s = {s:<8.4f}  (s - I)/(2s) = {q:.9f}   diff = {q - target:+.2e}")
    trend = all(abs(rows[i + 1][1] - target) <= abs(rows[i][1] - target) + 1e-12
                for i in range(len(rows) - 1))
    close = abs(rows[-1][1] - target) < 2e-3
    print(f"    monotone approach to the target: {trend}")
    print(f"  -> {'PASS' if (trend and close and odd < 1e-12) else 'CHECK'}\n")
    return trend and close and odd < 1e-12


def cross_check(h, name, s=0.05):
    """The series closed form against direct quadrature, so the series is not assumed."""
    direct = energy_direct(h, s, N=1024)
    from_series = s - series_deficit(h, s)
    print(f"CROSS-CHECK  {name} at s = {s}")
    print(f"    I by quadrature   = {direct: .6f}")
    print(f"    I from closed form= {from_series: .6f}")
    print(f"    |difference|      = {abs(direct - from_series):.2e}")
    ok = abs(direct - from_series) < 5e-3
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


if __name__ == "__main__":
    print("Independent check of the joukowsky opening-deficit limit\n")
    c1 = control_factorisation()
    c2 = control_haar([0.05, 0.02])
    if not (c1 and c2):
        print("CONTROLS FAILED - stopping, nothing downstream would mean anything.")
        sys.exit(1)
    x1 = cross_check(h_sin, "h = sin")
    x2 = cross_check(h_mix, "h = mixed")
    res = [check_member(n, f) for n, f in MEMBERS]
    print("Range check: the extreme member should give exactly 1/2.")
    print(f"    (1/2)||sign(sin)||^2 = {0.5 * l2_norm_sq(h_sign):.9f}")
    print(f"    h = 0 gives          = {0.5 * l2_norm_sq(h_zero):.9f}")
    print("\nSUMMARY", {"factorisation": c1, "haar control": c2,
                        "series vs quadrature": x1 and x2, "members": all(res)})
    sys.exit(0 if (c1 and c2 and x1 and x2 and all(res)) else 1)
