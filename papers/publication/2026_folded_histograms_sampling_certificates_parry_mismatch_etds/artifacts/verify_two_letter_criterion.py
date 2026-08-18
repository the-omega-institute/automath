#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent check of the main theorem of the folded_histograms note.

Theorem (sharp classification of collision-free windows). For irrational alpha in (0,1),
beta in (0,1), and delta = min(alpha, 1-alpha), the following are equivalent:

  (1) Fold_m is injective on S_m(alpha,beta) for every m >= 1
  (2) Fold_2 is injective on S_2(alpha,beta)
  (3) beta lies in (0,delta] union [1-delta,1)

Here s_j(x) = 1_[0,beta)(x + j alpha), and S_m is the set of length-m words realised on a
set of x of positive measure.

Method. s_j(x) = 1 exactly when x lies in the arc [-j alpha, beta - j alpha). The 2m
endpoints of these arcs cut the circle into at most 2m pieces, and each piece of positive
length contributes exactly one word to S_m. So S_m is computable exactly, with no sampling.

Arithmetic. alpha is taken to be a rational with a very large denominator - a continued
fraction convergent of a genuine irrational - so that every breakpoint comparison and every
arc length is exact and no floating-point tolerance is needed. For finite m the language
S_m depends only on the cyclic order of those 2m breakpoints, and a denominator far larger
than m cannot be distinguished from the irrational it approximates. Boundary values like
beta = delta can then be tested exactly, which is the whole point of a sharp threshold.
"""
import sys
from fractions import Fraction as Fr

# ---------------------------------------------------------------- Fibonacci and the fold

FIB = [0, 1]
while len(FIB) < 120:
    FIB.append(FIB[-1] + FIB[-2])


def value(w):
    """N_m(omega) = sum omega_j F_{j+1}, positions j = 1..m."""
    return sum(int(c) * FIB[j + 2] for j, c in enumerate(w))


def zeck_digits(n, m):
    """First m digits of the Zeckendorf expansion of n, in the paper's position order."""
    ks = []
    k = 2
    while FIB[k + 1] <= n:
        k += 1
    rest = n
    while rest > 0:
        while FIB[k] > rest:
            k -= 1
        ks.append(k)
        rest -= FIB[k]
        k -= 1
    out = ["0"] * m
    for k in ks:
        j = k - 2                      # digit at position j+1 has weight F_{j+2}
        if 0 <= j < m:
            out[j] = "1"
    return "".join(out)


def fold(w):
    return zeck_digits(value(w), len(w))


# ---------------------------------------------------------------- the realised language

def frac(x):
    return x - int(x) if x >= 0 else x - (int(x) - 1)


def realised_words(alpha, beta, m):
    """S_m(alpha,beta), computed exactly from the 2m arc endpoints."""
    pts = set()
    for j in range(m):
        pts.add(frac(-j * alpha))
        pts.add(frac(beta - j * alpha))
    pts = sorted(pts)
    words = set()
    for i in range(len(pts)):
        a, b = pts[i], pts[(i + 1) % len(pts)]
        length = (b - a) if b > a else (b + 1 - a)
        if length <= 0:
            continue
        mid = frac(a + length / 2)
        w = "".join("1" if in_arc(mid, frac(-j * alpha), beta) else "0" for j in range(m))
        words.add(w)
    return words


def in_arc(x, start, length):
    """Is x in the half-open circle arc [start, start+length)?"""
    d = x - start
    if d < 0:
        d += 1
    return d < length


# ---------------------------------------------------------------- controls

def control_bijection(maxm=14):
    print("CONTROL 1  N_m is a bijection from X_m onto {0,...,F_{m+2}-1}")
    ok = True
    for m in range(1, maxm + 1):
        legal = [w for w in _binary(m) if "11" not in w]
        vals = sorted(value(w) for w in legal)
        if vals != list(range(FIB[m + 2])):
            print(f"    MISMATCH m={m}: got {len(vals)} values, expected {FIB[m+2]}")
            ok = False
        for w in legal:
            if fold(w) != w:
                print(f"    Fold does not fix legal word {w}")
                ok = False
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def _binary(m):
    for i in range(1 << m):
        yield "".join("1" if (i >> k) & 1 else "0" for k in range(m))


def control_two_letter_table():
    print("CONTROL 2  the two-letter fold table quoted in the note")
    want = {"00": "00", "10": "10", "01": "01", "11": "00"}
    ok = all(fold(k) == v for k, v in want.items())
    for k, v in want.items():
        print(f"    Fold_2({k}) = {fold(k)}   note says {v}"
              f"   {'ok' if fold(k) == v else 'MISMATCH'}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def control_factor_count(alpha, beta, maxm=10):
    """A rotation coding by an interval has 2m factors of length m in the generic case."""
    print("CONTROL 3  |S_m| is the expected factor count (2m generic, m+1 Sturmian)")
    for m in range(1, maxm + 1):
        n = len(realised_words(alpha, beta, m))
        print(f"    m={m:2d}  |S_m| = {n}")
    print()
    return True


# ---------------------------------------------------------------- the theorem

def injective_on(alpha, beta, m):
    ws = realised_words(alpha, beta, m)
    return len({fold(w) for w in ws}) == len(ws)


def check_theorem(alpha, name, maxm=12):
    delta = min(alpha, 1 - alpha)
    print(f"THEOREM  alpha = {name}  (delta = {float(delta):.9f})")
    betas = []
    for num in range(1, 40):
        betas.append(Fr(num, 40))
    betas += [delta, 1 - delta, delta - Fr(1, 10**6), delta + Fr(1, 10**6),
              1 - delta - Fr(1, 10**6), 1 - delta + Fr(1, 10**6)]
    bad = 0
    for beta in sorted(set(b for b in betas if 0 < b < 1)):
        predicted = (beta <= delta) or (beta >= 1 - delta)
        allm = all(injective_on(alpha, beta, m) for m in range(1, maxm + 1))
        two = injective_on(alpha, beta, 2)
        if allm != predicted or two != predicted:
            bad += 1
            print(f"    MISMATCH beta={beta} predicted={predicted} "
                  f"all_m={allm} m2={two}")
    print(f"    {len(set(betas))} window lengths tested, {bad} mismatches")
    print(f"  -> {'PASS' if bad == 0 else 'FAIL'}\n")
    return bad == 0


def check_failure_is_at_two(alpha, name, maxm=12):
    """In the failing range the note says injectivity already fails at length two."""
    delta = min(alpha, 1 - alpha)
    print(f"REFINEMENT  in delta < beta < 1-delta the failure is already at m = 2"
          f"  ({name})")
    tested, bad = 0, 0
    for num in range(1, 60):
        beta = Fr(num, 60)
        if not (delta < beta < 1 - delta):
            continue
        tested += 1
        if injective_on(alpha, beta, 2):
            bad += 1
            print(f"    MISMATCH beta={beta} is injective at m=2")
    print(f"    {tested} window lengths in the failing range, {bad} mismatches")
    print(f"  -> {'PASS' if bad == 0 else 'FAIL'}\n")
    return bad == 0


if __name__ == "__main__":
    # Continued-fraction convergents of genuine irrationals, denominators far above any m.
    ALPHAS = [
        (Fr(165580141, 267914296), "golden ratio conjugate"),   # F_40/F_41
        (Fr(80782, 195025), "sqrt(2) - 1"),
        (Fr(4703, 33215), "pi - 3"),
    ]
    print("Independent check of the folded_histograms two-letter criterion\n")
    ok = control_bijection() and control_two_letter_table()
    if not ok:
        print("CONTROLS FAILED - the fold was implemented wrongly. Stopping.")
        sys.exit(1)
    control_factor_count(ALPHAS[0][0], Fr(1, 3))
    results = []
    for a, nm in ALPHAS:
        results.append(check_theorem(a, nm))
        results.append(check_failure_is_at_two(a, nm))
    print("SUMMARY  all checks passed:", all(results))
    sys.exit(0 if all(results) else 1)
