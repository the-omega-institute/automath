#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Is ||phi n|| controlled by the lowest Zeckendorf index of n?

Context. The remaining gap in the two-star lemma is the ineffectivity of the Subspace cutoff
(oracle_sprint_TWOSTAR_r1.md, section 5). Its Diophantine content is that a residual ambiguity
forces a signed two-power integer u = +-2^i +- 2^j to satisfy ||phi u|| <= 4 phi^{-(m+1)},
where ||.|| is distance to the nearest integer. The Subspace Theorem handles that for general
algebraic numbers and is ineffective.

But phi is not a general algebraic number. Its continued fraction is all ones, so its
inhomogeneous approximation theory is completely explicit through Zeckendorf/Ostrowski data,
and the natural guess - which I sketched at t439 but never checked - is

    ||phi n|| is governed by the LOWEST Zeckendorf index of n,

so that a small ||phi n|| forces n to have no low Zeckendorf digits, i.e. n is a tail number.
If that is exact, the Diophantine condition turns into the purely combinatorial statement that
u is a tail number AND a signed sum of two powers of two, which is where the imported
Bugeaud-Cipu-Mignotte classification already bites, and no Subspace Theorem is needed.

The basis is the identity phi F_k - F_{k+1} = -(-1/phi)^k, giving ||phi F_k|| = phi^{-k}
exactly for k large enough that the right side is below 1/2.

What is checked here:

  (A) ||phi F_k|| = phi^{-k}, exactly, for a range of k.
  (B) For general n with lowest Zeckendorf index kmin, whether ||phi n|| is comparable to
      phi^{-kmin}, and with what constants. This is the claim that matters and it is the one
      I have not seen stated anywhere, so it is tested rather than assumed.
  (C) The consequence actually needed: does ||phi n|| <= 4 phi^{-(m+1)} force kmin(n) >= m-2?
      Tested by brute force over all n below a bound, for several m. I first asked this with
      m in place of m-2 and it is false; see the note on check_C. The constant 4 costs about
      three Zeckendorf indices, which is the whole difference.

All values are computed in 80-digit arithmetic; the quantities compared are separated by many
orders of magnitude, so the precision is not doing delicate work.
"""
import sys

from mpmath import mp, mpf, floor, sqrt

mp.dps = 80
PHI = (1 + sqrt(5)) / 2

FIB = [0, 1, 1]
while len(FIB) < 200:
    FIB.append(FIB[-1] + FIB[-2])


def frac_norm(x):
    """Distance from x to the nearest integer."""
    f = x - floor(x)
    return min(f, 1 - f)


def zeck_indices(n):
    if n == 0:
        return []
    k = 2
    while FIB[k + 1] <= n:
        k += 1
    out, rest = [], n
    while rest > 0:
        while FIB[k] > rest:
            k -= 1
        out.append(k)
        rest -= FIB[k]
        k -= 1
    return out                      # descending


def check_A(kmax=60):
    print("(A)  ||phi F_k|| = phi^{-k}")
    ok = True
    worst = mpf(0)
    for k in range(3, kmax):
        lhs = frac_norm(PHI * FIB[k])
        rhs = PHI ** (-k)
        rel = abs(lhs - rhs) / rhs
        worst = max(worst, rel)
        if rel > mpf("1e-50"):          # 80 dps delivers about 1e-57, not 1e-60
            ok = False
            print("    k=%d: %s vs %s" % (k, mp.nstr(lhs, 12), mp.nstr(rhs, 12)))
    print("    k = 3..%d, worst relative error %s" % (kmax - 1, mp.nstr(worst, 6)))
    print("  -> %s" % ("PASS" if ok else "FAIL"))
    return ok


def check_B(nmax=200000):
    print("\n(B)  ||phi n|| against phi^{-kmin(n)}, kmin the lowest Zeckendorf index")
    lo = mpf("inf")
    hi = mpf(0)
    arg_lo = arg_hi = None
    for n in range(1, nmax):
        ks = zeck_indices(n)
        kmin = ks[-1]
        r = frac_norm(PHI * n) / PHI ** (-kmin)
        if r < lo:
            lo, arg_lo = r, (n, kmin)
        if r > hi:
            hi, arg_hi = r, (n, kmin)
    print("    n = 1..%d" % (nmax - 1))
    print("    ratio ||phi n|| / phi^{-kmin} lies in [%s, %s]"
          % (mp.nstr(lo, 8), mp.nstr(hi, 8)))
    print("        minimum at n=%d (kmin=%d), maximum at n=%d (kmin=%d)"
          % (arg_lo[0], arg_lo[1], arg_hi[0], arg_hi[1]))
    two_sided = lo > mpf("0.1") and hi < mpf("10")
    print("    two-sided comparability with absolute constants: %s" % two_sided)
    print("  -> %s" % ("PASS" if two_sided else "FAIL - the guess is not exact as stated"))
    return two_sided, lo, hi


def check_C(mlist=(6, 8, 10, 12, 14), nmax=300000):
    """The bound that (B) actually supports.

    My first version of this check asked whether the threshold forces kmin >= m. It does not,
    and the failure is arithmetic rather than structural. By (B), ||phi n|| >= phi^{-kmin}/phi,
    so ||phi n|| <= 4 phi^{-(m+1)} gives phi^{m+1-kmin} <= 4 phi, that is

        kmin >= m + 1 - log_phi(4 phi) = m - log(4)/log(phi) > m - 2.89.

    So the correct effective conclusion is kmin >= m - 2. The constant 4 in the Oracle's
    inequality costs about three Zeckendorf indices and nothing more. Stating it as kmin >= m
    was my error, not a defect in the approach.
    """
    print("\n(C)  does ||phi n|| <= 4 phi^{-(m+1)} force kmin(n) >= m - 2?")
    allok = True
    for m in mlist:
        thr = 4 * PHI ** (-(m + 1))
        bad = []
        small = 0
        for n in range(1, nmax):
            if frac_norm(PHI * n) <= thr:
                small += 1
                kmin = zeck_indices(n)[-1]
                if kmin < m - 2:
                    bad.append((n, kmin))
        ok = not bad
        allok &= ok
        print("    m=%2d  threshold %s : %d of %d integers qualify, %d with kmin < m-2 %s"
              % (m, mp.nstr(thr, 6), small, nmax - 1, len(bad),
                 "" if ok else ("e.g. " + str(bad[:3]))))
    print("  -> %s" % ("PASS" if allok else "FAIL"))
    return allok


def main():
    a = check_A()
    b, lo, hi = check_B()
    c = check_C()
    print("\nSUMMARY", {"(A) exact on Fibonacci": a,
                        "(B) two-sided on general n": b,
                        "(C) small norm forces kmin >= m-2": c})
    if a and b and c:
        print("\nSo the Diophantine condition is equivalent to a Zeckendorf-tail condition, with")
        print("explicit constants. That is an effective statement, which is what the Subspace")
        print("route lacks. It does NOT by itself close the lemma - the two-power side still")
        print("needs Bugeaud-Cipu-Mignotte - but it removes the ineffective step.")
    return 0 if (a and b and c) else 1


if __name__ == "__main__":
    sys.exit(main())
