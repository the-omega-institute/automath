#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""A single correction term cannot describe n^s Z_n, and that explains the disagreeing fits.

Prepared while the rate question was out with the Oracle, so that whatever answer comes back
can be tested immediately rather than taken on trust.

The known behaviour is that n^s Z_n(sigma_0) rises to about 15.28, turns over near n = 27, and
descends. Two consequences follow from the shape alone, before any analysis.

First, a form C + B n^(-alpha) approaches C monotonically. It cannot turn over, for any alpha
and any sign of B. So no single correction exponent can describe this sequence.

Second, that is testable against the pre-peak data, and it fails in a specific and informative
way. Fitting C + B n^(-alpha) by least squares on n = 12..25, taken from Zn_table_sigma0.txt:

    alpha = 0.25    C = 34.90
    alpha = 0.5     C = 24.43
    alpha = 1       C = 19.19
    alpha = s-1     C = 17.49
    alpha = 2       C = 16.57

Every one lands ABOVE the documented peak of 15.28. A sequence that peaks at 15.28 and then
descends must have its limit BELOW 15.28, so all of these are impossible as limits. They are
not evidence about the constant; they are evidence that the fitted form is wrong.

This retrospectively explains something recorded at t457 as a puzzle. verify_critical_tail_
constant.py reports A + B/d giving 16.89 and A + B/sqrt(d) giving 20.38, and I noted that the
disagreement meant the convergence rate was unidentified. The sharper statement is that both
are monotone one-term fits to a sequence that turns over, so neither could have been right and
their disagreement was guaranteed in advance.

WHAT THIS GIVES: a concrete test to apply to any proposed asymptotic. If an answer offers a
single correction exponent, it cannot account for the turnover and should be challenged on that
point. A satisfactory answer needs at least two terms of opposite sign, and should predict the
crossing near n = 27.
"""
import sys

from mpmath import mp, mpf, matrix, lu_solve

mp.dps = 30
SIGMA0 = mpf("2.4787507857339602606714872614")
PEAK = mpf("15.28")


def load(path="Zn_table_sigma0.txt"):
    rows = []
    for ln in open(path):
        if ln.startswith("#") or not ln.strip():
            continue
        p = ln.split()
        rows.append((int(p[0]), mpf(p[1])))
    return rows


def fit(rows, alpha):
    A = matrix(len(rows), 2)
    y = matrix(len(rows), 1)
    for i, (n, v) in enumerate(rows):
        A[i, 0] = 1
        A[i, 1] = mpf(n) ** (-alpha)
        y[i] = v
    sol = lu_solve(A.T * A, A.T * y)
    return sol[0], sol[1]


def main():
    rows = load()
    print("Single-term fits C + B n^(-alpha) on n = %d..%d\n" % (rows[0][0], rows[-1][0]))
    print("   alpha        C            above the peak %s?" % mp.nstr(PEAK, 4))
    all_above = True
    for alpha in (mpf("0.25"), mpf("0.5"), mpf(1), SIGMA0 - 1, mpf(2)):
        C, B = fit(rows, alpha)
        above = C > PEAK
        all_above &= above
        print("   %-10s %-12s %s" % (mp.nstr(alpha, 6), mp.nstr(C, 8), "yes" if above else "NO"))
    print()
    print("  every single-term fit exceeds the peak: %s" % all_above)
    print("  a sequence peaking at %s and descending has its limit BELOW that," % mp.nstr(PEAK, 4))
    print("  so none of these is a possible limit and the FORM is what fails.")
    print()
    print("  Test to apply to any proposed asymptotic: a single correction exponent cannot")
    print("  produce a turnover. At least two terms of opposite sign are needed, and the")
    print("  crossing near n = 27 should come out of them.")
    return 0 if all_above else 1


if __name__ == "__main__":
    sys.exit(main())
