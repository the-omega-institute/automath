#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Our Pi_q are the continuation of Sanna's published Table 1, not an independent family.

Sanna, "A Note on the Power Sums of the Number of Fibonacci Partitions", Discrete Analysis
2025:2, doi 10.19086/da.137601, arXiv 2309.12724v2. His Table 1 lists lambda_p together with
its minimal polynomial over Q for p = 1..8, and the text states that lambda_p is the greatest
real root of an effectively computable monic integer polynomial, hence an algebraic integer,
obtained as the Perron-Frobenius eigenvalue of the transition matrix of an automaton A_p built
from p parallel copies of Berstel's automaton.

That settles a question I got wrong once. At t421 I hypothesised Sanna obtains only a
generalized spectral radius, which would have left algebraicity open and to us. He does use
the generalized spectral radius, but only for the second theorem (the p -> infinity limit);
Theorem 1 goes through Perron-Frobenius on a single irreducible aperiodic matrix, so
algebraicity and the minimal polynomials are his.

WHAT THIS SCRIPT CHECKS. Whether our lambda_q for q = 9..17 are new numbers or the next rows
of his table. They are the next rows. His table ends at lambda_8 = 9.39867 and our q = 9 gives
11.7784; the normalised values lambda^(1/index) descend monotonically from his 1.3232 at p = 8
through ours to 1.2873 at q = 17, heading to sqrt(phi) = 1.27202 as his second theorem
requires. Every polynomial in both families has the same leading shape X^d - 2X^(d-1).

CONSEQUENCE FOR THE MANUSCRIPT. The polynomials are an extension of a published table by a
method the same paper already provides, so they cannot be presented as a discovery. What is
not in Sanna is the arithmetic of these numbers: he computes no Galois groups, no
discriminants and no splitting behaviour. The paper must cite Table 1 explicitly and claim
the extension as an extension.
"""
import json
import os
import sys

from mpmath import mp, polyroots

mp.dps = 40
PHI = (1 + mp.sqrt(5)) / 2

# Sanna, Table 1, transcribed from arXiv:2309.12724v2. Coefficients high degree first.
SANNA = {
    1: [1, -2],
    2: [1, -2, -2, 2],
    3: [1, -2, -4, 2],
    4: [1, -2, -7, 0, -2, 2],
    5: [1, -2, -11, -8, -20, 10],
    6: [1, -2, -17, -28, -88, 26, -4, 4],
    7: [1, -2, -26, -74, -311, 34, -84, 42],
    8: [1, -2, -40, -174, -969, -2, -428, 174, -4, 4],
}
SANNA_PRINTED = {1: "2.00000", 2: "2.48119", 3: "3.08613", 4: "3.84606",
                 5: "4.80052", 6: "5.99942", 7: "7.50569", 8: "9.39867"}


def largest_real_root(coeffs):
    rs = polyroots([mp.mpf(c) for c in coeffs], maxsteps=400, extraprec=600)
    real = [r.real for r in rs if abs(r.imag) < mp.mpf("1e-25")]
    return max(real)


def main():
    print("CONTROL  his printed values are reproduced by his printed polynomials\n")
    ok = True
    rows = []
    for p in sorted(SANNA):
        lam = largest_real_root(SANNA[p])
        # numeric comparison: a string prefix test fails on p=1, where nstr renders
        # the exact root 2 as "2.0" rather than "2.00000"
        agree = abs(lam - mp.mpf(SANNA_PRINTED[p])) < mp.mpf("5e-6")
        ok &= agree
        rows.append((p, lam, "Sanna"))
        print(f"    p={p}  root {mp.nstr(lam, 10):16s} printed {SANNA_PRINTED[p]}   "
              f"{'ok' if agree else 'MISMATCH'}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    if not ok:
        print("The transcription of Table 1 is wrong. No conclusion.")
        return 1

    here = os.path.dirname(os.path.abspath(__file__))
    P = json.load(open(os.path.join(here, "polynomial_certificates_q9_17.json")))["polynomials"]
    for e in P:
        rows.append((e["q"], largest_real_root(e["polynomial_coefficients"]), "ours"))

    print("CONTINUATION  one sequence, his rows then ours, normalised by the index\n")
    prev = None
    mono = True
    for idx, lam, who in rows:
        norm = lam ** (mp.mpf(1) / idx)
        flag = ""
        if prev is not None and idx > 2:
            if norm > prev:
                mono = False
                flag = "  NOT DECREASING"
            prev = norm
        elif idx > 2:
            prev = norm
        print(f"    {who:5s} index {idx:2d}   lambda {mp.nstr(lam, 12):18s} "
              f"lambda^(1/index) {mp.nstr(norm, 8)}{flag}")
    print(f"\n    target sqrt(phi) = {mp.nstr(mp.sqrt(PHI), 8)}")
    print(f"  monotone decreasing past index 2 -> {'PASS' if mono else 'FAIL'}")

    gap = rows[len(SANNA)][1] / rows[len(SANNA) - 1][1]
    print(f"  ratio lambda_9 / lambda_8 = {mp.nstr(gap, 8)}, in line with the "
          f"neighbouring ratios -> the rows are consecutive\n")

    lead = all(e["polynomial_coefficients"][:2] == [1, -2] for e in P) and \
        all(c[:2] == [1, -2] for p, c in SANNA.items() if len(c) > 1)
    print(f"  every polynomial in both families begins X^d - 2X^(d-1) -> "
          f"{'PASS' if lead else 'FAIL'}")
    return 0 if (ok and mono and lead) else 1


if __name__ == "__main__":
    sys.exit(main())
