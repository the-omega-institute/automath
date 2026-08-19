#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Are Sanna's own lambda_p also generic? Galois groups of his Table 1 polynomials.

t430 established that our Pi_q for q = 9..17 are the next rows of Sanna's published Table 1,
so the polynomials themselves are an extension of his table rather than a discovery. What is
not in his paper is any arithmetic of these numbers. Before claiming the Galois determination
as the manuscript's primary theorem it is worth knowing whether the answer is interesting or
automatic, and the cheapest way to find out is to run the same criterion on HIS rows.

If his p = 2..8 are all S_d too, then "the Galois group is the full symmetric group" is the
generic outcome across the whole family and a referee will read our nine values as a
computation continuing a pattern. If some of his are smaller, the family has arithmetic
structure and locating where it degenerates is a genuine result.

CRITERION, stated explicitly because I got this wrong once. At t425 I claimed "prime cycles"
of length 4 and 6; Jordan's theorem requires the cycle length to be prime. What is used here,
by degree:

  d = 3   G = S_3 unless disc(f) is a square, in which case G = A_3.
  d = 5   delegated to sympy's galois_group, which is exact in degree <= 6.
  d = 7   the degree is prime, so a transitive G is automatically primitive. A 3-cycle fixes
          4 >= 3 points, so Jordan gives A_7 <= G. An odd cycle type then gives S_7.
  d = 9   a transitive G containing a p-cycle with p prime and p > d/2 is primitive, so a
          5-cycle suffices; 5 <= 9 - 3 fixes 4 points, so Jordan gives A_9 <= G, and an odd
          cycle type gives S_9.

Cycle types come from Dedekind: for a prime P not dividing disc(f), the factorisation degrees
of f mod P are the cycle type of a Frobenius element of G.
"""
import sys

import sympy as sp

X = sp.symbols("x")

# Sanna, Table 1, arXiv:2309.12724v2. Coefficients high degree first.
SANNA = {
    2: [1, -2, -2, 2],
    3: [1, -2, -4, 2],
    4: [1, -2, -7, 0, -2, 2],
    5: [1, -2, -11, -8, -20, 10],
    6: [1, -2, -17, -28, -88, 26, -4, 4],
    7: [1, -2, -26, -74, -311, 34, -84, 42],
    8: [1, -2, -40, -174, -969, -2, -428, 174, -4, 4],
}


def poly(coeffs):
    d = len(coeffs) - 1
    return sp.Poly(sum(c * X ** (d - i) for i, c in enumerate(coeffs)), X)


def cycle_types(f, d, pmax=4000):
    """Dedekind: factorisation degrees mod P are a Frobenius cycle type."""
    disc = sp.discriminant(f)
    out = {}
    for P in sp.primerange(3, pmax):
        if disc % P == 0:
            continue
        fac = sp.factor_list(f.as_expr(), modulus=P)[1]
        if any(e > 1 for _, e in fac):
            continue
        t = tuple(sorted((sp.Poly(g, X).degree() for g, _ in fac), reverse=True))
        out.setdefault(t, P)
    return out, disc


def sign_of(t):
    """A cycle of length L is odd iff L is even; the permutation's sign is the product."""
    s = 1
    for L in t:
        if L % 2 == 0:
            s = -s
    return s


def verdict(d, types, disc):
    if d == 3:
        return ("S_3", "disc is not a square") if not sp.sqrt(disc).is_Integer \
            else ("A_3", "disc is a square")
    if d == 5:
        try:
            G, _ = sp.polys.numberfields.galoisgroups.galois_group(
                poly(SANNA_BY_DEG[d]), by_name=True)
            return (str(G), "sympy exact, degree <= 6")
        except Exception as exc:
            return ("?", f"sympy failed: {exc}")
    if d == 7:
        has3 = any(t.count(3) == 1 and set(t) <= {3, 1} for t in types)
        odd = any(sign_of(t) == -1 for t in types)
        if has3 and odd:
            return ("S_7", "prime degree gives primitivity; 3-cycle -> A_7; odd type -> S_7")
        return ("?", f"3-cycle {has3}, odd element {odd}")
    if d == 9:
        has5 = any(t.count(5) == 1 and set(t) <= {5, 1} for t in types)
        odd = any(sign_of(t) == -1 for t in types)
        if has5 and odd:
            return ("S_9", "5-cycle (5 > 9/2) -> primitive; 5 <= 9-3 -> A_9; odd type -> S_9")
        return ("?", f"5-cycle {has5}, odd element {odd}")
    return ("?", f"no criterion wired for degree {d}")


SANNA_BY_DEG = {}


def main():
    print("Galois groups of Sanna's own Table 1 polynomials\n")
    results = {}
    for p in sorted(SANNA):
        f = poly(SANNA[p])
        d = f.degree()
        SANNA_BY_DEG[d] = SANNA[p]
        if not f.is_irreducible:
            print(f"    p={p} degree {d}: REDUCIBLE, so not a minimal polynomial")
            results[p] = "reducible"
            continue
        types, disc = cycle_types(f, d)
        G, why = verdict(d, types, disc)
        results[p] = G
        print(f"    p={p}  degree {d}  G = {G}")
        print(f"          {why}")
        print(f"          {len(types)} distinct cycle types seen, e.g. "
              f"{sorted(types)[:4]}")
    print()
    allsym = all(str(v).startswith("S") for v in results.values())
    print(f"  every one of Sanna's rows is the full symmetric group: {allsym}")
    if allsym:
        print("  -> the generic answer holds across his rows as well, so our q = 9..17 "
              "continue\n     a pattern rather than breaking one. The Galois determination "
              "is real but it is\n     not a surprise, and the manuscript should not be "
              "written as though it were.")
    else:
        print("  -> at least one row degenerates; where the family stops being generic is "
              "worth\n     reporting and would strengthen the manuscript.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
