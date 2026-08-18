#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent check of the spectral half of the Fold_6 non-lumpability theorem.

The paper's main theorem has four parts. Parts (i) and (iv) - the certificate package and
the 48-state minimal equitable refinement - already have verification scripts in this
directory. Parts (ii) and (iii) did not, and they are the ones that carry the
non-lumpability argument:

  (ii)  the audited residual satisfies  || T_6 M_6 - M_6 P_6 ||_inf = 1/4
  (iii) P_6 has eigenvalues in (0.4841207858, 0.4841207859) and
        (-0.6030939755, -0.6030939754), disjoint from the hypercube grid
        {1, 2/3, 1/3, 0, -1/3, -2/3, -1}

Everything is rebuilt from the definitions: Q_6 with the simple random walk kernel T_6, the
Zeckendorf-prefix fold giving the block indicator M_6, the fibre-size diagonal D, and
P_6 = D^{-1} M_6^T T_6 M_6. The residual is computed in exact rational arithmetic; the
eigenvalues are then located by exact rational bisection on the characteristic polynomial,
so no floating-point eigensolver is trusted for the interval claim.
"""
import sys
from fractions import Fraction as Fr
from itertools import product

N = 6
FIB = [0, 1, 1]
while len(FIB) < 40:
    FIB.append(FIB[-1] + FIB[-2])


def value(w):
    """N(omega) = sum_r a_r 2^(6-r): the word is read as a BINARY code, 0..63.

    This is the point of the construction and it is easy to get wrong. The fold is not
    Fibonacci-weighting of the input; it is the binary value of the word, re-expanded
    greedily in Fibonacci weights F_{r+1}, keeping the first six digits. A first attempt
    here put Fibonacci weights on the input instead. That wrong fold also produced 21
    cells over 64 vertices with a stochastic quotient, so every control passed, and it
    reproduced neither the residual nor the eigenvalues. Cell count alone does not
    identify the fold.
    """
    return sum(b * 2 ** (N - 1 - j) for j, b in enumerate(w))


def zeck_prefix(n, m):
    ks, rest, k = [], n, 2
    while FIB[k + 1] <= n:
        k += 1
    while rest > 0:
        while FIB[k] > rest:
            k -= 1
        ks.append(k)
        rest -= FIB[k]
        k -= 1
    out = ["0"] * m
    for k in ks:
        if 0 <= k - 2 < m:
            out[k - 2] = "1"
    return "".join(out)


def build():
    verts = list(product((0, 1), repeat=N))
    fold = {v: zeck_prefix(value(v), N) for v in verts}
    cells = sorted(set(fold.values()))
    idx = {c: i for i, c in enumerate(cells)}
    members = [[] for _ in cells]
    for v in verts:
        members[idx[fold[v]]].append(v)
    return verts, cells, idx, fold, members


def matmul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m)] for i in range(n)]


def char_poly(M):
    """Exact characteristic polynomial by the Faddeev-LeVerrier recursion."""
    n = len(M)
    I = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    Mk = [row[:] for row in I]
    coeffs = [Fr(1)]
    Ak = None
    for k in range(1, n + 1):
        Ak = matmul(M, Mk)
        c = -sum(Ak[i][i] for i in range(n)) / k
        coeffs.append(c)
        Mk = [[Ak[i][j] + (c if i == j else 0) for j in range(n)] for i in range(n)]
    return coeffs                      # p(x) = sum coeffs[i] x^(n-i)


def peval(coeffs, x):
    r = Fr(0)
    for c in coeffs:
        r = r * x + c
    return r


def root_in(coeffs, lo, hi, iters=200):
    """Exact bisection for a sign change; returns None if the endpoints do not bracket."""
    flo, fhi = peval(coeffs, lo), peval(coeffs, hi)
    if flo == 0:
        return lo
    if fhi == 0:
        return hi
    if (flo > 0) == (fhi > 0):
        return None
    for _ in range(iters):
        mid = (lo + hi) / 2
        fm = peval(coeffs, mid)
        if fm == 0:
            return mid
        if (fm > 0) == (flo > 0):
            lo, flo = mid, fm
        else:
            hi = mid
    return (lo + hi) / 2


def main():
    verts, cells, idx, fold, members = build()
    print("CONTROL 1  the fold gives the partition the paper describes")
    sizes = [len(m) for m in members]
    print(f"    cells: {len(cells)}   (paper says 21)")
    print(f"    total vertices covered: {sum(sizes)}   (must be 64)")
    ok = (len(cells) == 21) and (sum(sizes) == 64)
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    if not ok:
        print("The fold was reconstructed wrongly. No conclusions drawn.")
        return 1

    n = len(cells)
    # T_6 : simple random walk on Q_6
    T = [[Fr(0)] * 64 for _ in range(64)]
    vi = {v: i for i, v in enumerate(verts)}
    for v in verts:
        for b in range(N):
            w = list(v)
            w[b] ^= 1
            T[vi[v]][vi[tuple(w)]] = Fr(1, N)
    M = [[Fr(int(idx[fold[v]] == c)) for c in range(n)] for v in verts]
    TM = matmul(T, M)
    MtTM = matmul([[M[i][j] for i in range(64)] for j in range(n)], TM)
    P = [[MtTM[i][j] / sizes[i] for j in range(n)] for i in range(n)]

    print("CONTROL 2  P is a stochastic matrix")
    rows = {sum(P[i]) for i in range(n)}
    nonneg = all(P[i][j] >= 0 for i in range(n) for j in range(n))
    print(f"    row sums: {rows}   all entries nonnegative: {nonneg}")
    print(f"  -> {'PASS' if rows == {Fr(1)} and nonneg else 'FAIL'}\n")

    print("CLAIM (ii)  || T M - M P ||_inf")
    MP = matmul(M, P)
    resid = max(abs(TM[i][j] - MP[i][j]) for i in range(64) for j in range(n))
    rowmax = max(sum(abs(TM[i][j] - MP[i][j]) for j in range(n)) for i in range(64))
    print(f"    max entrywise residual : {resid}   (paper: 1/4 as an inf-norm)")
    print(f"    max absolute row sum   : {rowmax}")
    hit = (resid == Fr(1, 4)) or (rowmax == Fr(1, 4))
    print(f"  -> {'matches 1/4' if hit else 'does NOT match 1/4'}\n")

    print("CLAIM (iii)  two off-grid eigenvalues")
    cp = char_poly(P)
    grid = [Fr(1), Fr(2, 3), Fr(1, 3), Fr(0), Fr(-1, 3), Fr(-2, 3), Fr(-1)]
    ivs = [(Fr(4841207858, 10**10), Fr(4841207859, 10**10)),
           (Fr(-6030939755, 10**10), Fr(-6030939754, 10**10))]
    allok = True
    for lo, hi in ivs:
        r = root_in(cp, lo, hi)
        inside = r is not None
        if not inside:
            allok = False
        print(f"    interval ({float(lo):.10f}, {float(hi):.10f}): "
              f"{'root found at ' + format(float(r), '.12f') if inside else 'NO SIGN CHANGE'}")
    print(f"    grid values that are eigenvalues: "
          f"{[str(g) for g in grid if peval(cp, g) == 0]}")
    offgrid = all(not (lo <= g <= hi) for lo, hi in ivs for g in grid)
    print(f"    the two intervals avoid every grid value: {offgrid}")
    print(f"  -> {'PASS' if (allok and offgrid) else 'CHECK'}\n")

    print("SUMMARY", {"partition": ok, "residual 1/4": hit,
                      "eigenvalue intervals": allok, "off grid": offgrid})
    return 0 if (ok and hit and allok and offgrid) else 1


if __name__ == "__main__":
    sys.exit(main())
