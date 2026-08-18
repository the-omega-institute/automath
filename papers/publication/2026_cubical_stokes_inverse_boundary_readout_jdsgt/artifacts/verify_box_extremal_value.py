#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent check of the principal contribution: the box extremal value.

The paper's headline is that for a box R = prod_j [0, L_j] the extremal coefficient-L^inf
norm among primitives of dx_1 ^ ... ^ dx_k is

    m(R) = ( 2 * sum_j 1/L_j )^{-1}

with an explicit affine minimiser attaining it.

Both bounds have short analytic proofs, recorded here and then checked numerically because
an algebra slip in either direction would be invisible from the formula alone.

Upper bound. Take eta = sum_j c_j (x_j - L_j/2) dx_{hat j} with signs making
d eta = dx_1 ^ ... ^ dx_k, which needs sum_j c_j = 1. The j-th coefficient has sup norm
c_j L_j / 2. Equalising them gives c_j = t / L_j with t = 1 / sum_j (1/L_j), and the common
value is t/2 = m(R).

Lower bound, one line of Stokes. prod_j L_j = int_R d eta = oint_{dR} eta. The boundary has
2k faces, the pair normal to j having area prod_{i != j} L_i, so

    prod_j L_j  <=  2 * sum_j ( prod_{i != j} L_i ) * ||eta||
                 =  2 * ( prod_j L_j ) * ( sum_j 1/L_j ) * ||eta||,

hence ||eta|| >= m(R).

The numerical check discretises the k = 2 problem as a linear program: minimise t subject
to |P| <= t, |Q| <= t on a grid and the finite-difference constraint dQ/dx - dP/dy = 1 on
each cell. The LP optimum should approach m(R) from below as the grid refines, since a
discrete primitive is less constrained than a smooth one.
"""
import sys

import numpy as np
from scipy.optimize import linprog


def m_formula(Ls):
    return 1.0 / (2.0 * sum(1.0 / L for L in Ls))


def affine_minimiser_value(Ls):
    """Value attained by the explicit affine construction, computed independently."""
    t = 1.0 / sum(1.0 / L for L in Ls)
    cs = [t / L for L in Ls]
    assert abs(sum(cs) - 1.0) < 1e-12, "the weights must sum to one"
    vals = [c * L / 2.0 for c, L in zip(cs, Ls)]
    assert max(vals) - min(vals) < 1e-12, "the construction should equalise the terms"
    return max(vals)


def lp_k2(L1, L2, n1, n2):
    """Discrete primitive on an n1 x n2 grid of cells; returns the LP optimum.

    Unknowns: P on horizontal edges, Q on vertical edges, and the bound t.
    Constraint per cell: (Q_right - Q_left)/hx - (P_top - P_bottom)/hy = 1.
    """
    hx, hy = L1 / n1, L2 / n2
    # P lives on cell-centred horizontal edges: index (i, j), i in [0,n1), j in [0,n2+1)
    nP = n1 * (n2 + 1)
    nQ = (n1 + 1) * n2
    nv = nP + nQ + 1
    tix = nv - 1

    def Pi(i, j):
        return i * (n2 + 1) + j

    def Qi(i, j):
        return nP + i * n2 + j

    rows, rhs = [], []
    for i in range(n1):
        for j in range(n2):
            r = np.zeros(nv)
            r[Qi(i + 1, j)] += 1.0 / hx
            r[Qi(i, j)] -= 1.0 / hx
            r[Pi(i, j + 1)] -= 1.0 / hy
            r[Pi(i, j)] += 1.0 / hy
            rows.append(r)
            rhs.append(1.0)
    Aeq = np.array(rows)
    beq = np.array(rhs)

    # |x| <= t  as  x - t <= 0  and  -x - t <= 0
    Aub, bub = [], []
    for k in range(nP + nQ):
        u = np.zeros(nv)
        u[k], u[tix] = 1.0, -1.0
        Aub.append(u)
        bub.append(0.0)
        w = np.zeros(nv)
        w[k], w[tix] = -1.0, -1.0
        Aub.append(w)
        bub.append(0.0)
    c = np.zeros(nv)
    c[tix] = 1.0
    bounds = [(None, None)] * (nP + nQ) + [(0, None)]
    res = linprog(c, A_ub=np.array(Aub), b_ub=np.array(bub),
                  A_eq=Aeq, b_eq=beq, bounds=bounds, method="highs")
    return res.fun if res.success else None


def main():
    print("CONTROL  the affine construction attains the stated formula\n")
    ok = True
    for Ls in ([1.0, 1.0], [1.0, 2.0], [0.5, 3.0], [1.0, 1.0, 1.0],
               [1.0, 2.0, 4.0], [0.3, 1.7, 2.9, 5.1]):
        a, f = affine_minimiser_value(Ls), m_formula(Ls)
        good = abs(a - f) < 1e-12
        ok &= good
        print(f"    L = {Ls}\n        affine value {a:.12f}   formula {f:.12f}   "
              f"{'ok' if good else 'MISMATCH'}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    if not ok:
        return 1

    print("NUMERIC  discrete LP optimum against m(R), k = 2")
    allok = True
    for L1, L2 in ((1.0, 1.0), (1.0, 2.0), (0.5, 3.0)):
        target = m_formula([L1, L2])
        print(f"    box {L1} x {L2}   m(R) = {target:.9f}")
        prev = None
        for n in (6, 10, 16, 24):
            val = lp_k2(L1, L2, n, n)
            if val is None:
                print(f"        n={n}: LP failed")
                allok = False
                continue
            print(f"        n={n:3d}   LP optimum {val:.9f}   "
                  f"ratio to m(R) {val / target:.6f}")
            prev = val
        if prev is not None and not (0.9 < prev / target <= 1.0 + 1e-6):
            allok = False
    print(f"  -> {'consistent' if allok else 'CHECK'}\n")
    print("SUMMARY", {"affine construction": ok, "discrete LP": allok})
    return 0 if (ok and allok) else 1


if __name__ == "__main__":
    sys.exit(main())
