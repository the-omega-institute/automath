#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Common helpers for the diagonal-coupling rate function R_w(delta).

Paper-local convention:
  - Work with full-support distributions w on a finite set X.
  - For delta in (0, delta0) with delta0 = 1 - sum_x w(x)^2, the unique optimizer has the
    exponential-family / diagonal-enhanced form with parameters (kappa, u).
  - A canonical normalization is obtained by enforcing Z=1, which yields the scalar
    "overlap amplitude" A = sum_x u(x) satisfying a 1D fixed-point equation.

This module provides numerically stable, high-precision solvers for:
  - A(kappa): solve A = Phi_kappa(A).
  - (A, kappa)(delta): solve A = Phi_{kappa(A)}(A) with kappa = (1-A^2)/(A^2-delta).
  - R_w(delta) using the closed 1D expression.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, List, Tuple

import mpmath as mp


@dataclass(frozen=True)
class ScalarCollapseSolution:
    # Canonical parameters.
    A: mp.mpf
    kappa: mp.mpf
    u: List[mp.mpf]
    # Derived diagnostics.
    delta: mp.mpf
    delta0: mp.mpf
    diag_prob: mp.mpf
    Z: mp.mpf
    R: mp.mpf
    # Max residuals (numerical).
    max_marginal_residual: mp.mpf
    max_fixed_point_residual: mp.mpf


def _to_mpf_list(w: List[float | str | mp.mpf]) -> List[mp.mpf]:
    return [mp.mpf(ww) for ww in w]


def entropy(w: List[float | str | mp.mpf]) -> mp.mpf:
    ww = _to_mpf_list(w)
    return -mp.fsum([p * mp.log(p) for p in ww])


def p2(w: List[float | str | mp.mpf]) -> mp.mpf:
    ww = _to_mpf_list(w)
    return mp.fsum([p * p for p in ww])


def delta0_from_w(w: List[float | str | mp.mpf]) -> mp.mpf:
    return mp.mpf(1) - p2(w)


def _bisect_root(f: Callable[[mp.mpf], mp.mpf], lo: mp.mpf, hi: mp.mpf, *, tol: mp.mpf, max_iter: int) -> mp.mpf:
    flo = f(lo)
    fhi = f(hi)
    if flo == 0:
        return lo
    if fhi == 0:
        return hi
    if flo * fhi > 0:
        raise ValueError("Root is not bracketed.")

    for _ in range(max_iter):
        mid = (lo + hi) / 2
        fmid = f(mid)
        if abs(fmid) <= tol:
            return mid
        # keep a bracketing interval
        if flo * fmid < 0:
            hi, fhi = mid, fmid
        else:
            lo, flo = mid, fmid
        if abs(hi - lo) <= tol * (mp.mpf(1) + abs(mid)):
            break
    return (lo + hi) / 2


def _u_kappa_A(w: List[mp.mpf], kappa: mp.mpf, A: mp.mpf) -> List[mp.mpf]:
    if kappa <= 0:
        raise ValueError("Expected kappa > 0.")
    out: List[mp.mpf] = []
    two_k = 2 * kappa
    for wx in w:
        out.append((mp.sqrt(A * A + 4 * kappa * wx) - A) / two_k)
    return out


def solve_A_for_kappa(
    w: List[float | str | mp.mpf],
    kappa: float | str | mp.mpf,
    *,
    dps: int = 80,
    tol: float | str | mp.mpf | None = None,
    max_iter: int = 200,
) -> Tuple[mp.mpf, List[mp.mpf]]:
    """Solve A = Phi_kappa(A) for a given kappa>0, returning (A, u)."""
    mp.mp.dps = int(dps)
    ww = _to_mpf_list(w)
    kk = mp.mpf(kappa)
    if kk <= 0:
        raise ValueError("Expected kappa > 0.")
    t = mp.mpf(tol) if tol is not None else mp.mpf(10) ** (-(mp.mp.dps // 2))

    def F(A: mp.mpf) -> mp.mpf:
        u = _u_kappa_A(ww, kk, A)
        return A - mp.fsum(u)

    lo = mp.mpf(0)
    hi = mp.mpf(1)
    # Ensure bracketing: F(lo)<0, F(hi)>0 (typically true), otherwise expand hi.
    flo = F(lo)
    fhi = F(hi)
    if flo * fhi > 0:
        hi = mp.mpf(2)
        fhi = F(hi)
    if flo * fhi > 0:
        raise RuntimeError("Failed to bracket A fixed point for kappa.")

    A_star = _bisect_root(F, lo, hi, tol=t, max_iter=max_iter)
    u_star = _u_kappa_A(ww, kk, A_star)
    return A_star, u_star


def solve_scalar_collapse(
    w: List[float | str | mp.mpf],
    delta: float | str | mp.mpf,
    *,
    dps: int = 80,
    tol: float | str | mp.mpf | None = None,
    max_iter: int = 250,
) -> ScalarCollapseSolution:
    """
    Solve the scalar-collapse parameterization for a given delta.

    Returns the canonical (A,kappa,u) with Z=1, the optimizer coupling P_kappa, and R_w(delta).
    """
    mp.mp.dps = int(dps)
    ww = _to_mpf_list(w)
    dd = mp.mpf(delta)
    if not (dd >= 0):
        raise ValueError("Expected delta >= 0.")
    if any(p <= 0 for p in ww):
        raise ValueError("Expected full support: all w(x) > 0.")
    if abs(mp.fsum(ww) - 1) > mp.mpf("1e-18"):
        raise ValueError("Expected sum_x w(x) = 1.")

    d0 = delta0_from_w(ww)
    if dd >= d0:
        # Independent coupling is feasible, rate is zero.
        return ScalarCollapseSolution(
            A=mp.mpf(1),
            kappa=mp.mpf(0),
            u=ww[:],
            delta=dd,
            delta0=d0,
            diag_prob=mp.fsum([p * p for p in ww]),
            Z=mp.mpf(1),
            R=mp.mpf(0),
            max_marginal_residual=mp.mpf(0),
            max_fixed_point_residual=mp.mpf(0),
        )

    if dd <= 0:
        raise ValueError("This solver expects delta in (0, delta0).")

    t = mp.mpf(tol) if tol is not None else mp.mpf(10) ** (-(mp.mp.dps // 2))
    eps = mp.mpf(10) ** (-(mp.mp.dps // 3))

    # Root in A in (sqrt(delta), 1).
    sqrt_d = mp.sqrt(dd)
    lo = sqrt_d + eps
    hi = mp.mpf(1) - eps

    def F(A: mp.mpf) -> mp.mpf:
        if not (A * A > dd):
            return mp.mpf(1)  # outside domain; keep sign positive near the left boundary
        kappa = (mp.mpf(1) - A * A) / (A * A - dd)
        u = _u_kappa_A(ww, kappa, A)
        return A - mp.fsum(u)

    flo = F(lo)
    fhi = F(hi)
    if flo * fhi > 0:
        # Try a slightly different bracket (numerically safer).
        lo2 = sqrt_d + mp.mpf(10) * eps
        hi2 = mp.mpf(1) - mp.mpf(10) * eps
        flo, fhi, lo, hi = F(lo2), F(hi2), lo2, hi2
    if flo * fhi > 0:
        raise RuntimeError("Failed to bracket A for given delta.")

    A_star = _bisect_root(F, lo, hi, tol=t, max_iter=max_iter)
    k_star = (mp.mpf(1) - A_star * A_star) / (A_star * A_star - dd)
    u_star = _u_kappa_A(ww, k_star, A_star)

    # Diagnostics (should satisfy A = sum u, and w = A u + kappa u^2).
    fixed_res = abs(A_star - mp.fsum(u_star))
    marg_res = mp.mpf(0)
    for wx, ux in zip(ww, u_star):
        marg_res = max(marg_res, abs(wx - (A_star * ux + k_star * ux * ux)))

    sum_u2 = mp.fsum([ux * ux for ux in u_star])
    Z = A_star * A_star + k_star * sum_u2
    diag_prob = (mp.mpf(1) + k_star) * sum_u2
    delta_check = mp.mpf(1) - diag_prob

    # Rate expression under Z=1 normalization.
    R = 2 * mp.fsum([wx * mp.log(ux / wx) for wx, ux in zip(ww, u_star)]) + diag_prob * mp.log(1 + k_star)

    return ScalarCollapseSolution(
        A=A_star,
        kappa=k_star,
        u=u_star,
        delta=delta_check,
        delta0=d0,
        diag_prob=diag_prob,
        Z=Z,
        R=R,
        max_marginal_residual=marg_res,
        max_fixed_point_residual=fixed_res,
    )

