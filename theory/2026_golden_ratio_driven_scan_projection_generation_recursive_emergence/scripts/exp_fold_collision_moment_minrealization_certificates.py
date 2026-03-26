#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Certificates: minimal linear realization dimension for higher collision moments S_k(m).

For Fold_m fibers, define:
  S_k(m) = sum_{x in X_m} d_m(x)^k.

For each k we:
1) Compute S_k(m) via modular DP residue counts c_m(r) modulo F_{m+2}.
2) Fit the minimal exact integer recurrence order d on a fixed audit window.
3) Exhibit a nonzero dxd Hankel minor for a_n := S_k(n+2) (Hankel rank >= d).
4) Conclude Hankel rank = d (since linear recurrence of order d implies rank <= d),
   hence minimal linear realization dimension is exactly d.
5) Emit a canonical Hankel-normal-form witness (paper: HANKELNF_q) from a finite
   2d-sample window: (d, ell; H0^(ell), H1^(ell); A, alpha, beta), with
     A := (H0^(ell))^{-1} H1^(ell), alpha^T := (a_ell,...,a_{ell+d-1}), beta := e0.

Output:
  - artifacts/export/fold_collision_moment_minrealization_certificates.json

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir
from common_phi_fold import Progress
from exp_fold_collision_moment_recursions_mod_dp import PRECOMPUTED_RECS_9_17, counts_mod_fib, moments_from_counts


def det_int_matrix(A: List[List[int]]) -> int:
    """Exact determinant via fraction-free Gaussian elimination (Bareiss)."""
    n = len(A)
    if n == 0:
        return 1
    M = [row[:] for row in A]
    det_sign = 1
    prev_pivot = 1
    for k in range(n - 1):
        if M[k][k] == 0:
            piv = None
            for i in range(k + 1, n):
                if M[i][k] != 0:
                    piv = i
                    break
            if piv is None:
                return 0
            M[k], M[piv] = M[piv], M[k]
            det_sign *= -1
        pivot = M[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * pivot - M[i][k] * M[k][j]) // prev_pivot
            M[i][k] = 0
        prev_pivot = pivot
    return det_sign * M[n - 1][n - 1]


def hankel_block(a: List[int], d: int, offset: int) -> List[List[int]]:
    return [[a[offset + i + j] for j in range(d)] for i in range(d)]


def build_recurrence_rows(seq_by_m: Dict[int, int], order: int, m_start: int, m_end: int) -> Tuple[List[List[int]], List[int]]:
    rows: List[List[int]] = []
    rhs: List[int] = []
    for m in range(m_start, m_end + 1):
        if m - order < min(seq_by_m.keys()):
            continue
        rows.append([seq_by_m[m - i] for i in range(1, order + 1)])
        rhs.append(seq_by_m[m])
    return rows, rhs


def solve_integer_recurrence(seq_by_m: Dict[int, int], order: int, m0: int, m_max: int) -> List[int] | None:
    """
    Try to solve integer coefficients c_1..c_d using data rows from m in [m0..m_max].
    Uses a greedy rank-growing selection to pick an invertible dxd subsystem.
    """
    rows, rhs = build_recurrence_rows(seq_by_m, order=order, m_start=m0, m_end=m_max)
    if len(rows) < order:
        return None

    A_sel: List[List[int]] = []
    b_sel: List[int] = []
    A_rank = 0
    for r, b in zip(rows, rhs, strict=True):
        if len(A_sel) == 0:
            A_sel.append(r)
            b_sel.append(b)
            A_rank = sp.Matrix([r]).rank()
            continue
        A_try = sp.Matrix(A_sel + [r])
        rk = A_try.rank()
        if rk > A_rank:
            A_sel.append(r)
            b_sel.append(b)
            A_rank = rk
        if len(A_sel) == order:
            break

    if len(A_sel) < order:
        return None
    A_sq = sp.Matrix(A_sel)
    if A_sq.det() == 0:
        return None
    b_sq = sp.Matrix(b_sel)
    sol = A_sq.LUsolve(b_sq)
    coeffs = [sp.nsimplify(x) for x in sol]
    if any((not x.is_rational) or (x.q != 1) for x in coeffs):
        return None
    return [int(x) for x in coeffs]


def verify_recurrence(seq_by_m: Dict[int, int], coeffs: List[int], m0: int, m_max: int) -> List[Tuple[int, int, int]]:
    d = len(coeffs)
    mism: List[Tuple[int, int, int]] = []
    for m in range(m0, m_max + 1):
        if m - d < min(seq_by_m.keys()):
            continue
        rhs = 0
        for i, c in enumerate(coeffs, start=1):
            rhs += c * seq_by_m[m - i]
        lhs = seq_by_m[m]
        if lhs != rhs:
            mism.append((m, lhs, rhs))
    return mism


def find_min_recurrence(seq_by_m: Dict[int, int], order_max: int, m_min: int, m_max: int) -> Tuple[int, int, List[int]]:
    """Return (order, start_m0, coeffs) for the smallest order with exact verification on [m0..m_max]."""
    for d in range(1, order_max + 1):
        for m0 in range(m_min + d, m_max + 1):
            coeffs = solve_integer_recurrence(seq_by_m, order=d, m0=m0, m_max=m_max)
            if coeffs is None:
                continue
            mism = verify_recurrence(seq_by_m, coeffs, m0=m0, m_max=m_max)
            if not mism:
                return d, m0, coeffs
    raise RuntimeError("Failed to fit an exact integer recurrence within order_max.")


@dataclass(frozen=True)
class HankelNF:
    """
    Canonical Hankel-normal-form witness built from a finite 2d window.

    We store A entries as strings (exact SymPy rationals) to keep the certificate
    JSON round-trip stable.
    """

    d: int
    ell: int
    H0: List[List[int]]
    H1: List[List[int]]
    A: List[List[str]]
    alpha: List[int]
    beta: List[int]
    sample_m: List[int]
    sample_S: List[int]


@dataclass(frozen=True)
class Certificate:
    k: int
    m_min: int
    m_max: int
    recurrence_order: int
    recurrence_m0: int
    recurrence_coeffs: List[int]
    hankel_d: int
    hankel_offset: int
    hankel_det: int
    hankel_nf: HankelNF


def main() -> None:
    parser = argparse.ArgumentParser(description="Certificates: minimal realization dimensions for S_k(m).")
    parser.add_argument("--k-list", type=str, default="9,10,11,12", help="Comma-separated k values.")
    parser.add_argument("--m-min", type=int, default=2)
    parser.add_argument("--m-max", type=int, default=26)
    parser.add_argument("--order-max", type=int, default=15)
    parser.add_argument("--offset-max", type=int, default=10)
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_moment_minrealization_certificates.json"),
    )
    args = parser.parse_args()

    ks = [int(s.strip()) for s in str(args.k_list).split(",") if s.strip()]
    if not ks:
        raise SystemExit("Empty --k-list")
    if any(k < 2 for k in ks):
        raise SystemExit("All k must be >= 2")
    k_max = max(ks)

    m_min = int(args.m_min)
    m_max_user = int(args.m_max)
    if m_min < 2 or m_max_user < m_min:
        raise SystemExit("Require m_max >= m_min >= 2")

    prog = Progress("minreal-certs", every_seconds=20.0)

    # If the precomputed table knows the (order, m0) for some k, ensure the
    # audit window is long enough to *solve* a dxd system (needs at least d rows):
    # require m_max >= m0 + d - 1.
    pre_by_k: Dict[int, Tuple[int, int]] = {}
    for r in PRECOMPUTED_RECS_9_17:
        kk = int(r["k"])
        dd = int(r["order"])
        m0 = int(r["m0"])
        pre_by_k[kk] = (dd, m0)

    m_max_req = m_max_user
    for k in ks:
        if k in pre_by_k:
            dd, m0 = pre_by_k[k]
            m_max_req = max(m_max_req, m0 + dd - 1)

    m_max = int(m_max_req)
    if m_max != m_max_user:
        print(f"[minreal-certs] auto-extended m_max: user={m_max_user} -> {m_max} (to fit known recurrences)", flush=True)

    # Compute all S_k(m) for k up to k_max in one pass over m.
    S: Dict[int, Dict[int, int]] = {k: {} for k in ks}
    for m in range(m_min, m_max + 1):
        c = counts_mod_fib(m, prog=prog)
        moms = moments_from_counts(c, k_max=k_max)
        for k in ks:
            S[k][m] = moms[k]
        print(f"[minreal-certs] m={m} mod={len(c)} computed k<= {k_max}", flush=True)

    certs: List[Certificate] = []
    for k in ks:
        seq = S[k]
        d, m0, coeffs = find_min_recurrence(seq, order_max=int(args.order_max), m_min=m_min, m_max=m_max)
        print(f"[minreal-certs] k={k} recurrence: order={d} starts_at_m={m0}", flush=True)

        hankel_d = d
        # For a dxd Hankel block at offset r we need:
        #   H0^(r) uses a_{r..r+2d-2}  -> S_k(m) up to m = r + 2d
        #   H1^(r) uses a_{r+1..r+2d-1} -> S_k(m) up to m = r + 2d + 1
        # Hence we require r <= m_max - (2d+1) to form both H0^(r), H1^(r).
        off_cap = min(int(args.offset_max), m_max - (2 * hankel_d + 1))
        if off_cap < 0:
            raise SystemExit(
                f"Need m_max >= {2*hankel_d + 1} to form both H0/H1 for a {hankel_d}x{hankel_d} Hankel witness at offset 0 "
                f"(got m_max={m_max})."
            )
        # Need a up to index (off_cap + 2d - 1) to build H1 at off_cap.
        n_need = off_cap + (2 * hankel_d - 1)
        a = [seq[n + 2] for n in range(n_need + 1)]

        found_off = None
        found_det = None
        for off in range(0, off_cap + 1):
            H = hankel_block(a, d=hankel_d, offset=off)
            detH = det_int_matrix(H)
            if detH != 0:
                found_off = off
                found_det = detH
                break
        if found_off is None or found_det is None:
            raise SystemExit(f"Failed to find nonzero {hankel_d}x{hankel_d} Hankel minor for k={k}.")

        print(f"[minreal-certs] k={k} Hankel witness: d={hankel_d} off={found_off} det!=0", flush=True)
        ell = int(found_off)
        H0 = hankel_block(a, d=hankel_d, offset=ell)
        H1 = hankel_block(a, d=hankel_d, offset=ell + 1)
        A = sp.Matrix(H0).LUsolve(sp.Matrix(H1))
        alpha = [int(a[ell + i]) for i in range(hankel_d)]
        beta = [1] + [0] * (hankel_d - 1)
        sample_m = [ell + 2 + i for i in range(2 * hankel_d)]
        sample_S = [int(seq[m]) for m in sample_m]
        hankel_nf = HankelNF(
            d=int(hankel_d),
            ell=int(ell),
            H0=[[int(x) for x in row] for row in H0],
            H1=[[int(x) for x in row] for row in H1],
            A=[[str(A[i, j]) for j in range(A.cols)] for i in range(A.rows)],
            alpha=[int(x) for x in alpha],
            beta=[int(x) for x in beta],
            sample_m=[int(x) for x in sample_m],
            sample_S=[int(x) for x in sample_S],
        )
        certs.append(
            Certificate(
                k=int(k),
                m_min=m_min,
                m_max=m_max,
                recurrence_order=int(d),
                recurrence_m0=int(m0),
                recurrence_coeffs=[int(x) for x in coeffs],
                hankel_d=int(hankel_d),
                hankel_offset=int(found_off),
                hankel_det=int(found_det),
                hankel_nf=hankel_nf,
            )
        )

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(
            {
                "m_min": m_min,
                "m_max_user": m_max_user,
                "m_max_used": m_max,
                "k_list": ks,
                "certificates": [asdict(c) for c in certs],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    print(f"[minreal-certs] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

