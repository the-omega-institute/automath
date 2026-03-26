#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Exact q=18..25 Fold collision fingerprints (recurrence + spectrum).

We work with Fold_m fiber multiplicities d_m(x)=|Fold_m^{-1}(x)| and collision moments:
  S_q(m) := sum_x d_m(x)^q.

Using the congruence form (residue DP modulo Fibonacci):
  S_q(m) = sum_{r mod F_{m+2}} c_m(r)^q,
where c_m(r) counts subset sums of Fibonacci weights modulo F_{m+2}.

For each q in [q_min..q_max] we:
  1) compute S_q(m) on an audit window m∈[m_min..m_max],
  2) fit a *small* exact integer recurrence
       S(m) = sum_{i=1..d} c_i S(m-i)
     by solving a square linear system at m0=d+2 (paper-canonical pattern) and
     verifying on the full audit window,
  3) certify minimality via a nonzero d×d Hankel minor (rank >= d),
  4) compute spectral fingerprints from the characteristic polynomial
       P_q(x) = x^d - c_1 x^{d-1} - ... - c_d:
       - r_q      : Perron root (dominant modulus; positive real),
       - Lambda_q : subdominant spectral modulus (max |mu|, mu != r_q),
       - gapratio : Lambda_q / r_q,
       - beta_q   : log Lambda_q / log r_q,
       - h_q      : log(2^q / r_q),
       - h_q^R    : h_q / (q-1),
       - Delta_q  : (2*floor(q/2)+1) - d.

Outputs (default):
  - artifacts/export/fold_collision_moment_signature_q18_25.json

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import numpy as np
import sympy as sp

from common_mod_fib_dp import counts_mod_fib
from common_paths import export_dir
from common_phi_fold import Progress


def moments_for_qs_from_counts(c: np.ndarray, qs: Iterable[int]) -> Dict[int, int]:
    """Compute S_q = sum_r c[r]^q for selected q values as exact Python ints.

    For our ranges (m<=35) the counts c[r] are typically small (~10^3), so using
    a bincount histogram avoids the expensive sort in np.unique.
    """
    qs_list = sorted(set(int(q) for q in qs))
    if any(q < 2 for q in qs_list):
        raise ValueError("all q must be >= 2")
    # Histogram: freq[v] = #{r : c[r]=v}.
    # np.bincount supports uint64 on modern numpy; fall back to int64 cast if needed.
    try:
        freq = np.bincount(c)  # type: ignore[arg-type]
    except TypeError:
        freq = np.bincount(c.astype(np.int64))
    idx = np.nonzero(freq)[0]
    freq_py = [int(freq[i]) for i in idx.tolist()]
    vals_py = [int(i) for i in idx.tolist()]

    out: Dict[int, int] = {}
    for q in qs_list:
        s = 0
        for v, f in zip(vals_py, freq_py, strict=True):
            # v is small; pow is exact.
            s += f * (v**q)
        out[q] = int(s)
    return out


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


def hankel_minor(a: List[int], d: int, offset: int = 0) -> List[List[int]]:
    """Return dxd Hankel matrix H_{ij} = a[offset + i + j]."""
    return [[a[offset + i + j] for j in range(d)] for i in range(d)]


def _poly_from_coeffs(coeffs: List[int]) -> sp.Expr:
    d = len(coeffs)
    x = sp.Symbol("x")
    poly = x**d
    for i, c in enumerate(coeffs, start=1):
        poly -= int(c) * x ** (d - i)
    return sp.expand(poly)


def _roots(poly: sp.Expr, *, dps: int) -> List[complex]:
    roots = sp.nroots(poly, n=int(dps), maxsteps=500)
    return [complex(sp.re(r).evalf(dps), sp.im(r).evalf(dps)) for r in roots]


def _perron_and_subdominant(roots: List[complex]) -> Tuple[float, float, complex]:
    roots_sorted = sorted(roots, key=lambda z: -abs(z))
    r = roots_sorted[0]
    if abs(r.imag) > 1e-14:
        raise RuntimeError(f"dominant root is not (numerically) real: {r}")
    if r.real <= 0:
        raise RuntimeError(f"dominant root is not positive: {r.real}")
    rq = float(r.real)

    tol = 1e-10
    others = [z for z in roots_sorted if abs(z - r) > tol]
    if not others:
        return rq, 0.0, 0.0 + 0.0j
    mu_star = max(others, key=lambda z: abs(z))
    Lambda = float(abs(mu_star))
    return rq, Lambda, mu_star


def _build_recurrence_rows(
    seq_by_m: Dict[int, int],
    *,
    d: int,
    m_start: int,
    m_end: int,
) -> Tuple[List[List[int]], List[int]]:
    """Build rows for S(m)=sum_{i=1..d} c_i S(m-i) on m in [m_start..m_end]."""
    rows: List[List[int]] = []
    rhs: List[int] = []
    for m in range(m_start, m_end + 1):
        if (m - d) < min(seq_by_m.keys()):
            continue
        rows.append([seq_by_m[m - i] for i in range(1, d + 1)])
        rhs.append(seq_by_m[m])
    return rows, rhs


def solve_integer_recurrence(
    seq_by_m: Dict[int, int],
    *,
    d: int,
    m0: int,
    m_max: int,
) -> List[int] | None:
    """Solve integer coefficients c_1..c_d by trying consecutive d×d windows.

    Compared to a rank-growing selection, this is faster and often sufficient in
    our audit windows. If all consecutive windows are singular, callers should
    increase m_max (more equations) or implement a more sophisticated row selection.
    """
    m_end_solve = min(m0 + 3 * d, m_max)
    rows, rhs = _build_recurrence_rows(seq_by_m, d=d, m_start=m0, m_end=m_end_solve)
    n = len(rows)
    if n < d:
        return None

    for s in range(0, n - d + 1):
        A_sq = sp.Matrix(rows[s : s + d])
        b_sq = sp.Matrix(rhs[s : s + d])
        try:
            sol = A_sq.LUsolve(b_sq)  # exact rationals
        except Exception:
            continue
        coeffs = [sp.nsimplify(x) for x in sol]
        if any((not x.is_rational) or (x.q != 1) for x in coeffs):
            continue
        return [int(x) for x in coeffs]
    return None


def verify_recurrence(seq_by_m: Dict[int, int], coeffs: List[int], *, m0: int, m_max: int) -> bool:
    d = len(coeffs)
    for m in range(m0, m_max + 1):
        if m - d < min(seq_by_m.keys()):
            continue
        rhs = 0
        for i, c in enumerate(coeffs, start=1):
            rhs += c * seq_by_m[m - i]
        if seq_by_m[m] != rhs:
            return False
    return True


def fit_min_recurrence(
    seq_by_m: Dict[int, int],
    *,
    m_min: int,
    m_max: int,
    d_min: int,
    d_max: int,
    m0_slack: int = 0,
) -> Tuple[int, int, List[int]]:
    """Find smallest order d with an exact integer recurrence verified on [m0..m_max].

    Search strategy: for each d, try m0 = (m_min + d) + s with s in [0..m0_slack].
    The canonical pattern in this paper is m0 = d + 2 (i.e. s=0 when m_min=2).
    """
    for d in range(max(1, int(d_min)), d_max + 1):
        base_m0 = m_min + d
        for s in range(0, m0_slack + 1):
            m0 = base_m0 + s
            # Need at least d equations (m0..m0+d-1) and values down to m0-d.
            if (m0 + d - 1) > m_max:
                continue
            if (m0 - d) < m_min:
                continue
            coeffs = solve_integer_recurrence(seq_by_m, d=d, m0=m0, m_max=m_max)
            if coeffs is None:
                continue
            if verify_recurrence(seq_by_m, coeffs, m0=m0, m_max=m_max):
                return d, m0, coeffs
    raise RuntimeError(f"failed to fit recurrence with d<= {d_max} on m∈[{m_min},{m_max}]")


def hankel_witness(seq_by_m: Dict[int, int], *, d: int, offset_max: int, m_max: int) -> Tuple[int, int]:
    """Return (offset, det) for a nonzero dxd Hankel minor of a_n:=S(n+2) on offsets up to offset_max."""
    # Need a_{off..off+2d-2} -> m up to (off+2d-2)+2 = off+2d.
    off_cap = min(int(offset_max), int(m_max - 2 * d))
    if off_cap < 0:
        raise RuntimeError(f"Need m_max >= {2*d} to form a {d}x{d} Hankel block (got m_max={m_max}).")
    n_need = off_cap + (2 * d - 2)
    a = [seq_by_m[n + 2] for n in range(n_need + 1)]
    for off in range(0, off_cap + 1):
        H = hankel_minor(a, d=d, offset=off)
        detH = det_int_matrix(H)
        if detH != 0:
            return off, int(detH)
    raise RuntimeError(f"failed to find nonzero Hankel witness for d={d} within offset<= {off_cap}")


@dataclass(frozen=True)
class Row:
    q: int
    m_min: int
    m_max: int
    order_d: int
    recurrence_m0: int
    coeffs: List[int]
    hankel_offset: int
    hankel_det: int
    r_q: float
    Lambda_q: float
    gapratio: float
    beta_q: float
    h_q: float
    h_q_R: float
    Delta_q: int


def main() -> None:
    ap = argparse.ArgumentParser(description="Exact q=18..25 Fold collision moment signatures (recurrence + spectrum).")
    ap.add_argument("--m-min", type=int, default=2)
    ap.add_argument("--m-max", type=int, default=35)
    ap.add_argument("--q-min", type=int, default=18)
    ap.add_argument("--q-max", type=int, default=25)
    ap.add_argument("--d-min", type=int, default=1, help="Minimum recurrence order to try (speed knob).")
    ap.add_argument("--dps", type=int, default=140, help="Decimal digits for sympy nroots.")
    ap.add_argument("--m0-slack", type=int, default=0, help="Try m0=(m_min+d)+s for s<=m0_slack.")
    ap.add_argument("--hankel-offset-max", type=int, default=8)
    ap.add_argument("--skip-hankel", action="store_true", help="Skip Hankel witness (faster; no minimality certificate).")
    ap.add_argument("--skip-roots", action="store_true", help="Skip nroots spectral extraction (debug/speed knob).")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_moment_signature_q18_25.json"),
    )
    args = ap.parse_args()

    m_min = int(args.m_min)
    m_max = int(args.m_max)
    q_min = int(args.q_min)
    q_max = int(args.q_max)
    if m_min < 2 or m_max < m_min:
        raise SystemExit("Require m_max >= m_min >= 2")
    if q_min < 2 or q_max < q_min:
        raise SystemExit("Require q_max >= q_min >= 2")

    qs = list(range(q_min, q_max + 1))

    # Max solvable order with a square system anchored at m0>=m_min+d:
    # need m0+d-1 <= m_max with m0=m_min+d -> 2d+m_min-1 <= m_max -> d <= floor((m_max-m_min+1)/2).
    d_max = int((m_max - m_min + 1) // 2)
    if d_max <= 0:
        raise SystemExit("m window too short to fit any recurrence.")

    prog = Progress("moment-signature-q18-25", every_seconds=20.0)

    # Compute S_q(m) for all q in qs over the audit window.
    S: Dict[int, Dict[int, int]] = {q: {} for q in qs}
    for m in range(m_min, m_max + 1):
        c = counts_mod_fib(m, prog=prog)
        moms = moments_for_qs_from_counts(c, qs)
        for q in qs:
            S[q][m] = moms[q]
        print(f"[moment-signature] m={m} mod=F_{{m+2}}={len(c)} computed q∈[{q_min},{q_max}]", flush=True)

    rows: List[Row] = []
    for q in qs:
        seq = S[q]
        d, m0, coeffs = fit_min_recurrence(
            seq,
            m_min=m_min,
            m_max=m_max,
            d_min=int(args.d_min),
            d_max=d_max,
            m0_slack=int(args.m0_slack),
        )
        print(f"[moment-signature] q={q:2d} recurrence: d={d} m0={m0} (computing spectrum...)", flush=True)
        if bool(args.skip_hankel):
            off, detH = -1, 0
        else:
            off, detH = hankel_witness(
                seq,
                d=d,
                offset_max=int(args.hankel_offset_max),
                m_max=m_max,
            )

        rq = float("nan")
        Lambdaq = float("nan")
        if not bool(args.skip_roots):
            poly = _poly_from_coeffs(coeffs)
            roots = _roots(poly, dps=int(args.dps))
            rq, Lambdaq, _mu_star = _perron_and_subdominant(roots)

        gapratio = float("nan")
        betaq = float("nan")
        if Lambdaq == Lambdaq and Lambdaq > 0 and rq == rq and rq > 0:
            gapratio = float(Lambdaq / rq)
            betaq = float(math.log(Lambdaq) / math.log(rq))

        hq = float("nan")
        hqR = float("nan")
        if rq == rq and rq > 0:
            hq = float(q) * math.log(2.0) - math.log(rq)
            hqR = hq / float(q - 1)
        Delta = (2 * (q // 2) + 1) - d

        rows.append(
            Row(
                q=int(q),
                m_min=m_min,
                m_max=m_max,
                order_d=int(d),
                recurrence_m0=int(m0),
                coeffs=[int(x) for x in coeffs],
                hankel_offset=int(off),
                hankel_det=int(detH),
                r_q=float(rq),
                Lambda_q=float(Lambdaq),
                gapratio=float(gapratio),
                beta_q=float(betaq),
                h_q=float(hq),
                h_q_R=float(hqR),
                Delta_q=int(Delta),
            )
        )

        print(
            f"[moment-signature] q={q:2d} d={d:2d} m0={m0:2d} "
            f"r_q={rq:.12f} Lambda_q={Lambdaq:.12f} beta_q={betaq:.6f} Delta_q={Delta}",
            flush=True,
        )

    out = Path(str(args.json_out))
    out.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "m_min": m_min,
        "m_max": m_max,
        "q_min": q_min,
        "q_max": q_max,
        "d_max_searched": d_max,
        "rows": [asdict(r) for r in rows],
    }
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[moment-signature] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

