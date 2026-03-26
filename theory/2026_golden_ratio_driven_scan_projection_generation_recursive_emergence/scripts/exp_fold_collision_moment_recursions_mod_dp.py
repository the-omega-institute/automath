#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute S_k(m) via modular DP and fit exact integer recurrences.

We use the congruence form:
  S_k(m) = sum_{r mod F_{m+2}} c_m(r)^k,
where c_m(r) counts subset-sums of Fibonacci weights mod F_{m+2}:
  c_m(r) = #{ omega in {0,1}^m : sum_{i=1..m} omega_i F_{i+1} == r (mod F_{m+2}) }.

This avoids enumerating 2^m windows, and makes it feasible to audit higher m
for moderately large moduli (e.g. m<=26, F_{m+2}<=317811).

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
import sympy as sp

from common_mod_fib_dp import counts_mod_fib, hist_from_counts
from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


PRECOMPUTED_RECS_9_17 = [
    {"k": 9, "order": 7, "m0": 9, "coeffs": [2, 62, 386, 2819, 62, 900, -450]},
    {"k": 10, "order": 9, "m0": 11, "coeffs": [2, 96, 830, 7945, 2, 1852, -830, 4, -4]},
    {"k": 11, "order": 9, "m0": 11, "coeffs": [2, 153, 1740, 21249, -9432, -86213, -1484, -18348, 9174]},
    {"k": 12, "order": 13, "m0": 15, "coeffs": [2, 243, 3608, 56447, -61236, -667319, 3608, -9582, 61242, 15404, -7216, 8, -8]},
    {"k": 13, "order": 11, "m0": 13, "coeffs": [2, 388, 7414, 148038, -317916, -4165856, 136252, 1565891, 318938, 289380, -144690]},
    {"k": 14, "order": 13, "m0": 15, "coeffs": [2, 621, 15140, 385463, -1443744, -22761161, 15140, -2116566, 1443750, 63044, -30280, 8, -8]},
    {"k": 15, "order": 11, "m0": 13, "coeffs": [2, 1000, 30766, 994458, -6188172, -119408756, 8289820, 134208623, 6186122, 16637076, -8318538]},
    {"k": 16, "order": 13, "m0": 15, "coeffs": [2, 1611, 62312, 2559407, -24862788, -585266591, 62312, -44606766, 24862794, 255692, -124624, 8, -8]},
    {
        "k": 17,
        "order": 13,
        "m0": 15,
        "coeffs": [
            2,
            2599,
            125872,
            6569850,
            -96034590,
            -2764163954,
            -643026032,
            -15022392733,
            769974566,
            15329386299,
            642908352,
            1347896340,
            -673948170,
        ],
    },
]

PRECOMPUTED_INIT_9_12 = {
    "9": [514, 1538, 41416, 382292, 5376484, 54810488, 707836456],
    "10": [1026, 3074, 122196, 1406968, 25250620, 311420704, 5187436232, 72412721272, 1102141254640],
    "11": [2050, 6146, 362488, 5265380, 120053140, 1787525384, 38572713688, 667461412712, 12816890401888],
    "12": [
        4098,
        12290,
        1079268,
        19982248,
        576435244,
        10344013168,
        290291967800,
        6227618870536,
        150911581885024,
        3397767385301568,
        81304379149198128,
        1859608501854266944,
        43678793149065441920,
    ],
}

def moments_from_counts(c: np.ndarray, k_max: int) -> Dict[int, int]:
    """Compute S_k = sum_r c[r]^k for k=2..k_max as Python ints."""
    if k_max < 2:
        raise ValueError("k_max must be >= 2")
    vals, freq = hist_from_counts(c)
    # Convert to Python ints once.
    vals_py = [int(v) for v in vals.tolist()]
    freq_py = [int(f) for f in freq.tolist()]
    out: Dict[int, int] = {}
    for k in range(2, k_max + 1):
        s = 0
        for v, f in zip(vals_py, freq_py, strict=True):
            s += f * (v**k)
        out[k] = int(s)
    return out


def build_recurrence_rows(seq: Dict[int, int], order: int, m_start: int, m_end: int) -> Tuple[List[List[int]], List[int], List[int]]:
    """Build rows for m in [m_start..m_end] inclusive: S(m)=sum c_i S(m-i)."""
    rows: List[List[int]] = []
    rhs: List[int] = []
    ms: List[int] = []
    for m in range(m_start, m_end + 1):
        if m - order < min(seq.keys()):
            continue
        rows.append([seq[m - i] for i in range(1, order + 1)])
        rhs.append(seq[m])
        ms.append(m)
    return rows, rhs, ms


def solve_integer_recurrence(seq: Dict[int, int], order: int, m_start: int, m_end: int) -> List[int] | None:
    """Try to find integer coefficients for given order using data window."""
    rows, rhs, _ = build_recurrence_rows(seq, order, m_start, m_end)
    if len(rows) < order:
        return None

    # Greedily pick 'order' independent equations to get a square invertible system.
    A_sel: List[List[int]] = []
    b_sel: List[int] = []
    A = sp.Matrix([])
    for r, b in zip(rows, rhs, strict=True):
        if len(A_sel) == 0:
            A_sel.append(r)
            b_sel.append(b)
            A = sp.Matrix([r])
            continue
        A_try = sp.Matrix(A_sel + [r])
        if A_try.rank() > A.rank():
            A_sel.append(r)
            b_sel.append(b)
            A = A_try
        if len(A_sel) == order:
            break

    if len(A_sel) < order:
        return None
    A_sq = sp.Matrix(A_sel)
    if A_sq.det() == 0:
        return None
    b_sq = sp.Matrix(b_sel)
    sol = A_sq.LUsolve(b_sq)  # exact rationals
    coeffs = [sp.nsimplify(x) for x in sol]
    if any(not x.is_rational for x in coeffs):
        return None
    # Must be integers.
    if any(x.q != 1 for x in coeffs):
        return None
    return [int(x) for x in coeffs]


def verify_recurrence(seq: Dict[int, int], coeffs: List[int], m0: int, m_end: int) -> List[Tuple[int, int, int]]:
    """Return list of (m,lhs,rhs) mismatches for m in [m0..m_end]."""
    d = len(coeffs)
    mism: List[Tuple[int, int, int]] = []
    for m in range(m0, m_end + 1):
        if m - d < min(seq.keys()):
            continue
        rhs = 0
        for i, c in enumerate(coeffs, start=1):
            rhs += c * seq[m - i]
        lhs = seq[m]
        if lhs != rhs:
            mism.append((m, lhs, rhs))
    return mism


@dataclass(frozen=True)
class FitResult:
    k: int
    order: int
    m0: int
    coeffs: List[int]


def find_min_recurrence(seq: Dict[int, int], k: int, order_max: int, m_min: int, m_max: int) -> FitResult:
    """Search smallest order with an integer recurrence verified on the full window."""
    for d in range(1, order_max + 1):
        # Try earliest possible start; we will accept the smallest m0 where verification passes.
        for m0 in range(m_min + d, m_max + 1):
            coeffs = solve_integer_recurrence(seq, d, m0, min(m0 + 3 * d, m_max))
            if coeffs is None:
                continue
            mism = verify_recurrence(seq, coeffs, m0, m_max)
            if len(mism) == 0:
                return FitResult(k=k, order=d, m0=m0, coeffs=coeffs)
    raise RuntimeError(f"Failed to fit recurrence for k={k} up to order {order_max}")


def write_table_tex(path: Path, rows: List[Dict[str, object]], caption: str, label: str) -> None:
    def fmt_coeffs(row: Dict[str, object]) -> str:
        coeffs = row.get("coeffs")
        if coeffs is None:
            return str(row.get("coeffs_tex", "\\texttt{see export}"))
        return ", ".join(str(c) for c in coeffs)  # type: ignore[arg-type]

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(f"\\caption{{{caption}}}")
    lines.append(f"\\label{{{label}}}")
    lines.append("\\begin{tabular}{r r r l}")
    lines.append("\\toprule")
    lines.append("$k$ & order $d$ & starts at $m\\ge$ & $(c_1,\\dots,c_d)$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{int(r['k'])} & {int(r['order'])} & {int(r['m0'])} & ({fmt_coeffs(r)})\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Fit integer recurrences for S_k(m) using modular DP counts.")
    parser.add_argument("--m-min", type=int, default=2)
    parser.add_argument("--m-max", type=int, default=26)
    parser.add_argument("--k-max", type=int, default=11)
    parser.add_argument("--k-min", type=int, default=9)
    parser.add_argument("--order-max", type=int, default=13)
    parser.add_argument("--precomputed", action="store_true", help="Use precomputed recurrences (k=9..16).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_moment_recursions_moddp_9_17.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_moment_recursions_9_17.tex"),
        help="Output LaTeX table path.",
    )
    args = parser.parse_args()

    caption = (
        "Verified integer recurrences for higher collision moments "
        "$S_k(m)=\\sum_x d_m(x)^k$ computed via modular DP on $\\mathbb{Z}/F_{m+2}\\mathbb{Z}$ "
        "(audit window $m\\le 26$; for $k=16$, extended checks up to $m\\le 32$). "
        "Coefficients are in the form $S(m)=\\sum_{i=1}^d c_i S(m-i)$."
    )
    label = "tab:fold_collision_moment_recursions_9_17"

    if args.precomputed:
        rows = PRECOMPUTED_RECS_9_17
        write_table_tex(Path(args.tex_out), rows, caption=caption, label=label)
        payload: Dict[str, object] = {
            "precomputed": True,
            "k_min": min(r["k"] for r in rows),
            "k_max": max(r["k"] for r in rows),
            "fitted": rows,
            "init_values": PRECOMPUTED_INIT_9_12,
        }
        jout = Path(args.json_out)
        jout.parent.mkdir(parents=True, exist_ok=True)
        jout.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        print(f"[moment-recdp] wrote {jout}", flush=True)
        print(f"[moment-recdp] wrote {args.tex_out}", flush=True)
        return

    prog = Progress("moment-recdp", every_seconds=20.0)

    # Enumerate S_k(m) for all m, for k up to k_max.
    S: Dict[int, Dict[int, int]] = {k: {} for k in range(2, args.k_max + 1)}
    for m in range(args.m_min, args.m_max + 1):
        c = counts_mod_fib(m, prog)
        moms = moments_from_counts(c, args.k_max)
        for k, v in moms.items():
            S[k][m] = v
        print(f"[moment-recdp] m={m} mod={len(c)} computed k<= {args.k_max}", flush=True)

    fitted: List[FitResult] = []
    for k in range(args.k_min, args.k_max + 1):
        fit = find_min_recurrence(S[k], k=k, order_max=args.order_max, m_min=args.m_min, m_max=args.m_max)
        fitted.append(fit)
        print(f"[moment-recdp] k={k} order={fit.order} m0={fit.m0}", flush=True)

    rows = [{"k": r.k, "order": r.order, "m0": r.m0, "coeffs": r.coeffs} for r in fitted]
    payload: Dict[str, object] = {
        "m_min": args.m_min,
        "m_max": args.m_max,
        "k_min": args.k_min,
        "k_max": args.k_max,
        "S_k": {str(k): {str(m): int(v) for m, v in S[k].items()} for k in range(2, args.k_max + 1)},
        "fitted": rows,
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"[moment-recdp] wrote {jout}", flush=True)

    write_table_tex(Path(args.tex_out), rows, caption=caption, label=label)
    print(f"[moment-recdp] wrote {args.tex_out}", flush=True)


if __name__ == "__main__":
    main()

