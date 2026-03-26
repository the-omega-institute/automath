#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Hankel-rank lower bounds for higher collision moments S_k(m).

We enumerate Fold_m fibers up to moderate m (default m<=18) and compute:
  S_k(m) = sum_x d_m(x)^k,  k=2..8.

From a linear-recursive (rational) series viewpoint, the Hankel rank gives the
minimal dimension of any linear representation a_n = u^T A^n v, hence lower-bounds
the state dimension of any weighted automaton realizing the sequence.

For a sequence satisfying a linear recurrence of order d, Hankel rank <= d.
To show Hankel rank >= d, it suffices to exhibit one nonzero dxd Hankel minor.

This script outputs such minors (determinants) for k=2..8 using the natural
reindex a_n := S_k(n+2) / 2 for k=2,3 and a_n := S_k(n+2) for k>=4 (scaling does
not affect rank).

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from itertools import product
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fold_m, word_to_str


def collision_counts(m: int, prog: Progress | None = None) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    total = 1 << m
    for i, bits in enumerate(product([0, 1], repeat=m), start=1):
        x = word_to_str(fold_m(bits))
        counts[x] = counts.get(x, 0) + 1
        if prog is not None:
            prog.tick(f"m={m} i={i}/{total} distinct={len(counts)}")
    return counts


def s_k_from_counts(counts: Dict[str, int], k: int) -> int:
    if k == 2:
        return sum(v * v for v in counts.values())
    if k == 3:
        return sum(v * v * v for v in counts.values())
    return sum(int(v**k) for v in counts.values())


def enumerate_S(m_min: int, m_max: int, k_max: int, prog: Progress) -> Dict[int, Dict[int, int]]:
    S: Dict[int, Dict[int, int]] = {k: {} for k in range(2, k_max + 1)}
    for m in range(m_min, m_max + 1):
        counts = collision_counts(m, prog)
        for k in range(2, k_max + 1):
            S[k][m] = s_k_from_counts(counts, k)
        print(f"[hankel-rank] m={m} |X_m|={len(counts)}", flush=True)
    return S


def extend_by_recurrence(
    seq_by_m: Dict[int, int],
    coeffs: List[int],
    m0: int,
    m_target: int,
) -> None:
    """Extend seq_by_m in-place up to m_target using S(m)=sum_{i=1..d} c_i S(m-i).

    Assumes recurrence is valid for all m >= m0 and that required past values exist.
    """
    d = len(coeffs)
    m_cur = max(seq_by_m.keys())
    for m in range(m_cur + 1, m_target + 1):
        if m < m0:
            raise ValueError(f"Need explicit values up to m0-1; got asked to extend at m={m}<m0={m0}")
        s = 0
        for i, c in enumerate(coeffs, start=1):
            s += c * seq_by_m[m - i]
        seq_by_m[m] = s


def det_int_matrix(A: List[List[int]]) -> int:
    """Exact determinant via fraction-free Gaussian elimination (Bareiss)."""
    n = len(A)
    if n == 0:
        return 1
    M = [row[:] for row in A]
    det_sign = 1
    prev_pivot = 1
    for k in range(n - 1):
        # find nonzero pivot
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


def hankel_minor(seq: List[int], d: int, offset: int = 0) -> List[List[int]]:
    """Return dxd Hankel matrix H_{ij} = seq[offset + i + j]."""
    return [[seq[offset + i + j] for j in range(d)] for i in range(d)]


@dataclass(frozen=True)
class Row:
    k: int
    order_d: int
    det_minor: int
    offset: int


def write_table_tex(path: Path, rows: List[Row]) -> None:
    def fmt_det(x: int) -> str:
        # keep readable; exact integers can be large.
        s = str(x)
        if len(s) <= 18:
            return s
        # scientific-ish: show first/last chunks
        return s[:10] + "\\cdots" + s[-6:]

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Nonzero Hankel minors witnessing Hankel-rank lower bounds for $S_k(m)=\\sum_x d_m(x)^k$. "
        "For each $k$ we form a sequence $a_n$ from $S_k(n+2)$ (rescaling does not affect rank) and "
        "report $\\det(H)$ for a $d\\times d$ Hankel block $H=(a_{i+j+r})_{0\\le i,j<d}$. "
        "Nonzero determinant implies Hankel rank $\\ge d$, hence any linear representation requires dimension $\\ge d$.}"
    )
    lines.append("\\label{tab:fold_collision_moment_hankel_rank}")
    lines.append("\\begin{tabular}{r r r r}")
    lines.append("\\toprule")
    lines.append("$k$ & target $d$ & offset $r$ & $\\det(H)$ (nonzero)\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(f"{r.k} & {r.order_d} & {r.offset} & ${fmt_det(r.det_minor)}$\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute Hankel-rank witnesses for S_k(m) collision moments.")
    parser.add_argument("--m-min", type=int, default=2)
    parser.add_argument("--m-max", type=int, default=18)
    parser.add_argument("--k-max", type=int, default=8)
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_moment_hankel_rank.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_moment_hankel_rank.tex"),
        help="Output LaTeX table path.",
    )
    args = parser.parse_args()

    prog = Progress("hankel-rank", every_seconds=20.0)
    S = enumerate_S(args.m_min, args.m_max, args.k_max, prog)

    # Known exact recurrences (verified elsewhere) to extend beyond enumeration window if needed.
    # Format: k -> (m0, coeffs) with S(m)=sum_{i=1..d} c_i S(m-i), valid for m>=m0.
    recs: Dict[int, Tuple[int, List[int]]] = {
        2: (5, [2, 2, -2]),
        3: (5, [2, 4, -2]),
        4: (13, [2, 7, 0, 2, -2]),
        5: (13, [2, 11, 8, 20, -10]),
        6: (15, [2, 17, 28, 88, -26, 4, -4]),
        7: (15, [2, 26, 74, 311, -34, 84, -42]),
        8: (17, [2, 40, 174, 969, 2, 428, -174, 4, -4]),
    }

    # Target orders: d = 2*floor(k/2)+1 for k>=2 (empirically; k=2,3 known).
    rows: List[Row] = []
    payload_rows: List[Dict[str, object]] = []

    for k in range(2, args.k_max + 1):
        d = 2 * (k // 2) + 1
        # build a_n from S_k(n+2); rescale for k=2,3 to match paper's a_n convention if desired
        # (rank unaffected by scaling).
        # We may need to extend S_k(m) a bit beyond args.m_max to get a robust nonzero minor.
        max_offset = 10
        n_need = max_offset + (2 * d - 2)
        m_need = (n_need + 2)
        if m_need > max(S[k].keys()):
            if k not in recs:
                raise SystemExit(f"No recurrence available to extend k={k} beyond m={max(S[k].keys())}")
            m0, coeffs = recs[k]
            if max(S[k].keys()) < m0:
                raise SystemExit(f"Need enumeration up to at least m0={m0} for k={k}")
            extend_by_recurrence(S[k], coeffs=coeffs, m0=m0, m_target=m_need)

        a: List[int] = []
        for n in range(n_need + 1):
            m = n + 2
            v = S[k][m]
            if k in (2, 3):
                if v % 2 != 0:
                    raise SystemExit(f"Expected even S_{k}(m) for k=2,3 at m={m}, got {v}")
                v //= 2
            a.append(v)

        # try small offsets to find a nonzero minor (robust to unlucky singular windows)
        found = None
        for off in range(0, max_offset + 1):
            H = hankel_minor(a, d, offset=off)
            detH = det_int_matrix(H)
            if detH != 0:
                found = (off, detH)
                break
        if found is None:
            raise SystemExit(f"Failed to find nonzero {d}x{d} Hankel minor for k={k} in offsets 0..5")
        off, detH = found
        rows.append(Row(k=k, order_d=d, det_minor=detH, offset=off))
        payload_rows.append({"k": k, "d": d, "offset": off, "det": int(detH)})

    payload: Dict[str, object] = {
        "m_min": args.m_min,
        "m_max": args.m_max,
        "k_max": args.k_max,
        "rows": payload_rows,
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"[hankel-rank] wrote {jout}", flush=True)

    write_table_tex(Path(args.tex_out), rows)
    print(f"[hankel-rank] wrote {args.tex_out}", flush=True)


if __name__ == "__main__":
    main()

