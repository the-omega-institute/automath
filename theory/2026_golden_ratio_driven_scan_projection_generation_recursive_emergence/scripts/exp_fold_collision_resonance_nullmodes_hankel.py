#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Resonance gap Delta(q) and explicit Hankel-null "NullModes(q)" certificates.

Context (paper PDF):
  - For Fold_m fibers, define S_q(m)=sum_{x in X_m} d_m(x)^q.
  - For q>=9, audited integer recurrences show a rank deficit:
      d_q < 2*floor(q/2)+1,
    where d_q is the minimal integer-recurrence order / minimal realization dimension.
  - Define the resonance gap:
      Delta(q) := (2*floor(q/2)+1) - d_q.

This script produces two fully auditable artifacts:
  1) A table of Delta(q) for q=9..17 from the repository-audited recurrences.
  2) For each q, a Z-basis of ker(H^T) for a Hankel block H=(a_{i+j}) built from
     a_n := S_q(n+2) on a fixed audit window.
     The basis vectors are reported as integer coefficient vectors
       alpha^{(j)} in Z^{2h+1}, h=floor(q/2),
     satisfying alpha^T H = 0 on the window.

Notes:
  - The NullModes(q) produced here are "Hankel-null certificates": they are
    explicit linear relations among contiguous samples a_n in a window.
  - All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from math import gcd
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from exp_fold_collision_moment_recursions_mod_dp import PRECOMPUTED_RECS_9_17, counts_mod_fib, moments_from_counts


def _lcm(a: int, b: int) -> int:
    if a == 0 and b == 0:
        return 0
    return abs(a // gcd(a, b) * b)


def _lcm_list(xs: List[int]) -> int:
    out = 1
    for x in xs:
        out = _lcm(out, abs(int(x)))
    return out


def _gcd_list(xs: List[int]) -> int:
    g = 0
    for x in xs:
        g = gcd(g, abs(int(x)))
    return g


def _normalize_int_vec(v: List[int]) -> List[int]:
    if all(x == 0 for x in v):
        return v
    g = _gcd_list(v)
    if g > 1:
        v = [x // g for x in v]
    # fix sign: first nonzero positive
    for x in v:
        if x != 0:
            if x < 0:
                v = [-t for t in v]
            break
    return v


def _rational_vec_to_int(v: sp.Matrix) -> List[int]:
    # v is a column vector with Rational entries.
    dens: List[int] = []
    for x in list(v):
        x = sp.nsimplify(x)
        if not x.is_rational:
            raise ValueError(f"Expected rational nullspace vector entry, got {x}")
        dens.append(int(x.q))
    scale = _lcm_list(dens)
    ints = []
    for x in list(v):
        x = sp.nsimplify(x)
        ints.append(int(x * scale))
    return _normalize_int_vec(ints)


def _rank_int_mat(A: List[List[int]]) -> int:
    return int(sp.Matrix(A).rank())


def _independent_integer_basis(vs: List[List[int]]) -> List[List[int]]:
    """Greedy keep vectors that increase rank over Q."""
    keep: List[List[int]] = []
    rk = 0
    for v in vs:
        if not keep:
            keep = [v]
            rk = int(sp.Matrix(keep).rank())
            continue
        cand = keep + [v]
        rk2 = int(sp.Matrix(cand).rank())
        if rk2 > rk:
            keep = cand
            rk = rk2
    return keep


def _build_hankel(a: List[int], rows: int, cols: int) -> List[List[int]]:
    # H[i][j] = a[i+j]
    return [[int(a[i + j]) for j in range(cols)] for i in range(rows)]


def _verify_hankel_null(a: List[int], alpha: List[int], rows: int) -> bool:
    # Verify sum_{i=0..rows-1} alpha[i] * a[i+t] == 0 for all valid shifts t.
    n_max = len(a) - 1
    t_max = n_max - (rows - 1)
    for t in range(0, t_max + 1):
        s = 0
        for i in range(rows):
            s += int(alpha[i]) * int(a[i + t])
        if s != 0:
            return False
    return True


@dataclass(frozen=True)
class NullModeRow:
    q: int
    h: int
    nominal_dim: int
    d_q: int
    delta_q: int
    m_min: int
    m_max: int
    hankel_rows: int
    hankel_cols: int
    hankel_rank: int
    basis_int: List[List[int]]  # vectors in Z^{nominal_dim}, indexed by ell=-h..h (stored in order)
    basis_support_sizes: List[int]
    verified_full_window: bool


def _precomputed_orders_9_17() -> Dict[int, int]:
    by_q: Dict[int, int] = {}
    for r in PRECOMPUTED_RECS_9_17:
        by_q[int(r["k"])] = int(r["order"])
    return by_q


def _write_delta_table_tex(path: Path, rows: List[NullModeRow]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Resonance gap function $\\Delta(q)=(2\\lfloor q/2\\rfloor+1)-d_q$ "
        "for higher collision moments $S_q(m)$ (values read from the audited minimal "
        "integer recurrences in Table~\\ref{tab:fold_collision_moment_recursions_9_17}).}"
    )
    lines.append("\\label{tab:fold_collision_resonance_gap_delta_q_9_17}")
    lines.append("\\begin{tabular}{r r r r}")
    lines.append("\\toprule")
    lines.append("$q$ & nominal $2\\lfloor q/2\\rfloor+1$ & $d_q$ & $\\Delta(q)$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(f"{r.q} & {r.nominal_dim} & {r.d_q} & {r.delta_q}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _fmt_vec(v: List[int]) -> str:
    # Compact, audit-friendly, no spaces.
    return "(" + ",".join(str(int(x)) for x in v) + ")"


def _write_nullmodes_table_tex(path: Path, rows: List[NullModeRow]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.15}")
    lines.append(
        "\\caption{Hankel-null certificates $\\mathrm{NullModes}(q)$ for $a_n:=S_q(n+2)$. "
        "For each $q$, we form a Hankel block $H=(a_{i+j})$ with $2\\lfloor q/2\\rfloor+1$ rows "
        "and compute an integer basis of $\\ker(H^{\\mathsf T})$. "
        "Vectors are listed in the order $(\\alpha_{-h},\\ldots,\\alpha_h)$, $h=\\lfloor q/2\\rfloor$.}"
    )
    lines.append("\\label{tab:fold_collision_resonance_nullmodes_q9_17}")
    lines.append("\\begin{tabular}{r r r l}")
    lines.append("\\toprule")
    lines.append("$q$ & $\\Delta(q)$ & Hankel size & $\\mathrm{NullModes}(q)$ (integer basis)\\\\")
    lines.append("\\midrule")
    for r in rows:
        basis = ",\\ ".join(f"$\\alpha^{{({j+1})}}={_fmt_vec(v)}$" for j, v in enumerate(r.basis_int))
        size = f"{r.hankel_rows}\\times {r.hankel_cols}"
        lines.append(f"{r.q} & {r.delta_q} & ${size}$ & {basis}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute resonance gaps and Hankel-null certificates for S_q(m).")
    parser.add_argument("--q-list", type=str, default="9,10,11,12,13,14,15,16,17")
    parser.add_argument("--m-min", type=int, default=2)
    parser.add_argument(
        "--m-max",
        type=int,
        default=32,
        help="Audit window max m (auto-extended if needed to make Hankel columns >= d_q).",
    )
    parser.add_argument(
        "--m-max-cap",
        type=int,
        default=36,
        help="Hard cap for auto-extension of m-max.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_resonance_nullmodes_hankel_q9_17.json"),
    )
    parser.add_argument(
        "--tex-delta-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_resonance_gap_delta_q_9_17.tex"),
    )
    parser.add_argument(
        "--tex-nullmodes-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_resonance_nullmodes_q9_17.tex"),
    )
    args = parser.parse_args()

    qs = [int(s.strip()) for s in str(args.q_list).split(",") if s.strip()]
    if not qs:
        raise SystemExit("Empty --q-list")
    if any(q < 2 for q in qs):
        raise SystemExit("All q must be >= 2")
    if any(q < 9 or q > 17 for q in qs):
        raise SystemExit("This script currently supports q in [9..17] (uses audited precomputed recurrences).")

    pre_order = _precomputed_orders_9_17()
    if any(q not in pre_order for q in qs):
        missing = [q for q in qs if q not in pre_order]
        raise SystemExit(f"Missing precomputed recurrence order for q={missing}")

    m_min = int(args.m_min)
    if m_min < 2:
        raise SystemExit("Require --m-min >= 2")

    m_max_user = int(args.m_max)
    m_max_cap = int(args.m_max_cap)
    if m_max_user < m_min:
        raise SystemExit("Require m_max >= m_min")
    if m_max_cap < m_max_user:
        raise SystemExit("Require m_max_cap >= m_max")

    # Auto-extend m_max so that for each q we can form a Hankel block with
    # columns >= d_q: need (m_max - (2h+1)) >= d_q.
    m_max_req = m_max_user
    for q in qs:
        h = q // 2
        nominal = 2 * h + 1
        dq = int(pre_order[q])
        m_max_req = max(m_max_req, nominal + dq)
    if m_max_req > m_max_cap:
        raise SystemExit(f"Need m_max >= {m_max_req} to certify all requested q; cap is {m_max_cap}.")
    m_max = int(m_max_req)
    if m_max != m_max_user:
        print(f"[nullmodes] auto-extended m_max: user={m_max_user} -> {m_max} (to make Hankel cols >= d_q)", flush=True)

    q_max = max(qs)
    prog = Progress("nullmodes", every_seconds=20.0)

    # Compute S_q(m) for all requested q on [m_min..m_max] via modular DP.
    S: Dict[int, Dict[int, int]] = {q: {} for q in qs}
    for m in range(m_min, m_max + 1):
        c = counts_mod_fib(m, prog=prog)
        moms = moments_from_counts(c, k_max=q_max)
        for q in qs:
            S[q][m] = int(moms[q])
        print(f"[nullmodes] m={m} mod={len(c)} computed q<= {q_max}", flush=True)

    out_rows: List[NullModeRow] = []
    for q in qs:
        dq = int(pre_order[q])
        h = q // 2
        nominal = 2 * h + 1
        delta = int(nominal - dq)
        if delta < 0:
            raise SystemExit(f"Invalid resonance gap for q={q}: nominal={nominal} < d_q={dq}")

        # a_n := S_q(n+2), so n in [0..m_max-2]
        a = [int(S[q][n + 2]) for n in range(0, (m_max - 2) + 1)]

        hankel_rows = nominal
        hankel_cols = m_max - nominal  # maximal cols so that i+j <= m_max-2
        if hankel_cols < dq:
            raise SystemExit(f"Internal error: hankel_cols={hankel_cols} < d_q={dq} for q={q}")

        H = _build_hankel(a, rows=hankel_rows, cols=hankel_cols)
        rk = _rank_int_mat(H)
        if rk != dq:
            print(
                f"[nullmodes] WARNING q={q}: Hankel rank in window is {rk}, but audited d_q is {dq}. "
                f"(rows={hankel_rows} cols={hankel_cols} m_max={m_max})",
                flush=True,
            )

        # Compute integer basis of ker(H^T).
        Ht = sp.Matrix(H).T
        ns = Ht.nullspace()
        basis_int_all = [_rational_vec_to_int(v) for v in ns]
        basis_int_all = [_normalize_int_vec(v) for v in basis_int_all]
        basis_int = _independent_integer_basis(basis_int_all)

        # Keep at most Delta(q) vectors (greedy) if nullspace is larger in this window.
        # If Delta(q)=0, we report an empty basis.
        if delta == 0:
            basis_int = []
        elif len(basis_int) > delta:
            basis_int = basis_int[:delta]
        if len(basis_int) < min(delta, len(ns)):
            # rank deficiency might be smaller than expected in this window.
            print(
                f"[nullmodes] WARNING q={q}: got only {len(basis_int)} independent integer null vectors, expected {delta}",
                flush=True,
            )

        support_sizes = [sum(1 for x in v if x != 0) for v in basis_int]
        verified = all(_verify_hankel_null(a, alpha=v, rows=hankel_rows) for v in basis_int)

        out_rows.append(
            NullModeRow(
                q=int(q),
                h=int(h),
                nominal_dim=int(nominal),
                d_q=int(dq),
                delta_q=int(delta),
                m_min=int(m_min),
                m_max=int(m_max),
                hankel_rows=int(hankel_rows),
                hankel_cols=int(hankel_cols),
                hankel_rank=int(rk),
                basis_int=[list(map(int, v)) for v in basis_int],
                basis_support_sizes=[int(s) for s in support_sizes],
                verified_full_window=bool(verified),
            )
        )
        print(f"[nullmodes] q={q} Delta={delta} null_basis={len(basis_int)} verified={verified}", flush=True)

    # Write JSON.
    payload = {
        "m_min": m_min,
        "m_max_user": m_max_user,
        "m_max_used": m_max,
        "q_list": qs,
        "rows": [asdict(r) for r in out_rows],
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[nullmodes] wrote {jout}", flush=True)

    # Write LaTeX tables.
    _write_delta_table_tex(Path(args.tex_delta_out), out_rows)
    print(f"[nullmodes] wrote {args.tex_delta_out}", flush=True)
    _write_nullmodes_table_tex(Path(args.tex_nullmodes_out), out_rows)
    print(f"[nullmodes] wrote {args.tex_nullmodes_out}", flush=True)


if __name__ == "__main__":
    main()
