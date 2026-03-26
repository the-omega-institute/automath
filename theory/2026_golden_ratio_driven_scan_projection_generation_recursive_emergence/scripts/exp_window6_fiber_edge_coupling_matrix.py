#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: weighted fiber edge-coupling matrix on X_6 induced by Q_6 edges.

All output is English-only by repository convention.

We work at the window-6 dyadic fold:
  Fold^{bin}_6 : {0,...,63} -> X_6,
and the label map on Omega_6={0,1}^6 (identified with integers 0..63):
  F6(omega) := Fold^{bin}_6(int_6(omega)) ∈ X_6.

Define the weighted coupling matrix M ∈ Z^{21×21} by:
  - M_{ww} = 0,
  - for w≠w', M_{ww'} = #{ {u,v} ∈ E(Q_6) : F6(u)=w, F6(v)=w' }.

Then:
  - M is symmetric,
  - row sums satisfy  Σ_{w'} M_{ww'} = 6 * d^{bin}_6(w),
  - det(M) is a nonzero integer, giving invertibility over R,
  - we output an explicit prime factorization of det(M).

Outputs:
  - artifacts/export/window6_fiber_edge_coupling_matrix.json
  - sections/generated/eq_window6_fiber_edge_coupling_det.tex
"""

from __future__ import annotations

import argparse
import json
from math import gcd
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir, generated_dir
from common_phi_fold import word_to_str, zeckendorf_digits


def _foldbin6_label(n: int) -> str:
    # For m=6, K(6)=9 (F_{10}=55 ≤ 63 < F_{11}=89), so digits up to k=9 are exact.
    digits = zeckendorf_digits(n, 9)  # digits for weights F_{k+1}, k=1..9
    return word_to_str(digits[:6])


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


def _fmt_factorization(sign: int, fac: Dict[int, int]) -> str:
    parts: List[str] = []
    if sign < 0:
        parts.append("-")
    for p in sorted(fac.keys()):
        e = fac[p]
        if e == 1:
            parts.append(str(p))
        else:
            parts.append(f"{p}^{{{e}}}")
    # join with \cdot, keeping leading "-" separate.
    if not parts:
        return "0"
    if parts[0] == "-":
        return "-" + "\\cdot ".join(parts[1:])
    return "\\cdot ".join(parts)


def main() -> None:
    ap = argparse.ArgumentParser(description="Compute the window-6 weighted fiber edge-coupling matrix M and det(M).")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "window6_fiber_edge_coupling_matrix.json"),
        help="Path to JSON audit output.",
    )
    ap.add_argument(
        "--tex-eq-out",
        type=str,
        default=str(generated_dir() / "eq_window6_fiber_edge_coupling_det.tex"),
        help="Path to generated TeX equation snippet (\\input{}).",
    )
    args = ap.parse_args()

    # Words in X_6 as the image of Fold^{bin}_6.
    labels = [_foldbin6_label(n) for n in range(64)]
    words = sorted(set(labels))
    if len(words) != 21:
        raise RuntimeError(f"Unexpected |X_6| from Fold^{{bin}}_6: {len(words)}")

    idx = {w: i for i, w in enumerate(words)}
    d_word: Dict[str, int] = {w: 0 for w in words}
    for w in labels:
        d_word[w] += 1

    # Build M from undirected Q_6 edges counted once (n<nn).
    m = 6
    nwords = len(words)
    M = [[0 for _ in range(nwords)] for _ in range(nwords)]
    for n in range(64):
        for j in range(m):
            nn = n ^ (1 << j)
            if n < nn:
                a = idx[labels[n]]
                b = idx[labels[nn]]
                if a == b:
                    raise RuntimeError("Unexpected internal edge inside a Fold^{bin}_6 fiber (should be edge-separated).")
                M[a][b] += 1
                M[b][a] += 1

    # Symmetry and row-sum checks.
    for i in range(nwords):
        if M[i][i] != 0:
            raise RuntimeError("Diagonal of M must be zero.")
        for j in range(nwords):
            if M[i][j] != M[j][i]:
                raise RuntimeError("M must be symmetric.")

    row_sums: Dict[str, int] = {}
    for w in words:
        i = idx[w]
        s = sum(M[i])
        row_sums[w] = int(s)
        if s != m * d_word[w]:
            raise RuntimeError(f"Row sum mismatch for {w}: sum={s}, expected={m*d_word[w]}")

    detM = det_int_matrix(M)
    if detM == 0:
        raise RuntimeError("Unexpected det(M)=0; expected invertibility over R.")

    sign = -1 if detM < 0 else 1
    fac = {int(p): int(e) for p, e in sp.factorint(abs(int(detM))).items()}

    # Extra: gcd of row sums as a coarse sanity fingerprint.
    g = 0
    for s in row_sums.values():
        g = gcd(g, int(s))

    payload: Dict[str, object] = {
        "m": 6,
        "words": words,
        "fiber_size_d_bin": {w: int(d_word[w]) for w in words},
        "M_edge_counts": M,
        "row_sums": {w: int(row_sums[w]) for w in words},
        "row_sum_gcd": int(g),
        "det_M": int(detM),
        "det_M_factorization": {"sign": int(sign), "prime_powers": {str(p): int(e) for p, e in sorted(fac.items())}},
    }

    json_out = Path(str(args.json_out))
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # TeX equation snippet.
    tex_out = Path(str(args.tex_eq_out))
    tex_out.parent.mkdir(parents=True, exist_ok=True)
    det_tex = _fmt_factorization(sign, fac)

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_window6_fiber_edge_coupling_matrix.py")
    lines.append("\\begin{equation}\\label{eq:window6_fiber_edge_coupling_det}")
    lines.append("\\begin{aligned}")
    lines.append("\\sum_{y\\in X_6} M_{xy}&=6\\,d^{\\mathrm{bin}}_6(x),\\\\")
    lines.append(f"\\det(M)&={det_tex}.")
    lines.append("\\end{aligned}")
    lines.append("\\end{equation}")
    lines.append("")
    tex_out.write_text("\n".join(lines), encoding="utf-8")

    print(f"File: {json_out.relative_to(export_dir().parent.parent)}")
    print(f"File: {tex_out.relative_to(generated_dir().parent.parent)}")


if __name__ == "__main__":
    main()

