#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: window-6 four-block Green kernel arithmetic and audit prime 571.

All output is English-only by repository convention.

We use the 4-state coarse Markov kernel T from the window-6 edge–flux skeleton
(see eq_window6_edge_flux_skeleton.tex). We compute:
  - the weighted spanning-tree number of the undirected block quotient graph,
  - the fundamental (Green) matrix Z = (I - T + 1*pi^T)^{-1},
  - det(I - T + 1*pi^T), showing the unavoidable prime 571,
  - Kemeny constant K = tr(Z) - 1 = p'(1)/p(1),
  - mean first passage times m_{alpha->beta} for alpha != beta.

Outputs:
  - artifacts/export/window6_green_kernel_audit_prime_571.json
  - sections/generated/eq_window6_green_kernel_audit_prime_571.tex
  - sections/generated/tab_window6_green_kernel_Z.tex
  - sections/generated/tab_window6_mean_first_passage_times.tex
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

from common_paths import export_dir, generated_dir


BLOCKS = ["2", "1", "L", "R"]  # order consistent with eq_window6_edge_flux_skeleton


def _coarse_kernel_T() -> Tuple[List[str], List[int], List[List[int]], List[List[Fraction]], List[Fraction]]:
    """Return (blocks, |U| vector, E undirected edge counts, T coarse kernel, pi stationary)."""
    U_size: Dict[str, int] = {"2": 27, "1": 22, "L": 9, "R": 6}
    # Undirected edge counts between unions U_alpha; symmetric, diagonal = internal edges.
    E = [
        [28, 63, 23, 20],
        [63, 21, 21, 6],
        [23, 21, 2, 6],
        [20, 6, 6, 2],
    ]

    # Directed edge counts: off-diagonal = E_ij, diagonal = 2*E_ii.
    A: List[List[int]] = [[0] * 4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            A[i][j] = (2 * E[i][j]) if i == j else E[i][j]

    # Coarse Markov kernel induced by one cube step under within-block uniform prior:
    #   T_ij = A_ij / (6 * |U_i|).
    T: List[List[Fraction]] = []
    for i, bi in enumerate(BLOCKS):
        denom = 6 * U_size[bi]
        T.append([Fraction(A[i][j], denom) for j in range(4)])

    # Stationary distribution is proportional to |U_alpha| (micro-volume).
    pi = [Fraction(U_size[b], 64) for b in BLOCKS]
    return BLOCKS[:], [U_size[b] for b in BLOCKS], E, T, pi


def _eye(n: int) -> List[List[Fraction]]:
    return [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]


def _det_fraction(M: List[List[Fraction]]) -> Fraction:
    """Determinant via fraction-preserving elimination (O(n^3), small n)."""
    A = [row[:] for row in M]
    n = len(A)
    det = Fraction(1, 1)
    for i in range(n):
        piv = i
        while piv < n and A[piv][i] == 0:
            piv += 1
        if piv == n:
            return Fraction(0, 1)
        if piv != i:
            A[i], A[piv] = A[piv], A[i]
            det *= -1
        pivval = A[i][i]
        det *= pivval
        # eliminate below
        for r in range(i + 1, n):
            if A[r][i] == 0:
                continue
            factor = A[r][i] / pivval
            for c in range(i, n):
                A[r][c] -= factor * A[i][c]
    return det


def _inv_fraction(M: List[List[Fraction]]) -> List[List[Fraction]]:
    """Matrix inverse by Gauss–Jordan (exact Fractions)."""
    n = len(M)
    aug = [row[:] + eye_row[:] for row, eye_row in zip([r[:] for r in M], _eye(n))]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if aug[r][col] != 0:
                piv = r
                break
        if piv is None:
            raise RuntimeError("singular matrix")
        aug[col], aug[piv] = aug[piv], aug[col]
        pivval = aug[col][col]
        aug[col] = [x / pivval for x in aug[col]]
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor == 0:
                continue
            aug[r] = [aug[r][c] - factor * aug[col][c] for c in range(2 * n)]
    return [row[n:] for row in aug]


def _laplacian_from_E_offdiag(E: List[List[int]]) -> List[List[int]]:
    """Weighted Laplacian for the undirected multigraph with edge multiplicities E_ij (i!=j)."""
    n = len(E)
    L = [[0] * n for _ in range(n)]
    for i in range(n):
        deg = 0
        for j in range(n):
            if i == j:
                continue
            deg += E[i][j]
        L[i][i] = deg
        for j in range(n):
            if i == j:
                continue
            L[i][j] = -E[i][j]
    return L


def _minor_int(M: List[List[int]], drop: int) -> List[List[Fraction]]:
    """Return the principal minor obtained by deleting row/col=drop as Fraction matrix."""
    n = len(M)
    out: List[List[Fraction]] = []
    for i in range(n):
        if i == drop:
            continue
        row: List[Fraction] = []
        for j in range(n):
            if j == drop:
                continue
            row.append(Fraction(M[i][j], 1))
        out.append(row)
    return out


def _factorint(n: int) -> Counter[int]:
    n = abs(int(n))
    f: Counter[int] = Counter()
    p = 2
    while p * p <= n:
        while n % p == 0:
            f[p] += 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        f[n] += 1
    return f


def _primes_in_denominators(fracs: Iterable[Fraction]) -> List[int]:
    primes: set[int] = set()
    for x in fracs:
        primes.update(_factorint(x.denominator).keys())
    return sorted(primes)


def _frac_tex(x: Fraction) -> str:
    if x.denominator == 1:
        return str(x.numerator)
    sgn = "-" if x.numerator < 0 else ""
    a = abs(x.numerator)
    b = x.denominator
    return f"{sgn}\\frac{{{a}}}{{{b}}}"


def _write_eq_tex(
    tex_out: Path,
    detA: Fraction,
    kemeny: Fraction,
    p_star: int,
) -> None:
    num_fac = _factorint(detA.numerator)
    den_fac = _factorint(detA.denominator)
    num_tex = " \\cdot ".join([f"{p}^{{{e}}}" if e != 1 else f"{p}" for p, e in sorted(num_fac.items())])
    den_tex = " \\cdot ".join([f"{p}^{{{e}}}" if e != 1 else f"{p}" for p, e in sorted(den_fac.items())])

    k_den_fac = _factorint(kemeny.denominator)
    k_den_tex = " \\cdot ".join([f"{p}^{{{e}}}" if e != 1 else f"{p}" for p, e in sorted(k_den_fac.items())])

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_window6_green_kernel_audit_prime_571.py")
    lines.append("\\begin{equation}\\label{eq:window6_green_kernel_audit_prime_571}")
    lines.append("\\begin{aligned}")
    lines.append(f"p_\\star&:={p_star},\\\\")
    lines.append(
        "\\det\\bigl(I-T+\\mathbf 1\\pi^\\top\\bigr)"
        f"&=\\frac{{{detA.numerator}}}{{{detA.denominator}}}"
        f"=\\frac{{{num_tex}}}{{{den_tex}}},\\\\"
    )
    lines.append(
        "K"
        ":=\\sum_{\\lambda\\in\\mathrm{Spec}(T)\\setminus\\{1\\}}\\frac{1}{1-\\lambda}"
        f"=\\frac{{{kemeny.numerator}}}{{{kemeny.denominator}}}"
        f"=\\frac{{{kemeny.numerator}}}{{{k_den_tex}}}."
    )
    lines.append("\\end{aligned}")
    lines.append("\\end{equation}")
    lines.append("")
    tex_out.write_text("\n".join(lines), encoding="utf-8")


def _write_Z_table(tex_out: Path, blocks: Sequence[str], Z: List[List[Fraction]]) -> None:
    def cell(i: int, j: int) -> str:
        return f"$({_frac_tex(Z[i][j])})$"

    header = " & " + " & ".join([f"$U_{b}$" for b in blocks]) + " \\\\"
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append("\\caption{Window-6 four-block fundamental matrix $Z=(I-T+\\mathbf 1\\pi^\\top)^{-1}$ (exact rationals).}")
    lines.append("\\label{tab:window6_green_kernel_Z}")
    lines.append("\\begin{tabular}{c c c c c}")
    lines.append("\\toprule")
    lines.append(header)
    lines.append("\\midrule")
    for i, b in enumerate(blocks):
        lines.append(f"$U_{b}$ & " + " & ".join([cell(i, j) for j in range(4)]) + " \\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")
    tex_out.write_text("\n".join(lines), encoding="utf-8")


def _write_mfp_table(
    tex_out: Path, blocks: Sequence[str], m: List[List[Fraction]], only_offdiag: bool = True
) -> None:
    def cell(i: int, j: int) -> str:
        if only_offdiag and i == j:
            return "--"
        return f"$({_frac_tex(m[i][j])})$"

    header = " & " + " & ".join([f"$U_{b}$" for b in blocks]) + " \\\\"
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Mean first passage times $m_{\\alpha\\to\\beta}$ for the window-6 four-block coarse chain $T$ (exact rationals; diagonal omitted).}"
    )
    lines.append("\\label{tab:window6_mean_first_passage_times}")
    lines.append("\\begin{tabular}{c c c c c}")
    lines.append("\\toprule")
    lines.append(header)
    lines.append("\\midrule")
    for i, b in enumerate(blocks):
        lines.append(f"$U_{b}$ & " + " & ".join([cell(i, j) for j in range(4)]) + " \\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")
    tex_out.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit window-6 Green kernel arithmetic and prime 571.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "window6_green_kernel_audit_prime_571.json"),
        help="Output JSON path.",
    )
    ap.add_argument(
        "--eq-tex-out",
        type=str,
        default=str(generated_dir() / "eq_window6_green_kernel_audit_prime_571.tex"),
        help="Output TeX equation path.",
    )
    ap.add_argument(
        "--Z-tex-out",
        type=str,
        default=str(generated_dir() / "tab_window6_green_kernel_Z.tex"),
        help="Output TeX table path for Z.",
    )
    ap.add_argument(
        "--mfp-tex-out",
        type=str,
        default=str(generated_dir() / "tab_window6_mean_first_passage_times.tex"),
        help="Output TeX table path for mean first passage times.",
    )
    args = ap.parse_args()

    blocks, U_sizes, E, T, pi = _coarse_kernel_T()
    n = 4

    # (1) Tree number of the undirected block quotient graph (ignore self-loops).
    L = _laplacian_from_E_offdiag(E)
    tau = _det_fraction(_minor_int(L, drop=0))
    if tau.denominator != 1:
        raise AssertionError("Expected integer tree number.")
    tau_int = int(tau.numerator)
    tau_fac = _factorint(tau_int)
    # audit prime: unique factor not dividing 6
    p_star_candidates = sorted([p for p in tau_fac.keys() if p not in (2, 3)])
    if p_star_candidates != [571]:
        raise AssertionError(f"Unexpected p_star candidates: {p_star_candidates}, tau_fac={tau_fac}")
    p_star = p_star_candidates[0]

    # (2) Fundamental matrix Z = (I - T + 1*pi^T)^{-1}.
    A = [[Fraction(int(i == j), 1) - T[i][j] + pi[j] for j in range(n)] for i in range(n)]
    detA = _det_fraction(A)
    Z = _inv_fraction(A)

    # (3) Kemeny constant: K = tr(Z) - 1 = sum_{lambda!=1} 1/(1-lambda).
    trZ = sum(Z[i][i] for i in range(n))
    kemeny = trZ - 1

    # Cross-check via p'(1)/p(1) for p(t) = (48114 t^3 + 7263 t^2 - 506 t - 55)/48114.
    f1 = 48114 + 7263 - 506 - 55
    fp1 = 3 * 48114 + 2 * 7263 - 506
    k_poly = Fraction(fp1, f1)  # same as p'(1)/p(1)
    if k_poly != kemeny:
        raise AssertionError(f"Kemeny mismatch: trace(Z)-1={kemeny}, p'(1)/p(1)={k_poly}")

    # (4) Mean first passage times (alpha != beta): m_ij = (Z_jj - Z_ij)/pi_j.
    mfp = [[Fraction(0, 1) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j:
                mfp[i][j] = Fraction(1, 1) / pi[j]
            else:
                mfp[i][j] = (Z[j][j] - Z[i][j]) / pi[j]

    primes_Z = _primes_in_denominators([Z[i][j] for i in range(n) for j in range(n)])
    primes_mfp_offdiag = _primes_in_denominators([mfp[i][j] for i in range(n) for j in range(n) if i != j])

    # Hard sanity checks (exact).
    if tau_int != 123336:
        raise AssertionError(f"Unexpected tau: {tau_int}")
    if detA != Fraction(9136, 8019):
        raise AssertionError(f"Unexpected det(A): {detA}")
    if kemeny != Fraction(79181, 27408):
        raise AssertionError(f"Unexpected Kemeny: {kemeny}")
    if set(primes_Z) != {2, 3, p_star}:
        raise AssertionError(f"Unexpected primes in Z denominators: {primes_Z}")
    if set(primes_mfp_offdiag) != {3, p_star}:
        raise AssertionError(f"Unexpected primes in mfp offdiag denominators: {primes_mfp_offdiag}")

    payload = {
        "blocks": blocks,
        "U_sizes": U_sizes,
        "E_undirected": E,
        "tau_tree_number": {
            "tau": tau_int,
            "factorization": {str(p): int(e) for p, e in sorted(tau_fac.items())},
            "audit_prime_p_star": p_star,
        },
        "pi": [str(x) for x in pi],
        "det_I_minus_T_plus_1piT": {
            "det": str(detA),
            "numerator": detA.numerator,
            "denominator": detA.denominator,
        },
        "Z": [[str(x) for x in row] for row in Z],
        "kemeny_constant": {
            "K": str(kemeny),
            "K_via_poly": str(k_poly),
        },
        "mean_first_passage_times": {
            "mfp": [[str(x) for x in row] for row in mfp],
            "primes_in_denominators_offdiag": primes_mfp_offdiag,
        },
        "primes_in_Z_denominators": primes_Z,
    }

    json_out = Path(str(args.json_out))
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    eq_tex_out = Path(str(args.eq_tex_out))
    eq_tex_out.parent.mkdir(parents=True, exist_ok=True)
    _write_eq_tex(eq_tex_out, detA=detA, kemeny=kemeny, p_star=p_star)

    Z_tex_out = Path(str(args.Z_tex_out))
    Z_tex_out.parent.mkdir(parents=True, exist_ok=True)
    _write_Z_table(Z_tex_out, blocks=blocks, Z=Z)

    mfp_tex_out = Path(str(args.mfp_tex_out))
    mfp_tex_out.parent.mkdir(parents=True, exist_ok=True)
    _write_mfp_table(mfp_tex_out, blocks=blocks, m=mfp, only_offdiag=True)


if __name__ == "__main__":
    main()

