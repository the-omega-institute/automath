#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
m=11 boundary sector (|X_11^{bdry}|=34) canonical Fold_7 indexing,
Z_34 shift action, and real Fourier decomposition certificate.

This script is English-only by repository convention.

We build the canonical bijection:
  j in {0,...,33}  ->  u_j = Fold_7(j) in X_7
and the boundary embedding (pi-channel endpoint fiber):
  w_j = 10 u_j 01 in X_11^{bdry}.

On the 34-dim real space with basis {e_j}, we define the cyclic shift
  T e_j = e_{j+1 mod 34}.
Its real representation decomposes canonically as:
  R^{34} = <Y0>  ⊕  <Y17>  ⊕  ⊕_{k=1}^{16} span{C_k, S_k},
where Y0 is the uniform vector, Y17 is the alternating sign vector, and
(C_k,S_k) are the cosine/sine modes (real DFT pairs).

We also certify the paired spectrum for any real symmetric circulant kernel;
as a concrete auditable example we use the cycle adjacency A = T + T^{-1},
whose eigenvalues are 2 cos(2πk/34) with multiplicities 1,1,2,...,2.

Outputs:
  - artifacts/export/m11_boundary_z34_fourier_certificate.json
  - sections/generated/eq_m11_boundary_z34_fourier_split.tex
  - sections/generated/tab_m11_boundary_words_fold7.tex
  - sections/generated/tab_m11_z34_cycle_adjacency_spectrum.tex
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import fib_upto, is_golden_legal, word_to_str, zeckendorf_digits


def _fib(k: int) -> int:
    """Return Fibonacci F_k with convention F_1=F_2=1 (k>=1)."""
    if k <= 0:
        raise ValueError("k must be >= 1")
    return fib_upto(k)[-1]


def zeck_value_bits(bits: Sequence[int]) -> int:
    """Value N(bits)=sum_{i=1}^m bits_i * F_{i+1}, with F_1=F_2=1."""
    m = len(bits)
    if m == 0:
        return 0
    fib = fib_upto(m + 2)  # [F_1..F_{m+2}]
    N = 0
    for i, b in enumerate(bits, start=1):
        if b:
            N += fib[i]  # F_{i+1}
    return N


def fold_m_word_from_residue(*, m: int, r: int) -> str:
    """Canonical Fold_m restricted to r in [0, F_{m+2}-1] (bijective onto X_m)."""
    if m <= 0:
        raise ValueError("m must be positive")
    if r < 0:
        raise ValueError("r must be non-negative")
    M = _fib(m + 2)  # |X_m|
    if r >= M:
        raise ValueError(f"r must satisfy 0 <= r < F_(m+2)={M} (got r={r})")
    bits = zeckendorf_digits(r, m)
    if not is_golden_legal(bits):
        raise AssertionError("Zeckendorf digits violated golden admissibility.")
    if zeck_value_bits(bits) != r:
        raise AssertionError("Zeckendorf value mismatch (fold numbering not canonical).")
    return word_to_str(bits)


def boundary_word_from_u(*, u: str) -> str:
    """Boundary embedding u in X_{m-4} -> w=10 u 01 in X_m^{bdry} (here m=|u|+4)."""
    return "10" + u + "01"


def enumerate_xm_golden(m: int) -> List[str]:
    """Enumerate X_m as sorted bitstrings (no adjacent ones)."""
    if m < 0:
        raise ValueError("m must be non-negative")
    out: List[str] = []

    def rec(pos: int, prev1: bool, acc: List[str]) -> None:
        if pos == m:
            out.append("".join(acc))
            return
        acc.append("0")
        rec(pos + 1, False, acc)
        acc.pop()
        if not prev1:
            acc.append("1")
            rec(pos + 1, True, acc)
            acc.pop()

    rec(0, False, [])
    return sorted(out)


def enumerate_boundary_words_endpoints(m: int) -> List[str]:
    """Enumerate X_m^{bdry} = {w in X_m : w1=wm=1} as sorted bitstrings."""
    if m <= 0:
        return []
    Xm = enumerate_xm_golden(m)
    return [w for w in Xm if w[0] == "1" and w[-1] == "1"]


def shift_forward(v: Sequence[float]) -> List[float]:
    """T e_j = e_{j+1}; action on coordinates: (Tv)_j = v_{j-1}."""
    n = len(v)
    return [v[(j - 1) % n] for j in range(n)]


def shift_backward(v: Sequence[float]) -> List[float]:
    """T^{-1} e_j = e_{j-1}; action on coordinates: (T^{-1}v)_j = v_{j+1}."""
    n = len(v)
    return [v[(j + 1) % n] for j in range(n)]


def dot(u: Sequence[float], v: Sequence[float]) -> float:
    if len(u) != len(v):
        raise ValueError("dot: length mismatch")
    return sum(a * b for a, b in zip(u, v))


def l2_norm(v: Sequence[float]) -> float:
    return math.sqrt(dot(v, v))


def vec_add(u: Sequence[float], v: Sequence[float]) -> List[float]:
    return [a + b for a, b in zip(u, v)]


def vec_sub(u: Sequence[float], v: Sequence[float]) -> List[float]:
    return [a - b for a, b in zip(u, v)]


def vec_scale(a: float, v: Sequence[float]) -> List[float]:
    return [a * x for x in v]


def max_abs(v: Sequence[float]) -> float:
    return max(abs(x) for x in v) if v else 0.0


def build_real_fourier_basis(n: int) -> Dict[str, object]:
    """Return an orthonormal real Fourier basis and audit metrics."""
    if n <= 0:
        raise ValueError("n must be positive")
    if n % 2 != 0:
        raise ValueError("n must be even for the k=n/2 sign mode used here")

    inv_sqrt_n = 1.0 / math.sqrt(n)
    # Y0 (uniform)
    Y0 = [inv_sqrt_n] * n
    # Y_{n/2} (alternating sign)
    Yh = [inv_sqrt_n * (1.0 if (j % 2 == 0) else -1.0) for j in range(n)]

    modes: List[Dict[str, object]] = []
    modes.append({"k": 0, "type": "trivial", "vector": Y0})
    modes.append({"k": n // 2, "type": "sign", "vector": Yh})

    # Real 2D rotation modes
    for k in range(1, n // 2):
        theta = 2.0 * math.pi * k / n
        scale = math.sqrt(2.0 / n)
        Ck = [scale * math.cos(theta * j) for j in range(n)]
        Sk = [scale * math.sin(theta * j) for j in range(n)]
        modes.append({"k": k, "type": "pair", "theta": theta, "C": Ck, "S": Sk})

    # Orthonormality audit (max absolute dot error vs identity).
    # Build a flat list of vectors in the expected decomposition order:
    vecs: List[Tuple[str, int, List[float]]] = [("Y0", 0, Y0), ("Yh", n // 2, Yh)]
    for k in range(1, n // 2):
        entry = next(m for m in modes if m.get("k") == k)
        vecs.append(("C", k, list(entry["C"])))  # type: ignore[index]
        vecs.append(("S", k, list(entry["S"])))  # type: ignore[index]

    max_dot_err = 0.0
    for i, (ti, ki, vi) in enumerate(vecs):
        for j, (tj, kj, vj) in enumerate(vecs):
            target = 1.0 if i == j else 0.0
            err = abs(dot(vi, vj) - target)
            if err > max_dot_err:
                max_dot_err = err

    # Shift-action audit on each subspace
    max_shift_err = 0.0

    # T(Y0)=Y0
    err0 = l2_norm(vec_sub(shift_forward(Y0), Y0))
    max_shift_err = max(max_shift_err, err0)

    # T(Yh)=-Yh (since n even)
    errh = l2_norm(vec_add(shift_forward(Yh), Yh))
    max_shift_err = max(max_shift_err, errh)

    # For k=1..n/2-1: (C,S) rotates by angle -theta:
    #   T C = cos(theta) C + sin(theta) S
    #   T S = cos(theta) S - sin(theta) C
    for k in range(1, n // 2):
        theta = 2.0 * math.pi * k / n
        entry = next(m for m in modes if m.get("k") == k)
        Ck = entry["C"]  # type: ignore[index]
        Sk = entry["S"]  # type: ignore[index]
        TC = shift_forward(Ck)
        TS = shift_forward(Sk)
        rhs_TC = vec_add(vec_scale(math.cos(theta), Ck), vec_scale(math.sin(theta), Sk))
        rhs_TS = vec_sub(vec_scale(math.cos(theta), Sk), vec_scale(math.sin(theta), Ck))
        eC = l2_norm(vec_sub(TC, rhs_TC))
        eS = l2_norm(vec_sub(TS, rhs_TS))
        max_shift_err = max(max_shift_err, eC, eS)

    return {
        "n": n,
        "modes": modes,
        "audit": {
            "max_dot_error": max_dot_err,
            "max_shift_error_l2": max_shift_err,
        },
    }


def cycle_adjacency_spectrum(n: int) -> List[Dict[str, object]]:
    """Spectrum of A = T + T^{-1} on Z_n (cycle adjacency), in k=0..n/2 form."""
    if n <= 0:
        raise ValueError("n must be positive")
    if n % 2 != 0:
        raise ValueError("n must be even")
    rows: List[Dict[str, object]] = []
    for k in range(0, n // 2 + 1):
        theta = 2.0 * math.pi * k / n
        lam = 2.0 * math.cos(theta)
        mult = 1 if (k == 0 or k == n // 2) else 2
        rows.append({"k": k, "eigenvalue": lam, "multiplicity": mult})
    return rows


def write_outputs(*, tex_eq: Path, tex_tab: Path, tex_spec: Path, json_out: Path) -> None:
    # --- Canonical boundary enumeration: j -> u_j -> w_j ---
    m_u = 7
    m_bdry = 11
    n = _fib(m_u + 2)  # |X_7| = F_9 = 34
    assert n == 34, f"Expected |X_7|=34, got {n}"

    u_by_j = [fold_m_word_from_residue(m=m_u, r=j) for j in range(n)]
    if len(set(u_by_j)) != n:
        raise AssertionError("Fold_7(j) did not produce distinct X_7 words.")

    w_by_j = [boundary_word_from_u(u=u) for u in u_by_j]
    if any(len(w) != m_bdry for w in w_by_j):
        raise AssertionError("Boundary words have unexpected length.")
    if any("11" in w for w in w_by_j):
        raise AssertionError("Boundary words violated golden admissibility.")
    if any(w[0] != "1" or w[-1] != "1" for w in w_by_j):
        raise AssertionError("Boundary words violated endpoint predicate w1=wm=1.")

    # Cross-check: endpoint-boundary enumeration inside X_11 matches our construction.
    bdry11_sorted = enumerate_boundary_words_endpoints(m_bdry)
    if len(bdry11_sorted) != n:
        raise AssertionError(f"Expected |X_11^bdry|=34, got {len(bdry11_sorted)}")
    if set(bdry11_sorted) != set(w_by_j):
        raise AssertionError("Boundary word construction 10u01 did not match endpoint filter.")

    # --- Z_34 Fourier decomposition certificate ---
    fourier = build_real_fourier_basis(n)
    audit = fourier["audit"]  # type: ignore[index]

    # --- A concrete kernel spectrum: cycle adjacency A = T + T^{-1} ---
    spec = cycle_adjacency_spectrum(n)

    # Sanity: total multiplicity equals n.
    if sum(int(r["multiplicity"]) for r in spec) != n:
        raise AssertionError("Adjacency spectrum multiplicities did not sum to n.")

    # --- Write JSON certificate ---
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(
        json.dumps(
            {
                "n": n,
                "x7_words_by_j": u_by_j,
                "m11_boundary_words_by_j": w_by_j,
                "z34_real_fourier_audit": audit,
                "cycle_adjacency_spectrum_k0_to_17": spec,
                "notes": {
                    "boundary_embedding": "w_j = 10 u_j 01, with u_j = Fold_7(j) and j in [0,33].",
                    "shift_action": "T e_j = e_{j+1 mod 34}; on coordinates (Tv)_j = v_{j-1}.",
                    "real_decomposition": "R^34 = <Y0> ⊕ <Y17> ⊕ ⊕_{k=1}^{16} span{C_k,S_k}.",
                    "heavy_split": "Orthogonal complement of Y0 has dim 33 = 1 (k=17) + 16*(2).",
                },
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    # --- LaTeX equation fragment: 1 ⊕ 33 and 16 pairs + 1 ---
    eq_lines: List[str] = []
    eq_lines.append("% AUTO-GENERATED by scripts/exp_m11_boundary_z34_fourier_certificate.py")
    eq_lines.append("\\[")
    eq_lines.append("\\begin{aligned}")
    eq_lines.append(
        "\\mathbb{R}^{34}"
        " &= \\langle Y_0\\rangle\\ \\oplus\\ \\langle Y_{17}\\rangle\\ \\oplus\\ \\bigoplus_{k=1}^{16}\\mathrm{span}_{\\mathbb{R}}\\{C_k,S_k\\},\\\\"
    )
    eq_lines.append(
        "Y_0"
        " &:= \\frac{1}{\\sqrt{34}}\\sum_{j=0}^{33} e_j,\\qquad"
        " Y_{17}:=\\frac{1}{\\sqrt{34}}\\sum_{j=0}^{33}(-1)^j e_j,\\\\"
    )
    eq_lines.append(
        "C_k"
        " &:= \\sqrt{\\frac{2}{34}}\\sum_{j=0}^{33}\\cos\\!\\left(\\frac{2\\pi k j}{34}\\right)e_j,\\qquad"
        " S_k:= \\sqrt{\\frac{2}{34}}\\sum_{j=0}^{33}\\sin\\!\\left(\\frac{2\\pi k j}{34}\\right)e_j,\\qquad (k=1,\\dots,16),\\\\"
    )
    eq_lines.append(
        "T Y_0"
        " &= Y_0,\\qquad T Y_{17}=-Y_{17},\\\\"
    )
    eq_lines.append(
        "\\begin{pmatrix}T C_k\\\\ T S_k\\end{pmatrix}"
        " &= \\begin{pmatrix}\\cos\\theta_k & \\sin\\theta_k\\\\ -\\sin\\theta_k & \\cos\\theta_k\\end{pmatrix}"
        "\\begin{pmatrix}C_k\\\\ S_k\\end{pmatrix},\\qquad"
        " \\theta_k:=\\frac{2\\pi k}{34}."
    )
    eq_lines.append("\\end{aligned}")
    eq_lines.append("\\]")
    eq_lines.append("")
    eq_lines.append(
        "% Heavy complement: (\\langle Y_0\\rangle)^\\perp has dim 33 = 1 (k=17) + 16 pairs (k=1..16)."
    )
    eq_lines.append("")
    tex_eq.parent.mkdir(parents=True, exist_ok=True)
    tex_eq.write_text("\n".join(eq_lines), encoding="utf-8")

    # --- LaTeX table: canonical boundary words by Fold_7 numbering ---
    tab_lines: List[str] = []
    tab_lines.append("% AUTO-GENERATED by scripts/exp_m11_boundary_z34_fourier_certificate.py")
    tab_lines.append("\\begin{table}[H]")
    tab_lines.append("\\centering")
    tab_lines.append("\\small")
    tab_lines.append("\\setlength{\\tabcolsep}{7pt}")
    tab_lines.append("\\renewcommand{\\arraystretch}{1.12}")
    tab_lines.append("\\caption{Canonical $m=11$ boundary words indexed by $u_j=\\mathrm{Fold}_7(j)\\in X_7$ via $w_j=10\\,u_j\\,01\\in X_{11}^{\\mathrm{bdry}}$.}")
    tab_lines.append("\\label{tab:m11_boundary_words_fold7}")
    tab_lines.append("\\begin{tabular}{r l l}")
    tab_lines.append("\\toprule")
    tab_lines.append("$j$ & $u_j\\in X_7$ & $w_j\\in X_{11}^{\\mathrm{bdry}}$ \\\\")
    tab_lines.append("\\midrule")
    for j, (u, w) in enumerate(zip(u_by_j, w_by_j)):
        tab_lines.append(f"{j} & \\texttt{{{u}}} & \\texttt{{{w}}} \\\\")
    tab_lines.append("\\bottomrule")
    tab_lines.append("\\end{tabular}")
    tab_lines.append("\\end{table}")
    tab_lines.append("")
    tex_tab.parent.mkdir(parents=True, exist_ok=True)
    tex_tab.write_text("\n".join(tab_lines), encoding="utf-8")

    # --- LaTeX table: cycle adjacency spectrum (paired) ---
    spec_lines: List[str] = []
    spec_lines.append("% AUTO-GENERATED by scripts/exp_m11_boundary_z34_fourier_certificate.py")
    spec_lines.append("\\begin{table}[H]")
    spec_lines.append("\\centering")
    spec_lines.append("\\small")
    spec_lines.append("\\setlength{\\tabcolsep}{8pt}")
    spec_lines.append("\\renewcommand{\\arraystretch}{1.12}")
    spec_lines.append(
        "\\caption{Paired spectrum on the $34$-mode boundary sector for the commuting kernel "
        "$A:=T+T^{-1}$ (cycle adjacency). Eigenvalues are $\\lambda_k=2\\cos(2\\pi k/34)$ with "
        "multiplicity $1$ at $k\\in\\{0,17\\}$ and multiplicity $2$ for $k=1,\\dots,16$.}"
    )
    spec_lines.append("\\label{tab:m11_z34_cycle_adjacency_spectrum}")
    spec_lines.append("\\begin{tabular}{r r r}")
    spec_lines.append("\\toprule")
    spec_lines.append("$k$ & $\\lambda_k$ & mult \\\\")
    spec_lines.append("\\midrule")
    for r in spec:
        k = int(r["k"])
        lam = float(r["eigenvalue"])
        mult = int(r["multiplicity"])
        spec_lines.append(f"{k} & {lam:.12f} & {mult} \\\\")
    spec_lines.append("\\bottomrule")
    spec_lines.append("\\end{tabular}")
    spec_lines.append("\\end{table}")
    spec_lines.append("")
    tex_spec.parent.mkdir(parents=True, exist_ok=True)
    tex_spec.write_text("\n".join(spec_lines), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Certify m=11 boundary Z_34 Fourier split (1 ⊕ 33 = 1 ⊕ (16 pairs + 1)).")
    parser.add_argument(
        "--tex-eq",
        type=str,
        default=str(generated_dir() / "eq_m11_boundary_z34_fourier_split.tex"),
        help="Output LaTeX equation path.",
    )
    parser.add_argument(
        "--tex-tab",
        type=str,
        default=str(generated_dir() / "tab_m11_boundary_words_fold7.tex"),
        help="Output LaTeX table (boundary words) path.",
    )
    parser.add_argument(
        "--tex-spec",
        type=str,
        default=str(generated_dir() / "tab_m11_z34_cycle_adjacency_spectrum.tex"),
        help="Output LaTeX table (paired spectrum) path.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "m11_boundary_z34_fourier_certificate.json"),
        help="Output JSON certificate path.",
    )
    args = parser.parse_args()

    write_outputs(
        tex_eq=Path(args.tex_eq),
        tex_tab=Path(args.tex_tab),
        tex_spec=Path(args.tex_spec),
        json_out=Path(args.json_out),
    )
    print(f"[m11_z34_fourier] wrote {args.tex_eq}", flush=True)
    print(f"[m11_z34_fourier] wrote {args.tex_tab}", flush=True)
    print(f"[m11_z34_fourier] wrote {args.tex_spec}", flush=True)
    print(f"[m11_z34_fourier] wrote {args.json_out}", flush=True)


if __name__ == "__main__":
    main()

