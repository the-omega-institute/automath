#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit certificate for the pushforward kernels P_m induced by Fold^{bin}_m.

All code is English-only by repository convention.

For each m in the configured list (default: 5,6,7,8,9), this script builds
the Fold^{bin}_m pushforward kernel
    P_m(w,w') = A_m(w,w') / (m * d^{bin}_m(w))
on X_m (golden-legal words of length m), computes the nontrivial factor
    chi_{P_m}(lambda) = (lambda - 1) q_m(lambda),
and certifies:
  - irreducibility of q_m over Q,
  - squarefreeness of q_m,
  - existence of unramified primes with factor-degree patterns [deg q_m]
    and [deg q_m - 1, 1] in F_p[lambda].

These certificates imply that the splitting-field Galois group contains an
n-cycle and an (n-1)-cycle (n = deg q_m), hence equals S_n.

Outputs:
  - artifacts/export/window_pushforward_markov_full_symmetric_galois_audit_m5_m9.json
  - sections/generated/eq_window6_pushforward_markov_charpoly_q6.tex
  - sections/generated/tab_window_pushforward_markov_full_symmetric_galois_audit_m5_m9.tex
"""

from __future__ import annotations

import argparse
import json
import warnings
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np
import sympy as sp

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, word_to_str, zeckendorf_digits

try:
    from sympy.utilities.exceptions import SymPyDeprecationWarning

    warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)
except Exception:
    # Compatibility fallback if SymPy changes warning paths.
    pass


@dataclass(frozen=True)
class Row:
    m: int
    x_size: int
    degree_q: int
    expected_degree_q: int
    denominator_lcm: str
    irreducible_over_Q: bool
    factor_degrees_over_Q: List[int]
    squarefree_over_Q: bool
    p_irreducible: int
    factor_degrees_mod_p_irreducible: List[int]
    p_nminus1_1: int
    factor_degrees_mod_p_nminus1_1: List[int]
    full_symmetric_group_certificate: bool


def _fib(n: int) -> int:
    if n <= 2:
        return 1
    a, b = 1, 1
    for _ in range(3, n + 1):
        a, b = b, a + b
    return b


def _K_of_limit(limit: int) -> int:
    if limit < 0:
        raise ValueError("limit must be non-negative")
    fib = [1, 1]
    while fib[-1] <= limit:
        fib.append(fib[-1] + fib[-2])
    return len(fib) - 2


def _fold_bin_prefix_word(n: int, m: int) -> str:
    limit = (1 << m) - 1
    if not (0 <= n <= limit):
        raise ValueError(f"n must be in [0,{limit}] for m={m}")
    K = _K_of_limit(limit)
    digits = zeckendorf_digits(n, K)
    return word_to_str(digits[:m])


def _build_pushforward_kernel(
    m: int,
) -> Tuple[List[str], List[int], List[List[int]], List[List[Fraction]]]:
    labels = [_fold_bin_prefix_word(n, m) for n in range(1 << m)]
    words = sorted(set(labels))
    idx = {w: i for i, w in enumerate(words)}

    d = [0 for _ in words]
    for n in range(1 << m):
        d[idx[labels[n]]] += 1

    A = [[0 for _ in words] for _ in words]
    for n in range(1 << m):
        i = idx[labels[n]]
        for j in range(m):
            nn = n ^ (1 << j)
            k = idx[labels[nn]]
            A[i][k] += 1

    P: List[List[Fraction]] = [[Fraction(0) for _ in words] for _ in words]
    for i in range(len(words)):
        denom = Fraction(m * d[i], 1)
        for j in range(len(words)):
            P[i][j] = Fraction(A[i][j], 1) / denom

    expected_x_size = _fib(m + 2)
    if len(words) != expected_x_size:
        raise RuntimeError(
            f"Unexpected |X_{m}|={len(words)} (expected Fibonacci count {expected_x_size})."
        )
    return words, d, A, P


def _nontrivial_factor_q(poly_chi: sp.Poly) -> sp.Poly:
    x = poly_chi.gens[0]
    q, rem = sp.div(poly_chi, sp.Poly(x - 1, x, domain=sp.QQ), domain=sp.QQ)
    rem_poly = sp.Poly(rem.as_expr(), x, domain=sp.QQ)
    if rem_poly.as_expr() != 0:
        raise RuntimeError("Expected (lambda-1) factor in chi_{P_m}, but remainder is nonzero.")
    return sp.Poly(q.as_expr(), x, domain=sp.QQ)


def _factor_degrees_over_Q(poly_q: sp.Poly) -> List[int]:
    x = poly_q.gens[0]
    _, facs = sp.factor_list(poly_q)
    degs: List[int] = []
    for f, e in facs:
        deg = int(sp.Poly(f, x, domain=sp.QQ).degree())
        degs.extend([deg] * int(e))
    degs.sort(reverse=True)
    return degs


def _clear_denoms_Z(poly_q: sp.Poly) -> Tuple[int, sp.Poly]:
    L_raw, f_raw = poly_q.clear_denoms(convert=True)
    x = poly_q.gens[0]
    L = int(L_raw)
    f = sp.Poly(f_raw, x, domain=sp.ZZ)
    return L, f


def _factor_degrees_mod_p_int_poly(poly_Z: sp.Poly, p: int) -> Tuple[bool, List[int]]:
    x = poly_Z.gens[0]
    f = sp.Poly(poly_Z.as_expr(), x, modulus=p)
    g = sp.gcd(f, f.diff())
    squarefree = bool(g.degree() == 0)
    _, facs = sp.factor_list(f, modulus=p)
    degs: List[int] = []
    for ff, ee in facs:
        deg = int(sp.Poly(ff, x, modulus=p).degree())
        degs.extend([deg] * int(ee))
    degs.sort(reverse=True)
    return squarefree, degs


def _find_prime_with_degrees(
    *,
    poly_Z: sp.Poly,
    denom_lcm: int,
    target_degrees: Sequence[int],
    p_max: int,
    progress: Progress,
    progress_label: str,
) -> Tuple[int, List[int]]:
    want = sorted([int(x) for x in target_degrees], reverse=True)
    checked = 0
    for p_sym in sp.primerange(2, p_max + 1):
        p = int(p_sym)
        if denom_lcm % p == 0:
            continue
        checked += 1
        if checked % 64 == 0:
            progress.tick(f"{progress_label}: checked {checked} primes (latest p={p})")
        squarefree, degs = _factor_degrees_mod_p_int_poly(poly_Z, p)
        if squarefree and degs == want:
            return p, degs
    raise RuntimeError(
        f"Failed to find prime with factor-degree pattern {want} up to p_max={p_max}."
    )


def _frac_to_tex(q: sp.Rational) -> str:
    qq = sp.Rational(q)
    if int(qq.q) == 1:
        return str(int(qq.p))
    return f"\\frac{{{int(qq.p)}}}{{{int(qq.q)}}}"


def _poly_to_aligned_terms(poly_q: sp.Poly, *, var_tex: str = "\\lambda") -> List[str]:
    deg = int(poly_q.degree())
    coeffs = [sp.Rational(c) for c in poly_q.all_coeffs()]

    atoms: List[Tuple[int, str]] = []
    for i, c in enumerate(coeffs):
        if c == 0:
            continue
        sign = 1 if c > 0 else -1
        a = abs(c)
        p = deg - i

        if p == 0:
            mon = _frac_to_tex(a)
        elif p == 1:
            if a == 1:
                mon = var_tex
            else:
                mon = f"{_frac_to_tex(a)}{var_tex}"
        else:
            if a == 1:
                mon = f"{var_tex}^{{{p}}}"
            else:
                mon = f"{_frac_to_tex(a)}{var_tex}^{{{p}}}"
        atoms.append((sign, mon))

    out: List[str] = []
    for k, (sign, mon) in enumerate(atoms):
        if k == 0:
            out.append(mon if sign > 0 else f"-{mon}")
        else:
            out.append(f" + {mon}" if sign > 0 else f" - {mon}")
    return out


def _write_eq_q6(
    *,
    q6: sp.Poly,
    L6: int,
    lambda2: float,
    lambda_min: float,
    out_path: Path,
) -> None:
    terms = _poly_to_aligned_terms(q6, var_tex="\\lambda")
    per_line = 4
    chunks = [terms[i : i + per_line] for i in range(0, len(terms), per_line)]

    lines: List[str] = []
    lines.append(
        "% AUTO-GENERATED by scripts/exp_window_pushforward_markov_full_symmetric_galois_audit.py"
    )
    lines.append("\\begin{equation}\\label{eq:window6_pushforward_markov_charpoly_q6}")
    lines.append("\\begin{aligned}")
    lines.append("\\chi_{P_6}(\\lambda)&=(\\lambda-1)q_6(\\lambda),\\\\")
    if chunks:
        lines.append("q_6(\\lambda)=&" + "".join(chunks[0]) + "\\\\")
        for chunk in chunks[1:-1]:
            lines.append("&" + "".join(chunk) + "\\\\")
        if len(chunks) >= 2:
            lines.append("&" + "".join(chunks[-1]) + ",\\\\")
        else:
            lines[-1] = lines[-1][:-2] + ",\\\\"
    lines.append(
        f"L_6\\,q_6(\\lambda)&\\in\\ZZ[\\lambda],\\qquad L_6={L6},\\\\"
    )
    lines.append(
        "\\lambda_2(P_6)&\\approx "
        + f"{lambda2:.15f}"
        + ",\\qquad\\lambda_{\\min}(P_6)\\approx "
        + f"{lambda_min:.15f}"
        + "."
    )
    lines.append("\\end{aligned}")
    lines.append("\\end{equation}")
    lines.append("")

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines), encoding="utf-8")


def _fmt_degrees(ds: Sequence[int]) -> str:
    return "(" + ",".join(str(int(x)) for x in ds) + ")"


def _write_table(rows: Sequence[Row], out_path: Path) -> None:
    lines: List[str] = []
    lines.append(
        "% AUTO-GENERATED by scripts/exp_window_pushforward_markov_full_symmetric_galois_audit.py"
    )
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append(
        "\\caption{对 $m\\in\\{5,6,7,8,9\\}$ 的 $P_m$ 非平凡谱多项式 $q_m$ 的可复核证书。"
        "列出不可约性、模素数分解次数型 $[\\deg q_m]$ 与 $[\\deg q_m-1,1]$，"
        "从而给出满对称群证书。}"
    )
    lines.append("\\label{tab:window_pushforward_markov_full_symmetric_galois_audit_m5_m9}")
    lines.append("\\begin{tabular}{r r c r l r l l}")
    lines.append("\\toprule")
    lines.append(
        "$m$ & $\\deg q_m$ & irreducible over $\\QQ$ & $p_{\\mathrm{irr}}$ & degs mod $p_{\\mathrm{irr}}$ & "
        "$p_{(n-1,1)}$ & degs mod $p_{(n-1,1)}$ & certified $\\mathrm{Gal}$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        irred = "yes" if r.irreducible_over_Q else "no"
        gal = f"$S_{{{r.degree_q}}}$" if r.full_symmetric_group_certificate else "--"
        lines.append(
            f"{r.m} & {r.degree_q} & {irred} & {r.p_irreducible} & ${_fmt_degrees(r.factor_degrees_mod_p_irreducible)}$ & "
            f"{r.p_nminus1_1} & ${_fmt_degrees(r.factor_degrees_mod_p_nminus1_1)}$ & {gal}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines), encoding="utf-8")


def _spectral_extrema_m6(P: List[List[Fraction]], d: Sequence[int]) -> Tuple[float, float]:
    n = len(P)
    P_np = np.zeros((n, n), dtype=np.float64)
    for i in range(n):
        for j in range(n):
            P_np[i, j] = float(P[i][j])
    pi = np.array([float(di / 64.0) for di in d], dtype=np.float64)
    s = np.sqrt(pi)
    S = (s[:, None] * P_np) / s[None, :]
    S = 0.5 * (S + S.T)
    evals = np.linalg.eigvalsh(S)  # ascending
    evals_desc = evals[::-1]
    lambda1 = float(evals_desc[0])
    if abs(lambda1 - 1.0) > 1e-10:
        raise RuntimeError(f"Unexpected top eigenvalue for P_6: {lambda1}")
    return float(evals_desc[1]), float(evals_desc[-1])


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Audit q_m irreducibility and full-symmetric Galois certificates for Fold^{bin}_m pushforward kernels."
    )
    ap.add_argument(
        "--m-list",
        type=str,
        default="5,6,7,8,9",
        help="Comma-separated window sizes m.",
    )
    ap.add_argument(
        "--p-max",
        type=int,
        default=20000,
        help="Prime search upper bound for mod-p degree certificates.",
    )
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "window_pushforward_markov_full_symmetric_galois_audit_m5_m9.json"),
    )
    ap.add_argument(
        "--tex-eq-out",
        type=str,
        default=str(generated_dir() / "eq_window6_pushforward_markov_charpoly_q6.tex"),
    )
    ap.add_argument(
        "--tex-tab-out",
        type=str,
        default=str(generated_dir() / "tab_window_pushforward_markov_full_symmetric_galois_audit_m5_m9.tex"),
    )
    args = ap.parse_args()

    m_list = [int(x.strip()) for x in str(args.m_list).split(",") if x.strip()]
    if not m_list:
        raise SystemExit("Empty --m-list")
    if min(m_list) < 2:
        raise SystemExit("Require m >= 2")

    progress = Progress("window-pushforward-galois")
    x = sp.Symbol("lambda")

    rows: List[Row] = []
    q6: sp.Poly | None = None
    L6: int | None = None
    lambda2: float | None = None
    lambda_min: float | None = None

    for m in m_list:
        progress.tick(f"build P_m and chi for m={m}")
        words, d, _A, P = _build_pushforward_kernel(m)

        P_sym = sp.Matrix(
            [[sp.Rational(fr.numerator, fr.denominator) for fr in row] for row in P]
        )
        chi = sp.Poly(sp.expand(P_sym.charpoly(x).as_expr()), x, domain=sp.QQ)
        q = _nontrivial_factor_q(chi)

        deg_q = int(q.degree())
        expected_deg_q = _fib(m + 2) - 1
        if deg_q != expected_deg_q:
            raise RuntimeError(
                f"Degree mismatch for m={m}: got deg q_m={deg_q}, expected {expected_deg_q}."
            )

        degs_Q = _factor_degrees_over_Q(q)
        irreducible = bool(len(degs_Q) == 1 and degs_Q[0] == deg_q)
        squarefree = bool(sp.gcd(q, q.diff()).degree() == 0)
        L, f_int = _clear_denoms_Z(q)

        progress.tick(f"search mod-p [n] certificate for m={m}")
        p_irr, degs_irr = _find_prime_with_degrees(
            poly_Z=f_int,
            denom_lcm=L,
            target_degrees=[deg_q],
            p_max=int(args.p_max),
            progress=progress,
            progress_label=f"m={m} [n]",
        )
        progress.tick(f"search mod-p [n-1,1] certificate for m={m}")
        p_nm1, degs_nm1 = _find_prime_with_degrees(
            poly_Z=f_int,
            denom_lcm=L,
            target_degrees=[deg_q - 1, 1],
            p_max=int(args.p_max),
            progress=progress,
            progress_label=f"m={m} [n-1,1]",
        )

        cert_full_symmetric = bool(irreducible and degs_irr == [deg_q] and degs_nm1 == [deg_q - 1, 1])

        # Guard rails for m=5,6,7 certificates used explicitly in the manuscript.
        expected_small_primes = {
            5: (101, 53),
            6: (41, 137),
            7: (37, 83),
        }
        if m in expected_small_primes:
            p_expected = expected_small_primes[m]
            if (p_irr, p_nm1) != p_expected:
                raise RuntimeError(
                    f"Unexpected certificate primes for m={m}: got {(p_irr, p_nm1)}, expected {p_expected}."
                )

        rows.append(
            Row(
                m=int(m),
                x_size=int(len(words)),
                degree_q=int(deg_q),
                expected_degree_q=int(expected_deg_q),
                denominator_lcm=str(int(L)),
                irreducible_over_Q=bool(irreducible),
                factor_degrees_over_Q=[int(v) for v in degs_Q],
                squarefree_over_Q=bool(squarefree),
                p_irreducible=int(p_irr),
                factor_degrees_mod_p_irreducible=[int(v) for v in degs_irr],
                p_nminus1_1=int(p_nm1),
                factor_degrees_mod_p_nminus1_1=[int(v) for v in degs_nm1],
                full_symmetric_group_certificate=bool(cert_full_symmetric),
            )
        )

        if m == 6:
            q6 = q
            L6 = int(L)
            lambda2, lambda_min = _spectral_extrema_m6(P, d)

        progress.tick(f"finished m={m}")

    rows = sorted(rows, key=lambda r: r.m)

    if q6 is None or L6 is None or lambda2 is None or lambda_min is None:
        raise RuntimeError("m=6 must be included in --m-list to emit q6 equation output.")

    payload: Dict[str, object] = {
        "m_list": [int(m) for m in m_list],
        "rows": [asdict(r) for r in rows],
        "m6_details": {
            "q6_expr": sp.sstr(q6.as_expr()),
            "lambda2": float(lambda2),
            "lambda_min": float(lambda_min),
        },
        "certificate_logic": {
            "criterion": "irreducible over Q + mod-p degree patterns [n] and [n-1,1] => full symmetric group S_n",
            "n_equals": "deg q_m",
        },
    }

    json_out = Path(str(args.json_out))
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    tex_eq_out = Path(str(args.tex_eq_out))
    _write_eq_q6(
        q6=q6,
        L6=L6,
        lambda2=float(lambda2),
        lambda_min=float(lambda_min),
        out_path=tex_eq_out,
    )

    tex_tab_out = Path(str(args.tex_tab_out))
    _write_table(rows, tex_tab_out)

    print(f"[window-pushforward-galois] wrote {json_out}", flush=True)
    print(f"[window-pushforward-galois] wrote {tex_eq_out}", flush=True)
    print(f"[window-pushforward-galois] wrote {tex_tab_out}", flush=True)


if __name__ == "__main__":
    main()

