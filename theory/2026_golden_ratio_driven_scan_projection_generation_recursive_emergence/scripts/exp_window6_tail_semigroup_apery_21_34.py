#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: Apéry thresholds and minimal representatives for <21,34>.

All output is English-only by repository convention.

We work with the two-generator numerical semigroup
  S := <21,34> ⊂ N,
which coincides with <21,34,55> since 55=21+34.

We compute the Apéry set with respect to 21:
  w_r := min{ s∈S : s ≡ r (mod 21) },   r=0..20,
and the canonical residue b_r ∈ {0..20} such that
  w_r = 34*b_r  and  34*b_r ≡ r (mod 21).

We also export minimal reachable dimension representatives
  D_r^min := 12 + w_r
and their Zeckendorf index sets S(D_r^min) in Fibonacci indices.

Outputs:
  - artifacts/export/window6_tail_semigroup_apery_21_34.json
  - sections/generated/tab_window6_tail_semigroup_apery_21_34.tex
  - sections/generated/tab_window6_tail_semigroup_minrep_zeckendorf_signatures.tex
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import fib_upto, zeckendorf_digits


def _m_for_zeckendorf(N: int) -> int:
    """Smallest m such that F_{m+2} > N (F_1=F_2=1)."""
    if N < 0:
        raise ValueError("N must be non-negative")
    fib = [1, 1]  # F1,F2
    while fib[-1] <= N:
        fib.append(fib[-1] + fib[-2])
    # fib[-1] is F_k > N, hence m+2 = k and m = k-2.
    k = len(fib)
    return k - 2


def _zeckendorf_index_set(N: int) -> List[int]:
    """Return the Zeckendorf index set S: N = sum_{k in S} F_k."""
    if N == 0:
        return []
    m = _m_for_zeckendorf(N)
    digits = zeckendorf_digits(N, m)  # c_1..c_m for weights F_{k+1}
    idx: List[int] = []
    for k, b in enumerate(digits, start=1):
        if b:
            idx.append(k + 1)  # weight index is (k+1)
    # Sanity: indices are strictly increasing and non-adjacent.
    for a, b in zip(idx, idx[1:]):
        if b - a == 1:
            raise AssertionError("Zeckendorf indices adjacent (should be impossible).")
    return idx


def _format_index_set(idx: List[int]) -> str:
    if not idx:
        return r"\varnothing"
    return r"\{" + ",".join(str(x) for x in idx) + r"\}"


def main() -> None:
    ap = argparse.ArgumentParser(description="Compute Apéry table and minimal Zeckendorf signatures for <21,34>.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "window6_tail_semigroup_apery_21_34.json"),
        help="Output JSON path.",
    )
    ap.add_argument(
        "--tex-out-apery",
        type=str,
        default=str(generated_dir() / "tab_window6_tail_semigroup_apery_21_34.tex"),
        help="Output TeX table path (Apéry thresholds).",
    )
    ap.add_argument(
        "--tex-out-minrep",
        type=str,
        default=str(generated_dir() / "tab_window6_tail_semigroup_minrep_zeckendorf_signatures.tex"),
        help="Output TeX table path (minimal representatives and Zeckendorf index sets).",
    )
    args = ap.parse_args()

    a = 21
    b = 34
    D0 = 12

    # 34 ≡ 13 (mod 21) and 13^{-1} ≡ 13 (mod 21).
    inv = pow(b % a, -1, a)
    if (inv * (b % a)) % a != 1:
        raise AssertionError("Modular inverse sanity check failed.")

    rows: List[Dict[str, int]] = []
    for r in range(a):
        br = (inv * r) % a
        wr = b * br
        if wr % a != r:
            raise AssertionError("Residue mismatch in Apéry construction.")
        gr = (wr - r) // a
        if r + a * gr != wr:
            raise AssertionError("g_r formula mismatch.")
        rows.append({"r": r, "b_r": br, "w_r": wr, "g_r": gr})

    # Sanity checks: involution and genus sum.
    bmap = {row["r"]: row["b_r"] for row in rows}
    for r in range(a):
        if bmap[bmap[r]] != r:
            raise AssertionError("Expected involution r -> b_r -> r.")
    genus = sum(row["g_r"] for row in rows)
    if genus != (a - 1) * (b - 1) // 2:
        raise AssertionError("Genus sum mismatch for two-generator semigroup.")

    # Minimal representatives and Zeckendorf index sets.
    minrep_rows: List[Dict[str, object]] = []
    seen_sig: Dict[Tuple[int, ...], int] = {}
    for row in rows:
        r = int(row["r"])
        wr = int(row["w_r"])
        Dmin = D0 + wr
        sig = tuple(_zeckendorf_index_set(Dmin))
        if sig in seen_sig:
            raise AssertionError(f"Duplicate Zeckendorf signature for r={r} and r={seen_sig[sig]}.")
        seen_sig[sig] = r
        if 2 not in sig or 3 in sig:
            raise AssertionError(f"Signature constraint failed for r={r}: sig={sig}.")
        minrep_rows.append({"r": r, "Dmin": Dmin, "sig": list(sig)})

    payload = {
        "semigroup": {"generators": [a, b], "note": "S=<21,34> equals <21,34,55> since 55=21+34."},
        "modulus": a,
        "inverse_b_mod_a": inv,
        "apery_rows": rows,
        "genus_sum_g_r": genus,
        "minrep_rows": minrep_rows,
    }

    json_out = Path(str(args.json_out))
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # TeX table: Apéry thresholds.
    tex_ap = Path(str(args.tex_out_apery))
    tex_ap.parent.mkdir(parents=True, exist_ok=True)
    ap_lines: List[str] = []
    ap_lines.append("% AUTO-GENERATED by scripts/exp_window6_tail_semigroup_apery_21_34.py")
    ap_lines.append("\\begin{table}[H]")
    ap_lines.append("\\centering")
    ap_lines.append("\\small")
    ap_lines.append("\\setlength{\\tabcolsep}{7pt}")
    ap_lines.append("\\renewcommand{\\arraystretch}{1.12}")
    ap_lines.append(
        "\\caption{Ap\\'ery thresholds for the numerical semigroup $\\langle 21,34\\rangle$ modulo $21$: "
        "for each residue $r\\in\\{0,\\dots,20\\}$ we list the canonical $b_r\\in\\{0,\\dots,20\\}$ with $34b_r\\equiv r\\pmod{21}$, "
        "the Ap\\'ery element $w_r=34b_r$, and the gap count $g_r=(w_r-r)/21$.}"
    )
    ap_lines.append("\\label{tab:window6_tail_semigroup_apery_21_34}")
    ap_lines.append("\\begin{tabular}{r r r r}")
    ap_lines.append("\\toprule")
    ap_lines.append("$r$ & $b_r$ & $w_r$ & $g_r$ \\\\")
    ap_lines.append("\\midrule")
    for row in rows:
        ap_lines.append(f"{row['r']} & {row['b_r']} & {row['w_r']} & {row['g_r']} \\\\")
    ap_lines.append("\\bottomrule")
    ap_lines.append("\\end{tabular}")
    ap_lines.append("\\end{table}")
    ap_lines.append("")
    tex_ap.write_text("\n".join(ap_lines), encoding="utf-8")

    # TeX table: minimal representatives and Zeckendorf index sets.
    tex_mr = Path(str(args.tex_out_minrep))
    tex_mr.parent.mkdir(parents=True, exist_ok=True)
    mr_lines: List[str] = []
    mr_lines.append("% AUTO-GENERATED by scripts/exp_window6_tail_semigroup_apery_21_34.py")
    mr_lines.append("\\begin{table}[H]")
    mr_lines.append("\\centering")
    mr_lines.append("\\small")
    mr_lines.append("\\setlength{\\tabcolsep}{7pt}")
    mr_lines.append("\\renewcommand{\\arraystretch}{1.12}")
    mr_lines.append(
        "\\caption{Minimal reachable representatives $D_r^{\\min}=12+w_r$ for each residue class $r\\pmod{21}$, "
        "together with their Zeckendorf index sets $S(D_r^{\\min})$ in Fibonacci indices (so $D_r^{\\min}=\\sum_{k\\in S}F_k$).}"
    )
    mr_lines.append("\\label{tab:window6_tail_semigroup_minrep_zeckendorf_signatures}")
    mr_lines.append("\\begin{tabular}{r r l}")
    mr_lines.append("\\toprule")
    mr_lines.append("$r$ & $D_r^{\\min}$ & $S(D_r^{\\min})$ \\\\")
    mr_lines.append("\\midrule")
    for rr in minrep_rows:
        r = int(rr["r"])
        Dmin = int(rr["Dmin"])
        sig = [int(x) for x in rr["sig"]]  # type: ignore[assignment]
        mr_lines.append(f"{r} & {Dmin} & ${_format_index_set(sig)}$ \\\\")
    mr_lines.append("\\bottomrule")
    mr_lines.append("\\end{tabular}")
    mr_lines.append("\\end{table}")
    mr_lines.append("")
    tex_mr.write_text("\n".join(mr_lines), encoding="utf-8")

    print(f"File: {json_out.relative_to(export_dir().parent.parent)}")
    print(f"File: {tex_ap.relative_to(generated_dir().parent.parent)}")
    print(f"File: {tex_mr.relative_to(generated_dir().parent.parent)}")


if __name__ == "__main__":
    main()

