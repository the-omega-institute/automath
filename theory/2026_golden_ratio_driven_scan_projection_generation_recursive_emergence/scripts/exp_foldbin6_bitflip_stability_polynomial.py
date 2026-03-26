#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: exact bit-flip noise stability polynomial for Fold^{bin}_6 ∘ int_6.

All output is English-only by repository convention.

Setup:
  - Omega_6 = {0,1}^6 is identified with integers {0,...,63} via the standard 6-bit binary encoding.
  - Fold^{bin}_6 : {0,...,63} -> X_6 is the Zeckendorf-prefix fold on the dyadic interval.
  - The label map is F6(omega) := Fold^{bin}_6(int_6(omega)).

Noise model:
  - W is uniform on Omega_6 (equivalently, uniform integer in {0,...,63}).
  - Each bit is flipped independently with probability p, yielding \\widetilde W.
  - Define the stability event S := {F6(W) = F6(\\widetilde W)}.

We compute the exact polynomial (degree 6):
  P(S) = sum_{k=0..6} a_k p^k,
with rational coefficients a_k.

Outputs:
  - artifacts/export/foldbin6_bitflip_stability_polynomial.json
  - sections/generated/eq_foldbin6_bitflip_stability_polynomial.tex
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import comb
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir
from common_phi_fold import word_to_str, zeckendorf_digits


def _foldbin6_label(n: int) -> str:
    # For m=6, K(6)=9 (F_{10}=55 ≤ 63 < F_{11}=89), so digits up to k=9 are exact.
    digits = zeckendorf_digits(n, 9)  # digits for weights F_{k+1}, k=1..9
    return word_to_str(digits[:6])


def _fmt_frac(fr: Fraction) -> str:
    if fr.denominator == 1:
        return str(fr.numerator)
    return f"\\frac{{{fr.numerator}}}{{{fr.denominator}}}"


def _poly_add_inplace(dst: List[Fraction], src: List[Fraction]) -> None:
    if len(dst) != len(src):
        raise ValueError("poly size mismatch")
    for i in range(len(dst)):
        dst[i] += src[i]


def main() -> None:
    ap = argparse.ArgumentParser(description="Compute exact Fold^{bin}_6 bit-flip stability polynomial.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "foldbin6_bitflip_stability_polynomial.json"),
        help="Path to JSON audit output.",
    )
    ap.add_argument(
        "--tex-eq-out",
        type=str,
        default=str(generated_dir() / "eq_foldbin6_bitflip_stability_polynomial.tex"),
        help="Path to generated TeX equation snippet (\\input{}).",
    )
    args = ap.parse_args()

    # Precompute labels for all microstates.
    labels = [_foldbin6_label(n) for n in range(64)]

    # Count stable (W,mask) pairs by mask weight k.
    stable_pairs_by_k: Dict[int, int] = {k: 0 for k in range(7)}
    total_pairs_by_k: Dict[int, int] = {k: 0 for k in range(7)}
    for mask in range(64):
        k = int(mask.bit_count())
        total_pairs_by_k[k] += 64
        for n in range(64):
            if labels[n] == labels[n ^ mask]:
                stable_pairs_by_k[k] += 1

    # Build polynomial P(S) = sum_k (stable_k/64) * p^k * (1-p)^{6-k}.
    coeffs = [Fraction(0) for _ in range(7)]  # p^0..p^6
    for k in range(7):
        stable_k = stable_pairs_by_k[k]
        # term = (stable_k/64) * p^k * sum_{j=0..6-k} C(6-k,j) (-1)^j p^j
        base = Fraction(stable_k, 64)
        term = [Fraction(0) for _ in range(7)]
        for j in range(0, 6 - k + 1):
            deg = k + j
            term[deg] += base * Fraction(comb(6 - k, j), 1) * (Fraction(-1, 1) ** j)
        _poly_add_inplace(coeffs, term)

    # Sanity: P(S)(0)=1, P(S)(1)=Pr[all bits flipped keeps label] in [0,1].
    if coeffs[0] != 1:
        raise RuntimeError(f"Unexpected constant term: {coeffs[0]}")

    payload: Dict[str, object] = {
        "m": 6,
        "domain_size": 64,
        "stable_pairs_by_weight": {str(k): int(v) for k, v in sorted(stable_pairs_by_k.items())},
        "total_pairs_by_weight": {str(k): int(v) for k, v in sorted(total_pairs_by_k.items())},
        "poly_P_S_coeffs_p0_to_p6": [str(c) for c in coeffs],
        "poly_P_U_coeffs_p0_to_p6": [str((Fraction(1) if i == 0 else Fraction(0)) - c) for i, c in enumerate(coeffs)],
    }

    json_out = Path(str(args.json_out))
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # TeX equation snippet.
    tex_out = Path(str(args.tex_eq_out))
    tex_out.parent.mkdir(parents=True, exist_ok=True)

    def _poly_tex(cs: List[Fraction]) -> str:
        def _term_tex(ac: Fraction, deg: int) -> str:
            if deg == 0:
                return _fmt_frac(ac)
            if deg == 1:
                return "p" if ac == 1 else f"{_fmt_frac(ac)}p"
            return f"p^{deg}" if ac == 1 else f"{_fmt_frac(ac)}p^{deg}"

        out = ""
        for deg, c in enumerate(cs):
            if c == 0:
                continue
            sign = "-" if c < 0 else "+"
            ac = -c if c < 0 else c
            term = _term_tex(ac, deg)
            if out == "":
                out = f"- {term}" if sign == "-" else term
            else:
                out += f" {sign} {term}"
        return out if out else "0"

    pS_tex = _poly_tex(coeffs)
    coeffs_U = [(Fraction(1) if i == 0 else Fraction(0)) - c for i, c in enumerate(coeffs)]
    pU_tex = _poly_tex(coeffs_U)

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_foldbin6_bitflip_stability_polynomial.py")
    lines.append("\\begin{equation}\\label{eq:foldbin6_bitflip_stability_polynomial}")
    lines.append("\\begin{aligned}")
    lines.append(f"\\mathbb{{P}}(\\mathcal{{S}})&={pS_tex},\\\\")
    lines.append(f"\\mathbb{{P}}(\\mathcal{{U}})&={pU_tex}.")
    lines.append("\\end{aligned}")
    lines.append("\\end{equation}")
    lines.append("")
    tex_out.write_text("\n".join(lines), encoding="utf-8")

    print(f"File: {json_out.relative_to(export_dir().parent.parent)}")
    print(f"File: {tex_out.relative_to(generated_dir().parent.parent)}")


if __name__ == "__main__":
    main()

