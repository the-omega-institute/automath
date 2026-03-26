#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: Fold^{bin}_6 information-loss constants (bits).

All output is English-only by repository convention.

We work with the dyadic (binary-interval) fold at m=6:
  Fold^{bin}_6 : {0,...,63} -> X_6,
defined by Zeckendorf digits (c_k) in Fibonacci weights N = sum_{k>=1} c_k F_{k+1}
and the prefix truncation pi_6(c_1,...)= (c_1,...,c_6).

For U ~ Unif({0,...,63}), let W := Fold^{bin}_6(U). Then
  P(W=w) = d^{bin}_6(w)/64,  where d^{bin}_6(w) := |Fold^{bin}_6{}^{-1}(w)|.

We certify (in base-2 / bits):
  - the fiber histogram (d : #{w in X_6}),
  - the hidden-bit constant  E[log2 d^{bin}_6(W)],
  - the output entropy        H_2(W),
  - the gap / KL-to-uniform   D_KL^{(2)}(P_W || Unif(X_6)) = log2|X_6| - H_2(W).

Outputs:
  - artifacts/export/foldbin6_information_loss_constants.json
  - sections/generated/eq_foldbin6_information_loss_constants.tex
"""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import fib_upto, word_to_str, zeckendorf_digits


def _K_of_limit(limit: int) -> int:
    """Unique K with F_{K+1} <= limit < F_{K+2} (F_1=F_2=1)."""
    if limit < 0:
        raise ValueError("limit must be non-negative")
    fib = [1, 1]
    while fib[-1] <= limit:
        fib.append(fib[-1] + fib[-2])
    # Now fib[-2] <= limit < fib[-1] and fib[-2] = F_{K+1} with K+2 = len(fib).
    return len(fib) - 2


def _fold_bin_prefix_word(N: int, m: int) -> str:
    """Compute Fold^{bin}_m(N) = prefix_m(Zeckendorf(N)) as an m-bit string."""
    limit = (1 << m) - 1
    if not (0 <= N <= limit):
        raise ValueError(f"N must be in [0,{limit}] for m={m}")
    K = _K_of_limit(limit)
    digits = zeckendorf_digits(N, K)  # c_1..c_K
    return word_to_str(digits[:m])


def _format_fraction(fr: Fraction) -> str:
    if fr.denominator == 1:
        return str(fr.numerator)
    return f"\\frac{{{fr.numerator}}}{{{fr.denominator}}}"


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit Fold^{bin}_6 information-loss constants (bits).")
    ap.add_argument("--m", type=int, default=6, help="Window size (default 6).")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "foldbin6_information_loss_constants.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_foldbin6_information_loss_constants.tex"),
    )
    args = ap.parse_args()

    m = int(args.m)
    if m != 6:
        raise ValueError("This certificate is anchored at m=6 (use m=6).")

    domain = list(range(0, (1 << m)))
    fibers: Dict[str, List[int]] = defaultdict(list)
    for N in domain:
        w = _fold_bin_prefix_word(N, m)
        fibers[w].append(N)

    X_size = len(fibers)
    if X_size != 21:
        raise RuntimeError(f"Unexpected |X_6|={X_size}; expected 21.")

    fiber_sizes = {w: len(pre) for w, pre in fibers.items()}
    hist = Counter(fiber_sizes.values())  # d -> #{w}

    # Convert to the (d : total microstates weight) histogram: sum_w d(w) = 2^m.
    weight_sum: Dict[int, int] = {d: int(d) * int(cnt) for d, cnt in hist.items()}
    if sum(weight_sum.values()) != (1 << m):
        raise RuntimeError("Weight histogram does not sum to 2^m.")

    # Compute bits constants numerically.
    E_log2_d = 0.0
    for d, wsum in sorted(weight_sum.items()):
        E_log2_d += (wsum / (1 << m)) * math.log2(d)
    H2_W = float(m) - E_log2_d
    KL2_to_unif = math.log2(X_size) - H2_W

    # Closed form for the audited m=6 histogram: d in {2,3,4}.
    expected_hist = {2: 8, 3: 4, 4: 9}
    if dict(hist) != expected_hist:
        raise RuntimeError(f"Unexpected audited histogram at m=6: {dict(hist)} vs {expected_hist}")

    w2 = weight_sum[2]  # 2*8 = 16
    w3 = weight_sum[3]  # 3*4 = 12
    w4 = weight_sum[4]  # 4*9 = 36
    denom = 1 << m
    rat_part = Fraction(w2 + 2 * w4, denom)  # log2(2)=1, log2(4)=2
    coef_log2_3 = Fraction(w3, denom)

    E_log2_d_tex = f"{_format_fraction(rat_part)}+{_format_fraction(coef_log2_3)}\\log_2 3"
    H2_rat_part = Fraction(m, 1) - rat_part
    H2_W_tex = f"{_format_fraction(H2_rat_part)}-{_format_fraction(coef_log2_3)}\\log_2 3"
    KL2_tex = f"\\log_2|X_6|-{_format_fraction(H2_rat_part)}+{_format_fraction(coef_log2_3)}\\log_2 3"

    payload = {
        "m": m,
        "domain_size": 1 << m,
        "X_size": X_size,
        "fiber_histogram_d_to_count": {str(d): int(c) for d, c in sorted(hist.items())},
        "fiber_weight_histogram_d_to_total_microstates": {str(d): int(wsum) for d, wsum in sorted(weight_sum.items())},
        "E_log2_d_exact_tex": E_log2_d_tex,
        "E_log2_d_bits": E_log2_d,
        "H2_W_exact_tex": H2_W_tex,
        "H2_W_bits": H2_W,
        "KL2_to_unif_exact_tex": KL2_tex,
        "KL2_to_unif_bits": KL2_to_unif,
    }

    json_out = Path(str(args.json_out))
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    tex_out = Path(str(args.tex_out))
    tex_out.parent.mkdir(parents=True, exist_ok=True)

    hist_tex = ",\\ ".join([f"{d}:{c}" for d, c in sorted(hist.items())])
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_foldbin6_information_loss_constants.py")
    lines.append("\\begin{equation}\\label{eq:foldbin6_information_loss_constants}")
    lines.append("\\begin{aligned}")
    lines.append(f"\\#\\{{d^{{\\mathrm{{bin}}}}_6=d\\}}&:\\quad {hist_tex},\\\\")
    lines.append(
        "\\mathbb{E}[\\log_2 d^{\\mathrm{bin}}_6(W)]"
        f"&= {E_log2_d_tex}"
        f"\\ \\approx\\ {E_log2_d:.6f}\\ \\text{{bits}},\\\\"
    )
    lines.append(
        "\\qquad H_2(W)"
        f"&= {H2_W_tex}"
        f"\\ \\approx\\ {H2_W:.6f}\\ \\text{{bits}},\\\\"
    )
    lines.append(
        "D^{(2)}_{\\mathrm{KL}}(P_W\\Vert \\mathrm{Unif}(X_6))"
        f"&= \\log_2|X_6|-H_2(W)"
        f"\\ \\approx\\ {KL2_to_unif:.6f}\\ \\text{{bits}}."
    )
    lines.append("\\end{aligned}")
    lines.append("\\end{equation}")
    lines.append("")
    tex_out.write_text("\n".join(lines), encoding="utf-8")

    print(f"File: {json_out.relative_to(json_out.parents[2])}")
    print(f"File: {tex_out.relative_to(tex_out.parents[2])}")


if __name__ == "__main__":
    main()

