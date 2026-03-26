#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Fibonacci-prime resolution windows for finite-resolution arithmetic.

Outputs:
- artifacts/export/fib_prime_resolution_windows.json
- sections/generated/tab_fib_prime_resolution_windows.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import List

from sympy import isprime

from common_paths import export_dir, generated_dir
from common_phi_fold import PHI, fib_upto


@dataclass(frozen=True)
class Row:
    m: int
    p: int  # p = F_{m+2}, required prime for the "field phase"
    eps: float  # epsilon_m = phi^{-m}


def _format_sci_tex(x: float, sig: int = 4) -> str:
    """Format a positive float in TeX scientific notation."""
    if x == 0.0:
        return "0"
    if x < 0.0:
        raise ValueError("x must be non-negative")
    s = f"{x:.{sig}e}"  # e.g. 4.0900e-05
    mantissa, exp = s.split("e")
    exp_i = int(exp)
    # Strip trailing zeros in mantissa, keep at least one decimal place.
    mantissa = mantissa.rstrip("0").rstrip(".")
    # TeX command is \times; write a single backslash to the output file.
    return f"{mantissa}\\times 10^{{{exp_i}}}"


def write_table(rows: List[Row], m_min: int, m_max: int, out_path: Path) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        (
            "\\caption{Fibonacci-prime 分辨率窗口：当 $p=F_{m+2}$ 为素数时，"
            "$(X_m,\\boxplus_m,\\boxtimes_m)\\cong \\mathbb{F}_p$ 为有限域（推论~\\ref{cor:field-phase-fib-prime}）。"
            "这里列出区间 $m\\in[%d,%d]$ 内的全部此类窗口，并给出尺度 $\\varepsilon_m=\\varphi^{-m}$ 的数值。}"
        )
        % (m_min, m_max)
    )
    lines.append("\\label{tab:fib_prime_resolution_windows}")
    lines.append("\\begin{tabular}{r r r}")
    lines.append("\\toprule")
    lines.append("$m$ & $p=F_{m+2}$ & $\\varepsilon_m=\\varphi^{-m}$ (approx)\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(f"{r.m} & {r.p} & ${_format_sci_tex(r.eps)}$\\\\")
    if not rows:
        lines.append("\\multicolumn{3}{c}{(no Fibonacci-prime windows in this range)}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m-min", type=int, default=6)
    parser.add_argument("--m-max", type=int, default=40)
    parser.add_argument(
        "--output",
        type=str,
        default="artifacts/export/fib_prime_resolution_windows.json",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    m_min = int(args.m_min)
    m_max = int(args.m_max)
    if m_min < 1 or m_max < m_min:
        raise ValueError("Require 1 <= m_min <= m_max")

    # Need Fibonacci numbers up to F_{m_max+2}.
    fib = fib_upto(m_max + 2)

    rows: List[Row] = []
    for m in range(m_min, m_max + 1):
        p = fib[m + 1]  # F_{m+2} with 1-indexed fib, 0-indexed list.
        if isprime(p):
            eps = PHI ** (-m)
            rows.append(Row(m=m, p=int(p), eps=float(eps)))

    payload = {
        "params": {
            "m_min": m_min,
            "m_max": m_max,
            "phi": PHI,
            "definition": {"p": "F_{m+2}", "epsilon_m": "phi^{-m}"},
        },
        "rows": [{"m": r.m, "p": r.p, "epsilon_m": r.eps} for r in rows],
    }

    out_path = Path(args.output)
    if not out_path.is_absolute():
        out_path = Path.cwd() / out_path
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    table_path = generated_dir() / "tab_fib_prime_resolution_windows.tex"
    write_table(rows, m_min, m_max, table_path)


if __name__ == "__main__":
    main()

