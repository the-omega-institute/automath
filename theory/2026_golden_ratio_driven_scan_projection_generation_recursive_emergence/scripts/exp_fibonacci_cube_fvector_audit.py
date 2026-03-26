#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Fibonacci-cube f-vector audit (recurrence / generating function / coefficient formula).

We work with the Fibonacci cube Γ_n: vertices are length-n 0/1 words with no adjacent 11,
edges are single-bit flips staying legal. Let C(n,k) be the number of k-dimensional
subcubes in Γ_n (k=0 vertices, k=1 edges). Define C_n(u)=Σ_k C(n,k) u^k.

This script:
  - computes C(n,k) via the (n,k)-recurrence,
  - cross-checks it against the closed-form coefficient formula,
  - emits small TeX snippets and a small-n f-vector table for the paper.

Outputs:
  - artifacts/export/fibonacci_cube_fvector_audit.json
  - sections/generated/eq_fibonacci_cube_bivariate_gf.tex
  - sections/generated/eq_fibonacci_cube_coeff_formula.tex
  - sections/generated/tab_fibonacci_cube_fvector_small_n.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from math import comb
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir


def _kmax_for_n(n: int) -> int:
    # Maximum number of independently flippable 1-bits is the maximum independent set size
    # in P_n, i.e. ceil(n/2).
    return (n + 1) // 2


def compute_C_dp(n_max: int) -> List[List[int]]:
    """Return dp[n][k] = C(n,k) for 0<=n<=n_max, 0<=k<=ceil(n_max/2)."""
    n_max = int(n_max)
    if n_max < 0:
        raise ValueError("n_max must be >= 0")
    k_max = _kmax_for_n(n_max)
    dp: List[List[int]] = [[0 for _ in range(k_max + 1)] for _ in range(n_max + 1)]

    # Initial conditions.
    dp[0][0] = 1
    if n_max >= 1:
        dp[1][0] = 2
        dp[1][1] = 1

    for n in range(2, n_max + 1):
        for k in range(0, _kmax_for_n(n) + 1):
            a = dp[n - 1][k] if k <= _kmax_for_n(n - 1) else 0
            b = dp[n - 2][k] if k <= _kmax_for_n(n - 2) else 0
            c = dp[n - 2][k - 1] if (k - 1) >= 0 and (k - 1) <= _kmax_for_n(n - 2) else 0
            dp[n][k] = int(a + b + c)
    return dp


def C_closed(n: int, k: int) -> int:
    """Closed-form coefficient formula for C(n,k)."""
    n = int(n)
    k = int(k)
    if n < 0 or k < 0:
        return 0
    # For Γ_n, the largest cube dimension is ceil(n/2).
    if k > _kmax_for_n(n):
        return 0
    out = 0
    # Note: the summation upper limit is ceil(n/2) = floor((n+1)/2).
    for j in range(k, ((n + 1) // 2) + 1):
        out += comb(n - j + 1, j) * comb(j, k)
    return int(out)


@dataclass(frozen=True)
class Row:
    n: int
    C: List[int]  # C(n,0..k_max)

    def to_dict(self) -> Dict[str, object]:
        return {"n": int(self.n), "C": [int(x) for x in self.C]}


def write_eq_bivariate_gf(path: Path) -> None:
    # Keep as a single display equation so it can be \input inside a theorem.
    tex = r"""\[
\sum_{n\ge 0} C_n(u)\,z^n\;=\;\frac{1+z(1+u)}{1-z-(1+u)z^2}.
\]
"""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(tex, encoding="utf-8")


def write_eq_coeff_formula(path: Path) -> None:
    tex = r"""\[
C(n,k)=\sum_{j=k}^{\lceil n/2\rceil}\binom{n-j+1}{j}\binom{j}{k}.
\]
"""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(tex, encoding="utf-8")


def write_table_small_n(rows: List[Row], n_max: int, out_path: Path) -> None:
    # Fix columns up to k_max(n_max) and fill with 0 beyond the per-row k_max.
    k_max = _kmax_for_n(int(n_max))
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append(
        (
            "\\caption{Fibonacci cube $\\Gamma_n$ 的 $f$-向量（立方面计数）在小 $n$ 上的可核验表。"
            "这里 $C(n,k)$ 为 $\\Gamma_n$ 中的 $k$-维子立方体个数（定义~\\ref{def:pom-fibcube-fvector}）。}"
        )
    )
    lines.append("\\label{tab:fibonacci_cube_fvector_small_n}")
    col_spec = "r" + (" r" * (k_max + 1))
    lines.append(f"\\begin{{tabular}}{{{col_spec}}}")
    lines.append("\\toprule")
    header = ["$n$"] + [f"$C(n,{k})$" for k in range(0, k_max + 1)]
    lines.append(" & ".join(header) + "\\\\")
    lines.append("\\midrule")
    for r in rows:
        row_vals = [str(r.n)] + [str(int(r.C[k]) if k < len(r.C) else 0) for k in range(0, k_max + 1)]
        lines.append(" & ".join(row_vals) + "\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Audit the Fibonacci-cube f-vector identities and emit TeX snippets.")
    ap.add_argument("--n-max", type=int, default=12, help="Max n for the small-n table and audits.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fibonacci_cube_fvector_audit.json"),
    )
    return ap.parse_args()


def main() -> None:
    args = parse_args()
    n_max = int(args.n_max)
    if n_max < 0:
        raise SystemExit("Require --n-max >= 0")

    dp = compute_C_dp(n_max)

    # Cross-check against the closed form.
    for n in range(0, n_max + 1):
        for k in range(0, _kmax_for_n(n) + 1):
            want = int(dp[n][k])
            got = int(C_closed(n, k))
            if want != got:
                raise AssertionError(f"C(n,k) mismatch at n={n} k={k}: dp={want} closed={got}")

    rows: List[Row] = []
    for n in range(0, n_max + 1):
        km = _kmax_for_n(n)
        rows.append(Row(n=n, C=[int(dp[n][k]) for k in range(0, km + 1)]))

    payload: Dict[str, object] = {
        "params": {
            "n_max": n_max,
            "definition": {
                "C(n,k)": "number of k-cubes in the Fibonacci cube Γ_n",
                "C_n(u)": "Σ_k C(n,k) u^k",
                "k_max(n)": "ceil(n/2)",
            },
            "identities": {
                "recurrence": "C(n,k)=C(n-1,k)+C(n-2,k)+C(n-2,k-1) for n>=2",
                "gf": "Σ_{n>=0} C_n(u) z^n = (1+z(1+u))/(1-z-(1+u)z^2)",
                "closed_form": "C(n,k)=Σ_{j=k..ceil(n/2)} binom(n-j+1,j) binom(j,k)",
            },
        },
        "rows": [r.to_dict() for r in rows],
    }

    json_out = Path(args.json_out)
    if not json_out.is_absolute():
        json_out = Path.cwd() / json_out
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    write_eq_bivariate_gf(generated_dir() / "eq_fibonacci_cube_bivariate_gf.tex")
    write_eq_coeff_formula(generated_dir() / "eq_fibonacci_cube_coeff_formula.tex")
    write_table_small_n(rows, n_max=n_max, out_path=(generated_dir() / "tab_fibonacci_cube_fvector_small_n.tex"))


if __name__ == "__main__":
    main()

