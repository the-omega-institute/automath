#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Primitive orbit spectrum for the 4th-collision kernel A4.

This script treats the 5-state kernel A4 as an SFT adjacency matrix and computes:
  - trace sequence a_n = Tr(A4^n)
  - primitive orbit counts p_n via Möbius inversion

Outputs (default):
  - artifacts/export/collision_kernel_A4_primitive.json
  - sections/generated/tab_collision_kernel_A4_primitive.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


A4: List[List[int]] = [
    [0, 1, 0, 0, 0],
    [0, 0, 7, 0, 1],
    [0, 1, 2, 0, 0],
    [1, 0, 1, 0, 0],
    [0, 0, 0, 1, 0],
]


def matmul(X: List[List[int]], Y: List[List[int]]) -> List[List[int]]:
    n = len(X)
    Z = [[0 for _ in range(n)] for __ in range(n)]
    for i in range(n):
        for k in range(n):
            xik = X[i][k]
            if xik == 0:
                continue
            for j in range(n):
                Z[i][j] += xik * Y[k][j]
    return Z


def trace(M: List[List[int]]) -> int:
    return sum(M[i][i] for i in range(len(M)))


def mobius_upto(n: int) -> List[int]:
    mu = [0] * (n + 1)
    mu[0] = 0
    mu[1] = 1
    primes: List[int] = []
    is_comp = [False] * (n + 1)
    for i in range(2, n + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n:
                break
            is_comp[i * p] = True
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def divisors(n: int) -> List[int]:
    ds: List[int] = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            ds.append(i)
            if i * i != n:
                ds.append(n // i)
        i += 1
    return sorted(ds)


@dataclass(frozen=True)
class Spectrum:
    a_n: List[int]  # 1-indexed length max_n+1
    p_n: List[int]  # 1-indexed length max_n+1


def traces_and_primitives(max_n: int, prog: Progress) -> Spectrum:
    cur = [row[:] for row in A4]
    a_n = [0] * (max_n + 1)
    for n in range(1, max_n + 1):
        if n == 1:
            cur = [row[:] for row in A4]
        else:
            cur = matmul(cur, A4)
        a_n[n] = trace(cur)
        prog.tick(f"n={n}/{max_n} trace={a_n[n]}")

    mu = mobius_upto(max_n)
    p_n = [0] * (max_n + 1)
    for n in range(1, max_n + 1):
        s = 0
        for d in divisors(n):
            s += mu[d] * a_n[n // d]
        p_n[n] = s // n
    return Spectrum(a_n=a_n, p_n=p_n)


def write_table_tex(path: Path, max_n: int, a_n: List[int], p_n: List[int]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Primitive orbit spectrum for the 4th-collision kernel $A_4$ (as an SFT). "
        "Here $a_n=\\mathrm{Tr}(A_4^n)$ and $p_n$ is the number of primitive orbits of length $n$ (by M\\\"obius inversion).}"
    )
    lines.append("\\label{tab:collision_kernel_A4_primitive}")
    lines.append("\\begin{tabular}{r r r}")
    lines.append("\\toprule")
    lines.append("$n$ & $a_n=\\mathrm{Tr}(A_4^n)$ & $p_n(A_4)$\\\\")
    lines.append("\\midrule")
    for n in range(1, max_n + 1):
        lines.append(f"{n} & {a_n[n]} & {p_n[n]}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute primitive spectrum for 4th-collision kernel A4.")
    parser.add_argument("--max-n", type=int, default=20, help="Max n for traces/primitives.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_kernel_A4_primitive.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_collision_kernel_A4_primitive.tex"),
        help="Output LaTeX table path.",
    )
    args = parser.parse_args()

    prog = Progress("collision-A4-primitive", every_seconds=20.0)
    spec = traces_and_primitives(args.max_n, prog)

    payload: Dict[str, object] = {
        "A4": A4,
        "max_n": args.max_n,
        "a_n": spec.a_n,
        "p_n": spec.p_n,
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"[collision-A4-primitive] wrote {jout}", flush=True)

    write_table_tex(Path(args.tex_out), args.max_n, spec.a_n, spec.p_n)
    print(f"[collision-A4-primitive] wrote {args.tex_out}", flush=True)


if __name__ == "__main__":
    main()

