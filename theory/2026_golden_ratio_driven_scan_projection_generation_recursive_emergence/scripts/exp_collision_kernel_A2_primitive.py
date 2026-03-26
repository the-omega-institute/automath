#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Primitive orbit spectrum for the collision kernel A2.

This script treats the 3-state collision kernel A2 as an SFT adjacency matrix and
computes:
  - trace sequence a_n = Tr(A2^n)
  - primitive orbit counts p_n via Möbius inversion

Outputs (default):
  - artifacts/export/collision_kernel_A2_primitive.json
  - sections/generated/tab_collision_kernel_A2_primitive.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


A2: List[List[int]] = [
    [0, 0, 1],
    [0, 1, 1],
    [2, 1, 1],
]


def matmul3(X: List[List[int]], Y: List[List[int]]) -> List[List[int]]:
    Z = [[0, 0, 0] for _ in range(3)]
    for i in range(3):
        for k in range(3):
            xik = X[i][k]
            if xik == 0:
                continue
            for j in range(3):
                Z[i][j] += xik * Y[k][j]
    return Z


def trace3(X: List[List[int]]) -> int:
    return X[0][0] + X[1][1] + X[2][2]


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
    # Compute powers iteratively.
    cur = [row[:] for row in A2]
    a_n = [0] * (max_n + 1)
    for n in range(1, max_n + 1):
        if n == 1:
            cur = [row[:] for row in A2]
        else:
            cur = matmul3(cur, A2)
        a_n[n] = trace3(cur)
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
        "\\caption{Primitive orbit spectrum for the collision kernel $A_2$ (as an SFT). "
        "Here $a_n=\\mathrm{Tr}(A_2^n)$ and $p_n$ is the number of primitive orbits of length $n$ (by M\\\"obius inversion).}"
    )
    lines.append("\\label{tab:collision_kernel_A2_primitive}")
    lines.append("\\begin{tabular}{r r r}")
    lines.append("\\toprule")
    lines.append("$n$ & $a_n=\\mathrm{Tr}(A_2^n)$ & $p_n(A_2)$\\\\")
    lines.append("\\midrule")
    for n in range(1, max_n + 1):
        lines.append(f"{n} & {a_n[n]} & {p_n[n]}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute primitive spectrum for collision kernel A2.")
    parser.add_argument("--max-n", type=int, default=20, help="Max n for traces/primitives.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_kernel_A2_primitive.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_collision_kernel_A2_primitive.tex"),
        help="Output LaTeX table path.",
    )
    args = parser.parse_args()

    prog = Progress("collision-A2-primitive", every_seconds=20.0)
    spec = traces_and_primitives(args.max_n, prog)

    payload: Dict[str, object] = {
        "A2": A2,
        "max_n": args.max_n,
        "a_n": spec.a_n,
        "p_n": spec.p_n,
    }
    Path(args.json_out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json_out).write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"[collision-A2-primitive] wrote {args.json_out}", flush=True)

    write_table_tex(Path(args.tex_out), args.max_n, spec.a_n, spec.p_n)
    print(f"[collision-A2-primitive] wrote {args.tex_out}", flush=True)


if __name__ == "__main__":
    main()

