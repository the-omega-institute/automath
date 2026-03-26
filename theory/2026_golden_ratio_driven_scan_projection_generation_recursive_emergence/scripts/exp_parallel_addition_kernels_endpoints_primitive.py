#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Endpoint primitive-orbit spectrum for 9/13/21-local kernels (A-route).

Goal: provide a zero-error, closed-form baseline fingerprint table at u=0 and u=1,
for primitive orbit counts p_n up to n=N (single-flow and global).

Endpoint meanings:
- u=0: carry-free skeleton (kappa=0 edges only). For the three kernels this is:
    K9: full shift with m=7
    K13: full shift with m=3
    K21: golden-mean shift with adjacency G=[[1,1],[1,0]] (Lucas traces)
- u=1: ignore kappa weighting; in our single-flow compilation Tr(M(1)^n)=|B|^n,
       hence primitive counts are the full shift with m=|B|:
    K9: m=21, K13: m=13, K21: m=5

Global (block-level) assembly:
- K9 has 4 congruence streams (m_flow=4), so full-shift size becomes m^4.
- K13, K21 have 2 streams, so full-shift size becomes m^2.
- For K21 carry-free global is golden-mean × golden-mean: traces L_n^2.

Outputs:
- sections/generated/tab_parallel_addition_kernels_endpoint_primitive.tex
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import generated_dir


def _write_text(p: Path, s: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(s, encoding="utf-8")


def _mobius(n: int) -> int:
    if n == 1:
        return 1
    x = n
    mu = 1
    p = 2
    while p * p <= x:
        if x % p == 0:
            x //= p
            mu = -mu
            if x % p == 0:
                return 0
            while x % p == 0:
                x //= p
        p += 1 if p == 2 else 2
    if x > 1:
        mu = -mu
    return mu


def _divisors(n: int) -> List[int]:
    ds: List[int] = []
    d = 1
    while d * d <= n:
        if n % d == 0:
            ds.append(d)
            if d * d != n:
                ds.append(n // d)
        d += 1
    return sorted(ds)


def _primitive_from_traces(traces: List[int]) -> List[int]:
    # traces[k-1] = a_k = Tr(A^k)
    out: List[int] = []
    for n in range(1, len(traces) + 1):
        s = 0
        for d in _divisors(n):
            mu = _mobius(d)
            if mu == 0:
                continue
            s += mu * traces[n // d - 1]
        if s % n != 0:
            raise RuntimeError(f"non-integer primitive at n={n}: {s}/{n}")
        out.append(s // n)
    return out


def _traces_full_shift(m: int, n_max: int) -> List[int]:
    return [m**n for n in range(1, n_max + 1)]


def _traces_golden_mean(n_max: int) -> List[int]:
    # Lucas-like traces L_n = Tr(G^n) for G=[[1,1],[1,0]]:
    # L_1=1, L_2=3, L_{n}=L_{n-1}+L_{n-2}.
    if n_max <= 0:
        return []
    if n_max == 1:
        return [1]
    L = [1, 3]
    while len(L) < n_max:
        L.append(L[-1] + L[-2])
    return L[:n_max]


def _fmt_seq(xs: List[int]) -> str:
    return "(" + ",".join(str(x) for x in xs) + ")"


def _make_table(rows: List[Dict[str, str]], *, n_max: int) -> str:
    lines: List[str] = []
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\scriptsize")
    lines.append(r"\setlength{\tabcolsep}{4pt}")
    lines.append(r"\renewcommand{\arraystretch}{1.12}")
    lines.append(
        rf"\caption{{端点谱表（闭式零误差）：三核在 $u=0$（carry-free 骨架）与 $u=1$（无权 full shift）处的 primitive 轨道数 $p_n$，给到 $n\le {n_max}$。单流与全局块级均由闭式 Möbius 反演得到（脚本 \texttt{{scripts/exp\_parallel\_addition\_kernels\_endpoints\_primitive.py}} 生成）。}}"
    )
    lines.append(r"\label{tab:parallel-addition-kernels-endpoint-primitive}")
    lines.append(r"\resizebox{\textwidth}{!}{%")
    lines.append(r"\begin{tabular}{@{}lcccc@{}}")
    lines.append(r"\toprule")
    lines.append(r"核 & 端点 & 单流 $p_n$（$n\le 20$） & 全局块级（流数 $m$） & 全局 $p_n$（$n\le 20$） \\")
    lines.append(r"\midrule")
    for r in rows:
        lines.append(" & ".join([r["kernel"], r["endpoint"], r["flow_seq"], r["glob_desc"], r["glob_seq"]]) + r" \\")
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"}")
    lines.append(r"\end{table}")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description="Endpoint primitive-orbit spectrum table for 9/13/21-local kernels")
    parser.add_argument("--nmax", type=int, default=20, help="Max n for primitive counts")
    parser.add_argument("--no-output", action="store_true")
    args = parser.parse_args()

    n_max = int(args.nmax)
    if n_max < 1:
        raise SystemExit("--nmax must be >= 1")

    # Kernel endpoint parameters (single-flow).
    # u=0:
    #  - K9: full shift size 7
    #  - K13: full shift size 3
    #  - K21: golden mean (Lucas traces)
    # u=1:
    #  - K9: full shift size 21
    #  - K13: full shift size 13
    #  - K21: full shift size 5
    configs: List[Tuple[str, str, List[int], str, List[int]]] = []

    # K9
    configs.append((r"$K_{9}$", r"$u=0$", _primitive_from_traces(_traces_full_shift(7, n_max)), r"$m=4,\ 7^4=2401$", _primitive_from_traces(_traces_full_shift(2401, n_max))))
    configs.append((r"$K_{9}$", r"$u=1$", _primitive_from_traces(_traces_full_shift(21, n_max)), r"$m=4,\ 21^4=194481$", _primitive_from_traces(_traces_full_shift(194481, n_max))))

    # K13
    configs.append((r"$K_{13}$", r"$u=0$", _primitive_from_traces(_traces_full_shift(3, n_max)), r"$m=2,\ 3^2=9$", _primitive_from_traces(_traces_full_shift(9, n_max))))
    configs.append((r"$K_{13}$", r"$u=1$", _primitive_from_traces(_traces_full_shift(13, n_max)), r"$m=2,\ 13^2=169$", _primitive_from_traces(_traces_full_shift(169, n_max))))

    # K21
    L = _traces_golden_mean(n_max)
    configs.append((r"$K_{21}$", r"$u=0$", _primitive_from_traces(L), r"$m=2,\ \mathrm{GM}\times\mathrm{GM}$", _primitive_from_traces([t * t for t in L])))
    configs.append((r"$K_{21}$", r"$u=1$", _primitive_from_traces(_traces_full_shift(5, n_max)), r"$m=2,\ 5^2=25$", _primitive_from_traces(_traces_full_shift(25, n_max))))

    rows: List[Dict[str, str]] = []
    for kernel, endpoint, flow_p, glob_desc, glob_p in configs:
        rows.append(
            {
                "kernel": kernel,
                "endpoint": endpoint,
                "flow_seq": f"${_fmt_seq(flow_p)}$",
                "glob_desc": glob_desc,
                "glob_seq": f"${_fmt_seq(glob_p)}$",
            }
        )

    if args.no_output:
        return

    out_tex = generated_dir() / "tab_parallel_addition_kernels_endpoint_primitive.tex"
    _write_text(out_tex, _make_table(rows, n_max=n_max))
    print(f"[par-add-endpoints] wrote {out_tex}", flush=True)


if __name__ == "__main__":
    main()

