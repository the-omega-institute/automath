#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Compute truncated two-variable zeta series coefficients for 9/13/21-local kernels (single-flow).

We work with the weighted adjacency family M_K(u) defined by kappa(e) and compute:
  a_n(u) = Tr(M_K(u)^n) in Z[u]  (exact, by periodic-word enumeration)
  zeta_K(z,u) = exp( sum_{n>=1} a_n(u) z^n / n )

This script outputs the truncated zeta series:
  zeta_K(z,u) = sum_{m=0..N} c_m(u) z^m + O(z^{N+1})
where each c_m(u) is an integer polynomial in u.

Outputs:
- artifacts/export/parallel_addition_kernels_zeta_series.json
- sections/generated/tab_parallel_addition_kernels_zeta_series.tex
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir

import exp_parallel_addition_kernels_bfs as bfs
import exp_parallel_addition_kernels_weighted_primitive as wp


def _write_text(p: Path, s: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(s, encoding="utf-8")


def _poly_mul(a: List[Fraction], b: List[Fraction], deg_max: int) -> List[Fraction]:
    out = [Fraction(0) for _ in range(deg_max + 1)]
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if bj == 0:
                continue
            if i + j > deg_max:
                break
            out[i + j] += ai * bj
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def _poly_scale(a: List[Fraction], s: Fraction) -> List[Fraction]:
    return [ai * s for ai in a]


def _poly_to_int_list(p: List[Fraction]) -> List[int]:
    out: List[int] = []
    for c in p:
        if c.denominator != 1:
            raise RuntimeError(f"non-integer coefficient in zeta series: {c}")
        out.append(int(c.numerator))
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def _zeta_series_from_traces(
    a_polys: Dict[int, List[int]],
    *,
    zeta_n: int,
    deg_cap: int,
) -> Dict[int, List[int]]:
    # Build F(z) = sum_{n=1..zeta_n} f_n(u) z^n with f_n(u)=a_n(u)/n in Q[u]
    f: Dict[int, List[Fraction]] = {0: [Fraction(0)]}
    for n in range(1, zeta_n + 1):
        an = a_polys[n]
        f[n] = [Fraction(c, n) for c in an]

    # exp(F): g0=1; for m>=1: m*g_m = sum_{k=1..m} k*f_k * g_{m-k}
    g: Dict[int, List[Fraction]] = {0: [Fraction(1)]}
    for m in range(1, zeta_n + 1):
        acc = [Fraction(0) for _ in range(deg_cap + 1)]
        for k in range(1, m + 1):
            fk = f.get(k)
            if fk is None:
                continue
            gm_k = g[m - k]
            term = _poly_mul(_poly_scale(fk, Fraction(k)), gm_k, deg_cap)
            for i, ci in enumerate(term):
                acc[i] += ci
        g[m] = _poly_scale(acc, Fraction(1, m))
        while len(g[m]) > 1 and g[m][-1] == 0:
            g[m].pop()

    return {m: _poly_to_int_list(g[m]) for m in range(0, zeta_n + 1)}


def _make_table(rows: List[Dict[str, str]], *, zeta_n: int) -> str:
    lines: List[str] = []
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\scriptsize")
    lines.append(r"\setlength{\tabcolsep}{6pt}")
    lines.append(r"\renewcommand{\arraystretch}{1.15}")
    lines.append(
        rf"\caption{{两变量 $\zeta_K(z,u)$ 的截断级数系数：$\zeta_K(z,u)=\sum_{{m=0}}^{{{zeta_n}}}c_m(u)z^m+O(z^{{{zeta_n+1}}})$（单流，同一 $\kappa$ 加权；由脚本 \texttt{{scripts/exp\_parallel\_addition\_kernels\_zeta\_series.py}} 生成）。}}"
    )
    lines.append(r"\label{tab:parallel-addition-kernels-zeta-series}")
    cols = "l" + ("c" * (zeta_n + 1))
    lines.append(rf"\begin{{tabular}}{{@{{}}{cols}@{{}}}}")
    lines.append(r"\toprule")
    header = ["核"] + [rf"$c_{m}(u)$" for m in range(0, zeta_n + 1)]
    lines.append(" & ".join(header) + r" \\")
    lines.append(r"\midrule")
    for r in rows:
        line = [r["kernel"]] + [r[f"c{m}"] for m in range(0, zeta_n + 1)]
        lines.append(" & ".join(line) + r" \\")
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description="Truncated zeta series coefficients for 9/13/21-local kernels (single-flow)")
    parser.add_argument("--zeta-n", type=int, default=4, help="Truncate zeta series at z^N")
    parser.add_argument("--max-iters", type=int, default=50, help="Max iterations for periodic word fixed-point convergence")
    parser.add_argument("--no-output", action="store_true")
    args = parser.parse_args()

    zeta_n = int(args.zeta_n)
    if zeta_n < 1:
        raise SystemExit("--zeta-n must be >= 1")

    # Degree cap in u for c_m(u): safe cap 3*N (covers our kernels; trims happen naturally in wp._poly_to_latex).
    deg_cap = 3 * zeta_n

    prog = bfs.Progress(label="par-add-zeta-series", every_seconds=20.0)
    print("[par-add-zeta-series] start", flush=True)

    specs = bfs._make_specs(zeta_n)
    payload: Dict[str, object] = {"zeta_n": zeta_n, "kernels": []}
    rows: List[Dict[str, str]] = []

    for sp in specs:
        name_tex = r"$K_{9}$" if "9-local" in sp.name else (r"$K_{13}$" if "13-local" in sp.name else r"$K_{21}$")
        # compute exact traces a_n(u) for n<=zeta_n (polynomials)
        a_polys = wp._trace_polys_by_word_enumeration(sp, zeta_n, max_iters=args.max_iters, prog=prog, label=sp.name)
        c_polys = _zeta_series_from_traces(a_polys, zeta_n=zeta_n, deg_cap=deg_cap)

        payload["kernels"].append(
            {
                "name": sp.name,
                "alphabet_B": sp.alphabet,
                "states_reachable": len(bfs._bfs_states(sp, prog)[0]),
                "a_n_u_poly": {str(n): a_polys[n] for n in range(1, zeta_n + 1)},
                "c_m_u_poly": {str(m): c_polys[m] for m in range(0, zeta_n + 1)},
            }
        )

        row: Dict[str, str] = {"kernel": name_tex}
        for m in range(0, zeta_n + 1):
            row[f"c{m}"] = f"${wp._poly_to_latex(c_polys[m])}$"
        rows.append(row)

    if not args.no_output:
        out_json = export_dir() / "parallel_addition_kernels_zeta_series.json"
        _write_text(out_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"[par-add-zeta-series] wrote {out_json}", flush=True)

        out_tex = generated_dir() / "tab_parallel_addition_kernels_zeta_series.tex"
        _write_text(out_tex, _make_table(rows, zeta_n=zeta_n))
        print(f"[par-add-zeta-series] wrote {out_tex}", flush=True)

    print("[par-add-zeta-series] done", flush=True)


if __name__ == "__main__":
    main()

