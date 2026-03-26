#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Selection-law scan for the (3,3,p) slow mode with third axis N2 mod p.

We scan primes p and compute:
  rho_{3,3,p} = max_{(j1,j2,j3) != (0,0,0)} rho(M_{j1,j2,j3}),
  gap(p)      = 1 - rho_{3,3,p}/lambda,
  g(p)        = gap(p) * p^2.

This is a fast experiment: it computes spectral radii only (no Mertens constants).

Outputs (default):
  - artifacts/export/arity_335_n2_selection_law_primes.json
  - sections/generated/tab_real_input_40_arity_335_n2_selection_law_primes.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from exp_sync_kernel_real_input_40_arity_3d import (
    build_kernel_edges,
    build_kernel_map,
    build_real_input_states,
    build_weighted_matrix_numeric,
    spectral_radius,
)


@dataclass(frozen=True)
class Row:
    p: int
    rho: float
    rho_ratio: float
    gap: float
    g: float
    kappa_p: float
    argmax: List[Tuple[int, int, int]]


def _parse_int_list_csv(s: str) -> List[int]:
    out: List[int] = []
    for chunk in (x.strip() for x in s.split(",")):
        if not chunk:
            continue
        out.append(int(chunk))
    return out


def _scan_rho_max_for_p(p: int, prog: Progress) -> Row:
    # Fixed (3,3,p) with third axis = N2 mod p.
    m1, m2, m3 = 3, 3, p
    phi = (1.0 + 5.0**0.5) / 2.0
    lam = phi * phi

    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()

    omega1 = np.exp(2j * math.pi / m1)
    omega2 = np.exp(2j * math.pi / m2)
    omega3 = np.exp(2j * math.pi / m3)

    rho_max = -1.0
    argmax: List[Tuple[int, int, int]] = []
    tol = 1e-12

    for j1 in range(m1):
        q = omega1**j1
        for j2 in range(m2):
            r = omega2**j2
            for j3 in range(m3):
                if j1 == 0 and j2 == 0 and j3 == 0:
                    continue
                u = omega3**j3
                M = build_weighted_matrix_numeric(
                    q, r, u, states, kernel_map, third_axis="N2"
                )
                rho = spectral_radius(M)
                if rho > rho_max + tol:
                    rho_max = rho
                    argmax = [(j1, j2, j3)]
                elif abs(rho - rho_max) <= tol:
                    argmax.append((j1, j2, j3))
        prog.tick(f"p={p} scanned j1={j1}/{m1-1}")

    rho_ratio = rho_max / lam
    gap = 1.0 - rho_ratio
    g = gap * float(p * p)
    theta = (2.0 * math.pi) / float(p)
    kappa_p = gap / (theta * theta)
    argmax_sorted = sorted(argmax)
    return Row(
        p=p,
        rho=rho_max,
        rho_ratio=rho_ratio,
        gap=gap,
        g=g,
        kappa_p=kappa_p,
        argmax=argmax_sorted,
    )


def _write_table_tex(path: Path, rows: Sequence[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{选择律扫描：第三轴取 $c=N_2(\\gamma)\\bmod p$ 时 $((3,3,p))$ 的最坏扭曲谱半径比与判别量 "
        "$g(p):=(1-\\rho_{3,3,p}/\\lambda)p^2$。这里 $\\lambda=\\varphi^2$。}"
    )
    lines.append("\\label{tab:real_input_40_arity_335_n2_selection_law_primes}")
    lines.append("\\begin{tabular}{r r r r r r l}")
    lines.append("\\toprule")
    lines.append("$p$ & $\\rho_{3,3,p}$ & $\\rho_{3,3,p}/\\lambda$ & $1-\\rho/\\lambda$ & $g(p)$ & $\\kappa_p$ & argmax $j$\\\\")
    lines.append("\\midrule")
    for row in rows:
        jtxt = ",\\ ".join([f"({a},{b},{c})" for (a, b, c) in row.argmax]) if row.argmax else "-"
        lines.append(
            f"{row.p} & {row.rho:.12f} & {row.rho_ratio:.12f} & {row.gap:.12f} & {row.g:.6f} & {row.kappa_p:.6f} & ${jtxt}$\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Selection-law scan for (3,3,p) with third axis N2 mod p.")
    parser.add_argument(
        "--p-list",
        type=str,
        default="5,7,11,13,17,19,23,29,31",
        help="Comma-separated list of moduli p to scan (typically primes).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "arity_335_n2_selection_law_primes.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_arity_335_n2_selection_law_primes.tex"),
        help="Output LaTeX table path.",
    )
    args = parser.parse_args()

    p_list = _parse_int_list_csv(str(args.p_list))
    if not p_list:
        raise SystemExit("[arity-335-selection-law] empty p-list")
    for p in p_list:
        if p < 2:
            raise SystemExit(f"[arity-335-selection-law] invalid p: {p}")

    prog = Progress("arity-335-selection-law", every_seconds=20.0)
    rows: List[Row] = []
    for p in p_list:
        rows.append(_scan_rho_max_for_p(p, prog))
        prog.tick(f"p={p} done rho_ratio={rows[-1].rho_ratio:.12f}")

    payload: Dict[str, object] = {
        "third_axis": "N2",
        "m1": 3,
        "m2": 3,
        "p_list": p_list,
        "rows": [
            {
                "p": r.p,
                "rho": r.rho,
                "rho_ratio": r.rho_ratio,
                "gap": r.gap,
                "g": r.g,
                "kappa_p": r.kappa_p,
                "argmax": r.argmax,
            }
            for r in rows
        ],
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[arity-335-selection-law] wrote {jout}", flush=True)

    _write_table_tex(Path(args.tex_out), rows)
    print(f"[arity-335-selection-law] wrote {args.tex_out}", flush=True)


if __name__ == "__main__":
    main()

