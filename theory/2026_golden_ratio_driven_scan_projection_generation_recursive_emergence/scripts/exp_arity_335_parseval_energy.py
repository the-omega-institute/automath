#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Parseval energy diagnostics for the ((3,3,5)) Dirichlet–Mertens constants tensor (third axis N2 mod 5).

Goal: compress the centered constants tensor into a single auditable scalar and connect it
to character-channel strengths.

We parse the reproducible TeX output:
  sections/generated/tab_real_input_40_arity_dirichlet_mertens_335_N2.tex
to recover the 3x3x5 tensor C_{a,b,c} (a=chi mod 3, b=N_- mod 3, c=N2 mod 5).

Define:
  M := sum_{a,b,c} C_{a,b,c},
  C~ := C - M/45,
  B := sum_{a,b,c} (C~_{a,b,c})^2.

Let G = (Z/3)^2 x (Z/5), |G|=45, and define the unnormalized DFT:
  C_hat(j) := sum_{a,b,c} C~_{a,b,c} * w3^{j1 a + j2 b} * w5^{j3 c}.
Then Parseval gives the exact identity (up to floating error):
  B = (1/45) * sum_{j in G} |C_hat(j)|^2.

We also compute the twisted spectral ratios rho(j)/lambda on the same character grid
and report how much of the energy is captured by the slowest (largest rho(j)) channels.

Outputs (default):
  - artifacts/export/arity_335_parseval_energy.json
  - sections/generated/eq_arity_335_parseval_energy.tex
  - sections/generated/tab_arity_335_slow_modes_energy_head.tex

All stdout is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir, paper_root
from exp_sync_kernel_real_input_40_arity_3d import (
    build_kernel_edges,
    build_kernel_map,
    build_real_input_states,
    build_weighted_matrix_numeric,
    spectral_radius,
)


def _read_text(rel_or_abs: str) -> str:
    p = Path(rel_or_abs)
    if p.is_absolute():
        return p.read_text(encoding="utf-8")
    return (paper_root() / rel_or_abs).read_text(encoding="utf-8")


def _parse_tensor_from_tex(tex: str) -> np.ndarray:
    """Parse the 3x3x5 tensor from the generated TeX snippet.

    Convention (as stated in the TeX):
      - slice index: c in {0..4}
      - matrix rows: b in {0,1,2}
      - matrix cols: a in {0,1,2}
      entry(row=b, col=a) = C_{a,b,c}.
    """
    T = np.zeros((3, 3, 5), dtype=float)  # [a,b,c]
    lines = tex.splitlines()
    i = 0
    num_re = re.compile(r"[-+]?\d+(?:\.\d+)?(?:[eE][-+]?\d+)?")
    while i < len(lines):
        line = lines[i].strip()
        if line.startswith("c=") and ":\\quad" in line:
            # "c=0:\quad"
            m = re.match(r"c=(\d+):\\\\quad", line.replace(" ", ""))
            if not m:
                # fallback: just extract first integer after c=
                m2 = re.search(r"c\s*=\s*(\d+)", line)
                if not m2:
                    i += 1
                    continue
                c = int(m2.group(1))
            else:
                c = int(m.group(1))
            # advance to \begin{pmatrix}
            while i < len(lines) and "\\begin{pmatrix}" not in lines[i]:
                i += 1
            if i >= len(lines):
                break
            i += 1  # first row line
            for b in range(3):
                if i >= len(lines):
                    raise RuntimeError("unexpected EOF while parsing pmatrix rows")
                row = lines[i]
                row = row.replace("\\phantom{-}", "")
                nums = [float(x) for x in num_re.findall(row)]
                if len(nums) != 3:
                    raise RuntimeError(f"bad row parse for c={c}, b={b}: got {nums!r}")
                for a in range(3):
                    T[a, b, c] = nums[a]
                i += 1
            # advance past \end{pmatrix}
            while i < len(lines) and "\\end{pmatrix}" not in lines[i]:
                i += 1
        i += 1
    return T


def _w(n: int, k: int) -> complex:
    return complex(math.cos(2.0 * math.pi * k / n), math.sin(2.0 * math.pi * k / n))


@dataclass(frozen=True)
class ModeRow:
    j1: int
    j2: int
    j3: int
    rho_over_lam: float
    energy: float
    energy_frac: float
    energy_cum: float


def _support_size(j: Tuple[int, int, int]) -> int:
    return int((j[0] != 0) + (j[1] != 0) + (j[2] != 0))


def main() -> None:
    parser = argparse.ArgumentParser(description="Parseval energy diagnostics for ((3,3,5)) constants tensor (N2 axis).")
    parser.add_argument(
        "--in-tex",
        type=str,
        default="sections/generated/tab_real_input_40_arity_dirichlet_mertens_335_N2.tex",
        help="Input TeX snippet path (relative to paper root unless absolute).",
    )
    parser.add_argument("--head", type=int, default=12, help="Number of slow modes to report in the LaTeX head table.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "arity_335_parseval_energy.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--eq-tex-out",
        type=str,
        default=str(generated_dir() / "eq_arity_335_parseval_energy.tex"),
        help="Output LaTeX equation snippet path.",
    )
    parser.add_argument(
        "--table-tex-out",
        type=str,
        default=str(generated_dir() / "tab_arity_335_slow_modes_energy_head.tex"),
        help="Output LaTeX table path for slow-mode head.",
    )
    args = parser.parse_args()

    tex = _read_text(str(args.in_tex))
    C = _parse_tensor_from_tex(tex)  # shape (3,3,5) with indices [a,b,c]

    M_total = float(np.sum(C))
    mean = M_total / 45.0
    Cc = C - mean
    B = float(np.sum(Cc * Cc))

    # DFT over G = (Z/3)^2 x (Z/5), unnormalized.
    w3 = _w(3, 1)
    w5 = _w(5, 1)
    modes: Dict[Tuple[int, int, int], complex] = {}
    for j1 in range(3):
        for j2 in range(3):
            for j3 in range(5):
                s = 0.0 + 0.0j
                for a in range(3):
                    for b in range(3):
                        for c in range(5):
                            s += complex(Cc[a, b, c]) * (w3 ** (j1 * a + j2 * b)) * (w5 ** (j3 * c))
                modes[(j1, j2, j3)] = s
    energies = {j: float(abs(z) ** 2) for j, z in modes.items()}
    E_total = float(sum(energies.values()))
    parseval_rel_err = abs(B - (E_total / 45.0)) / max(1e-300, B)

    # Compute twisted spectral ratios rho(j)/lambda on the same grid.
    phi = (1.0 + 5.0**0.5) / 2.0
    lam = phi * phi
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()
    omega3 = np.exp(2j * math.pi / 3)
    omega5 = np.exp(2j * math.pi / 5)
    rho_ratio: Dict[Tuple[int, int, int], float] = {}
    for j1 in range(3):
        q = omega3**j1
        for j2 in range(3):
            r = omega3**j2
            for j3 in range(5):
                u = omega5**j3
                Mj = build_weighted_matrix_numeric(q, r, u, states, kernel_map, third_axis="N2")
                rho = spectral_radius(Mj)
                rho_ratio[(j1, j2, j3)] = float(rho / lam)

    # Sort nontrivial modes by slowest rho_ratio (descending), report head.
    items = []
    for j, e in energies.items():
        if j == (0, 0, 0):
            continue
        items.append((rho_ratio[j], e, j))
    items.sort(reverse=True, key=lambda t: (t[0], t[1], t[2]))

    head_n = int(args.head)
    rows: List[ModeRow] = []
    cum = 0.0
    for rr, e, (j1, j2, j3) in items[:head_n]:
        frac = (e / E_total) if E_total > 0 else 0.0
        cum += frac
        rows.append(
            ModeRow(
                j1=int(j1),
                j2=int(j2),
                j3=int(j3),
                rho_over_lam=float(rr),
                energy=float(e),
                energy_frac=float(frac),
                energy_cum=float(cum),
            )
        )

    # Energy captured by the top-K slow modes.
    def energy_frac_topk_slowest(k: int) -> float:
        s = 0.0
        for _rr, e, _j in items[:k]:
            s += e
        return float(s / E_total) if E_total > 0 else 0.0

    topk = [2, 4, 6, 10, 12]
    topk_energy = {str(k): energy_frac_topk_slowest(k) for k in topk}

    # Energy carried by pure collision modes (j1=j2=0, j3!=0).
    pure_collision_energy = float(sum(energies[(0, 0, j3)] for j3 in range(1, 5)) / E_total) if E_total > 0 else 0.0

    payload: Dict[str, object] = {
        "tensor": "3x3x5",
        "third_axis": "N2",
        "M_total": M_total,
        "mean_M_over_45": mean,
        "B_sum_sq_centered": B,
        "E_total_hat": E_total,
        "parseval": {"rel_err": parseval_rel_err},
        "topk_energy_frac_by_slowest_rho": topk_energy,
        "pure_collision_energy_frac": pure_collision_energy,
        "slow_mode_head": [asdict(r) for r in rows],
    }

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[arity-335-parseval] wrote {jout}", flush=True)

    # LaTeX equation snippet.
    eq = Path(args.eq_tex_out)
    eq.parent.mkdir(parents=True, exist_ok=True)
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_arity_335_parseval_energy.py")
    lines.append("\\paragraph{Parseval 能量：常数张量偏差的单标量指纹（可复现）}")
    lines.append("令 $G=(\\mathbb{Z}/3)^2\\times(\\mathbb{Z}/5)$ 且 $|G|=45$，并记中心化张量 $\\widetilde C:=C-\\mathsf{M}/45$。定义偏差能量")
    lines.append("\\[")
    lines.append(
        rf"\mathcal{{B}}:=\sum_{{(a,b,c)\in G}}\bigl(\widetilde C_{{a,b,c}}\bigr)^2\approx {B:.12g}."
    )
    lines.append("\\]")
    lines.append("对 $\\widetilde C$ 作未归一化离散傅里叶变换 $\\widehat{\\widetilde C}(j)$，则 Parseval 恒等式给出严格等式（数值相对误差为 "
                 f"${parseval_rel_err:.2e}$）：")
    lines.append("\\[")
    lines.append(
        "\\boxed{\\ \\mathcal{B}=\\frac{1}{45}\\sum_{j\\in G}\\left|\\widehat{\\widetilde C}(j)\\right|^2\\ }."
    )
    lines.append("\\]")
    lines.append(
        "把角色通道按最坏谱比 $\\rho(j)/\\lambda$ 从大到小排序后，前 $K$ 个最慢通道解释的能量占比分别为："
    )
    lines.append("\\[")
    lines.append(
        ",\\ ".join([rf"K={k}:\ {topk_energy[str(k)]:.6f}" for k in topk]) + "."
    )
    lines.append("\\]")
    lines.append(
        f"其中纯碰撞通道（$j_1=j_2=0,\\,j_3\\ne 0$）的总能量占比为 ${pure_collision_energy:.6f}$。"
    )
    eq.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[arity-335-parseval] wrote {eq}", flush=True)

    # LaTeX head table for slow modes.
    tab = Path(args.table_tex_out)
    tab.parent.mkdir(parents=True, exist_ok=True)
    tlines: List[str] = []
    tlines.append("\\begin{table}[H]")
    tlines.append("\\centering")
    tlines.append("\\scriptsize")
    tlines.append("\\setlength{\\tabcolsep}{6pt}")
    tlines.append(
        "\\caption{Slow-mode head for the centered $((3,3,5))$ tensor $\\widetilde C$ (third axis $N_2\\bmod 5$). "
        "Modes are sorted by the twisted spectral ratio $\\rho(j)/\\lambda$ (descending); we list their Fourier energy "
        "fractions and cumulative energy.}"
    )
    tlines.append("\\label{tab:arity_335_slow_modes_energy_head}")
    tlines.append("\\begin{tabular}{r r r r r r}")
    tlines.append("\\toprule")
    tlines.append("$j_1$ & $j_2$ & $j_3$ & $\\rho(j)/\\lambda$ & $|\\widehat{\\widetilde C}(j)|^2$ & cum\\\\")
    tlines.append("\\midrule")
    for r in rows:
        tlines.append(
            f"{r.j1} & {r.j2} & {r.j3} & {r.rho_over_lam:.12f} & {r.energy:.6e} & {r.energy_cum:.6f}\\\\"
        )
    tlines.append("\\bottomrule")
    tlines.append("\\end{tabular}")
    tlines.append("\\end{table}")
    tab.write_text("\n".join(tlines) + "\n", encoding="utf-8")
    print(f"[arity-335-parseval] wrote {tab}", flush=True)


if __name__ == "__main__":
    main()

