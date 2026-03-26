#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Compute ANOVA/Hoeffding interaction diagnostics for Dirichlet–Mertens constant tensors.

We load reproducible outputs from:
  - artifacts/export/sync_kernel_real_input_40_arity_3d.json
  - artifacts/export/sync_kernel_real_input_40_arity_3d_N2_335.json

For each 3D constant tensor C_{a,b,c} (a=chi mod m1, b=N_- mod m2, c=third axis mod m3),
we form the centered tensor:
  C~ = C - mathsf_M / |G|
and compute the standard 3-way Hoeffding/ANOVA orthogonal decomposition under the
uniform inner product on G = Z/m1 x Z/m2 x Z/m3.

We report:
  - S_ABC := ||C^(ABC)||_2^2 / ||C~||_2^2
  - L_lock(A<->C) := (||C^(AC)||_2^2 + ||C^(ABC)||_2^2) / ||C~||_2^2
where axis A is chi and axis C is the 3rd coordinate (Ne or N2 depending on the tensor).

We also attach the worst twisted ratio rho/lambda and the worst character indices j.

Outputs:
  - artifacts/export/real_input_40_dirichlet_mertens_tensor_anova.json
  - artifacts/export/real_input_40_dirichlet_mertens_tensor_anova_scatter.png
  - sections/generated/tab_real_input_40_dirichlet_mertens_tensor_anova.tex
  - sections/generated/fig_real_input_40_dirichlet_mertens_tensor_anova_scatter.tex

All stdout is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib.pyplot as plt
import numpy as np

from common_paths import export_dir, generated_dir, paper_root


def _phi() -> float:
    return (1.0 + 5.0**0.5) / 2.0


def _lam() -> float:
    p = _phi()
    return p * p


def _parse_triple(key: str) -> Tuple[int, int, int]:
    parts = key.split("x")
    if len(parts) != 3:
        raise ValueError(f"bad triple key: {key!r}")
    return int(parts[0]), int(parts[1]), int(parts[2])


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _tensor_from_map(m1: int, m2: int, m3: int, mp: Dict[str, float]) -> np.ndarray:
    T = np.zeros((m1, m2, m3), dtype=float)
    for a in range(m1):
        for b in range(m2):
            for c in range(m3):
                T[a, b, c] = float(mp[f"{a},{b},{c}"])
    return T


@dataclass(frozen=True)
class Metrics:
    triple: str
    third_axis: str  # "Ne" or "N2"
    m1: int
    m2: int
    m3: int
    S_ABC: float
    L_A_C: float
    rho_over_lam: float
    rho_max: float
    j_argmax: List[Tuple[int, int, int]]
    j_support_min: int
    j_support_max: int


def _anova_metrics(C: np.ndarray, mathsf_M: float) -> Tuple[float, float]:
    m1, m2, m3 = C.shape
    mean = float(mathsf_M) / float(m1 * m2 * m3)
    Ct = C - mean

    # Main effects.
    A = np.mean(Ct, axis=(1, 2))  # shape (m1,)
    B = np.mean(Ct, axis=(0, 2))  # shape (m2,)
    Cc = np.mean(Ct, axis=(0, 1))  # shape (m3,)

    # Two-way means.
    mean_ab = np.mean(Ct, axis=2)  # (m1,m2)
    mean_ac = np.mean(Ct, axis=1)  # (m1,m3)
    mean_bc = np.mean(Ct, axis=0)  # (m2,m3)

    AB = mean_ab - A[:, None] - B[None, :]
    AC = mean_ac - A[:, None] - Cc[None, :]
    BC = mean_bc - B[:, None] - Cc[None, :]

    # Broadcast into full tensor space.
    A3 = A[:, None, None]
    B3 = B[None, :, None]
    C3 = Cc[None, None, :]
    AB3 = AB[:, :, None]
    AC3 = AC[:, None, :]
    BC3 = BC[None, :, :]
    ABC = Ct - (A3 + B3 + C3 + AB3 + AC3 + BC3)

    n_tot = float(np.sum(Ct * Ct))
    if n_tot <= 0.0:
        return 0.0, 0.0
    n_abc = float(np.sum(ABC * ABC))
    n_ac = float(np.sum(AC3 * AC3))
    S_ABC = n_abc / n_tot
    L_A_C = (n_ac + n_abc) / n_tot
    return float(S_ABC), float(L_A_C)


def _worst_character(rho_map: Dict[str, float], *, eps: float = 1e-12) -> Tuple[float, List[Tuple[int, int, int]]]:
    if not rho_map:
        return 0.0, []
    rho_max = max(float(v) for v in rho_map.values())
    argmax_keys = sorted([k for k, v in rho_map.items() if abs(float(v) - rho_max) <= eps])
    out: List[Tuple[int, int, int]] = []
    for k in argmax_keys:
        parts = [int(x) for x in k.split(",")]
        if len(parts) != 3:
            continue
        out.append((parts[0], parts[1], parts[2]))
    return rho_max, out


def _support_size(j: Tuple[int, int, int]) -> int:
    return int((j[0] != 0) + (j[1] != 0) + (j[2] != 0))


def _fmt_j_list(js: List[Tuple[int, int, int]], max_show: int = 4) -> str:
    if not js:
        return "-"
    shown = js[:max_show]
    s = ", ".join(f"({a},{b},{c})" for (a, b, c) in shown)
    if len(js) > max_show:
        s += ", …"
    return s


def _write_table_tex(path: Path, rows: List[Metrics]) -> None:
    def fmt(x: float) -> str:
        return f"{x:.3f}"

    def fmt_ratio(x: float) -> str:
        return f"{x:.12f}"

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Interaction diagnostics (ANOVA/Hoeffding) for reproducible Dirichlet--Mertens constant tensors "
        "$C_{a,b,c}$ of the real-input 40-state kernel. "
        "We report $S_{ABC}=\\|C^{(ABC)}\\|_2^2/\\|\\widetilde C\\|_2^2$ and "
        "$L_{A\\leftrightarrow C}=(\\|C^{(AC)}\\|_2^2+\\|C^{(ABC)}\\|_2^2)/\\|\\widetilde C\\|_2^2$ with "
        "$A=\\chi$ and $C$ the third axis. "
        "We also list the worst twisted ratio $\\rho/\\lambda$ and the corresponding worst character indices $j$.}"
    )
    lines.append("\\label{tab:real_input_40_dirichlet_mertens_tensor_anova}")
    lines.append("\\begin{tabular}{l l r r l l}")
    lines.append("\\toprule")
    lines.append("tensor & third axis & $S_{ABC}$ & $L_{A\\leftrightarrow C}$ & $\\rho/\\lambda$ & worst $j$ (support)\\\\")
    lines.append("\\midrule")
    for r in rows:
        jtxt = _fmt_j_list(r.j_argmax)
        supp = f"{r.j_support_min}" if r.j_support_min == r.j_support_max else f"{r.j_support_min}--{r.j_support_max}"
        lines.append(
            f"$(({r.m1},{r.m2},{r.m3}))$ & {r.third_axis} & {fmt(r.S_ABC)} & {fmt(r.L_A_C)} & {fmt_ratio(r.rho_over_lam)} & {jtxt} ({supp})\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_scatter_png(path: Path, rows: List[Metrics]) -> None:
    # Scatter: x = S_ABC, y = rho/lambda. Marker size by support size.
    plt.figure(figsize=(6.8, 4.4), dpi=160)
    ax = plt.gca()

    # group by third axis
    groups: Dict[str, List[Metrics]] = {}
    for r in rows:
        groups.setdefault(r.third_axis, []).append(r)

    colors = {"Ne": "#1f77b4", "N2": "#d62728"}
    for g, items in groups.items():
        xs = [it.S_ABC for it in items]
        ys = [it.rho_over_lam for it in items]
        ss = [60 + 50 * it.j_support_min for it in items]
        ax.scatter(xs, ys, s=ss, alpha=0.85, c=colors.get(g, "#333333"), label=g, edgecolors="white", linewidths=0.7)
        for it in items:
            ax.annotate(
                f"({it.m1},{it.m2},{it.m3})",
                (it.S_ABC, it.rho_over_lam),
                textcoords="offset points",
                xytext=(6, 5),
                fontsize=8,
            )

    ax.set_xlabel(r"$S_{ABC}=\|C^{(ABC)}\|_2^2/\|\widetilde C\|_2^2$")
    ax.set_ylabel(r"$\rho/\lambda$")
    ax.set_title("Dirichlet–Mertens tensor interaction vs worst twisted ratio")
    ax.grid(True, linestyle="--", alpha=0.35)
    ax.legend(title="third axis", loc="best", fontsize=8, title_fontsize=8, frameon=True)
    ax.set_xlim(-0.02, 1.02)
    ax.set_ylim(0.85, 0.99)
    plt.tight_layout()
    path.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(path)
    plt.close()


def _write_fig_tex(path: Path, png_rel: str) -> None:
    lines: List[str] = []
    lines.append("\\begin{figure}[H]")
    lines.append("\\centering")
    lines.append(f"\\includegraphics[width=0.92\\linewidth]{{{png_rel}}}")
    lines.append(
        "\\caption{Scatter of tensor interaction order $S_{ABC}$ versus the worst twisted spectral ratio $\\rho/\\lambda$ "
        "for reproducible Dirichlet--Mertens constant tensors. Marker size scales with the support size of worst $j$.}"
    )
    lines.append("\\label{fig:real_input_40_dirichlet_mertens_tensor_anova_scatter}")
    lines.append("\\end{figure}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="ANOVA interaction diagnostics for Dirichlet–Mertens constant tensors.")
    parser.add_argument(
        "--json-ne",
        type=str,
        default=str(export_dir() / "sync_kernel_real_input_40_arity_3d.json"),
        help="Input JSON for third axis Ne.",
    )
    parser.add_argument(
        "--json-n2",
        type=str,
        default=str(export_dir() / "sync_kernel_real_input_40_arity_3d_N2_335.json"),
        help="Input JSON for third axis N2 (typically only 3x3x5).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_dirichlet_mertens_tensor_anova.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_dirichlet_mertens_tensor_anova.tex"),
    )
    parser.add_argument(
        "--png-out",
        type=str,
        default=str(export_dir() / "real_input_40_dirichlet_mertens_tensor_anova_scatter.png"),
    )
    parser.add_argument(
        "--fig-tex-out",
        type=str,
        default=str(generated_dir() / "fig_real_input_40_dirichlet_mertens_tensor_anova_scatter.tex"),
    )
    args = parser.parse_args()

    lam = _lam()

    rows: List[Metrics] = []

    # Load Ne tensors.
    p_ne = Path(args.json_ne)
    if p_ne.is_file():
        data = _load_json(p_ne)
        mathsf_M = float(data["mathsf_M"])
        triple_class = data.get("triple_class_C", {})
        triple_rho = data.get("triple_rho", {})
        for triple, mp in triple_class.items():
            m1, m2, m3 = _parse_triple(triple)
            C = _tensor_from_map(m1, m2, m3, mp)
            S_ABC, L_AC = _anova_metrics(C, mathsf_M)
            rho_map = {k: float(v) for k, v in (triple_rho.get(triple, {}) or {}).items()}
            rho_max, argmax = _worst_character(rho_map)
            rho_ratio = rho_max / lam if lam > 0 else 0.0
            supps = [_support_size(j) for j in argmax] if argmax else [0]
            rows.append(
                Metrics(
                    triple=triple,
                    third_axis="Ne",
                    m1=m1,
                    m2=m2,
                    m3=m3,
                    S_ABC=S_ABC,
                    L_A_C=L_AC,
                    rho_over_lam=float(rho_ratio),
                    rho_max=float(rho_max),
                    j_argmax=argmax,
                    j_support_min=int(min(supps)),
                    j_support_max=int(max(supps)),
                )
            )

    # Load N2 tensors (if present).
    p_n2 = Path(args.json_n2)
    if p_n2.is_file():
        data = _load_json(p_n2)
        mathsf_M = float(data["mathsf_M"])
        triple_class = data.get("triple_class_C", {})
        triple_rho = data.get("triple_rho", {})
        for triple, mp in triple_class.items():
            m1, m2, m3 = _parse_triple(triple)
            C = _tensor_from_map(m1, m2, m3, mp)
            S_ABC, L_AC = _anova_metrics(C, mathsf_M)
            rho_map = {k: float(v) for k, v in (triple_rho.get(triple, {}) or {}).items()}
            rho_max, argmax = _worst_character(rho_map)
            rho_ratio = rho_max / lam if lam > 0 else 0.0
            supps = [_support_size(j) for j in argmax] if argmax else [0]
            rows.append(
                Metrics(
                    triple=triple,
                    third_axis="N2",
                    m1=m1,
                    m2=m2,
                    m3=m3,
                    S_ABC=S_ABC,
                    L_A_C=L_AC,
                    rho_over_lam=float(rho_ratio),
                    rho_max=float(rho_max),
                    j_argmax=argmax,
                    j_support_min=int(min(supps)),
                    j_support_max=int(max(supps)),
                )
            )

    # Stable sorting: by (m1,m2,m3,third_axis).
    rows.sort(key=lambda r: (r.m1, r.m2, r.m3, r.third_axis))

    payload = {
        "lambda": lam,
        "rows": [
            {
                "triple": r.triple,
                "third_axis": r.third_axis,
                "m1": r.m1,
                "m2": r.m2,
                "m3": r.m3,
                "S_ABC": r.S_ABC,
                "L_A_C": r.L_A_C,
                "rho_over_lambda": r.rho_over_lam,
                "rho_max": r.rho_max,
                "j_argmax": [list(j) for j in r.j_argmax],
                "j_support_min": r.j_support_min,
                "j_support_max": r.j_support_max,
            }
            for r in rows
        ],
    }

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[dm-anova] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    _write_table_tex(tout, rows)
    print(f"[dm-anova] wrote {tout}", flush=True)

    png = Path(args.png_out)
    _write_scatter_png(png, rows)
    print(f"[dm-anova] wrote {png}", flush=True)

    ftx = Path(args.fig_tex_out)
    # figure tex uses repo-relative path
    png_rel = str(png.relative_to(paper_root()))
    _write_fig_tex(ftx, png_rel=png_rel)
    print(f"[dm-anova] wrote {ftx}", flush=True)


if __name__ == "__main__":
    main()

