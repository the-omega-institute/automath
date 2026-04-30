#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Generate LaTeX fragments (figures/tables) from exported CSV/PNGs."""

from __future__ import annotations

import csv
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib.pyplot as plt

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class Row:
    model: str
    alpha_name: str
    alpha: float
    partial_quotients_prefix: str
    beta: float
    x0: float
    m: int
    N: int
    tv: float
    kl: float
    unique_types: int
    DN_star_upper_bound: float | None
    DN_star_exact: float | None
    tv_multiscale_residual: float | None


@dataclass(frozen=True)
class IidRow:
    model: str
    p1: float | None
    seed: int
    m: int
    N: int
    tv_to_parry: float
    kl_to_parry: float
    kl_to_true: float
    tv_gap_true_to_parry: float
    kl_eps_95: float
    kl_bound_95: float
    tv_eps_95: float
    tv_bound_95: float
    unique_types: int


def read_rows(csv_path: Path) -> List[Row]:
    out: List[Row] = []
    with csv_path.open("r", encoding="utf-8") as f:
        rd = csv.DictReader(f)
        for r in rd:
            ub_s = (r.get("DN_star_upper_bound", "") or "").strip()
            ex_s = (r.get("DN_star_exact", "") or "").strip()
            em_s = (r.get("tv_multiscale_residual", "") or "").strip()
            out.append(
                Row(
                    model=r["model"],
                    alpha_name=r["alpha_name"],
                    alpha=float(r["alpha"]),
                    partial_quotients_prefix=r.get("partial_quotients_prefix", ""),
                    beta=float(r["beta"]),
                    x0=float(r["x0"]),
                    m=int(r["m"]),
                    N=int(r["N"]),
                    tv=float(r["tv"]),
                    kl=float(r["kl"]),
                    unique_types=int(r["unique_types"]),
                    DN_star_upper_bound=float(ub_s) if ub_s else None,
                    DN_star_exact=float(ex_s) if ex_s else None,
                    tv_multiscale_residual=float(em_s) if em_s else None,
                )
            )
    return out


def read_iid_rows(csv_path: Path) -> List[IidRow]:
    out: List[IidRow] = []
    with csv_path.open("r", encoding="utf-8") as f:
        rd = csv.DictReader(f)
        for r in rd:
            p1s = r.get("p1", "").strip()
            out.append(
                IidRow(
                    model=r["model"],
                    p1=float(p1s) if p1s else None,
                    seed=int(r["seed"]),
                    m=int(r["m"]),
                    N=int(r["N"]),
                    tv_to_parry=float(r["tv_to_parry"]),
                    kl_to_parry=float(r["kl_to_parry"]),
                    kl_to_true=float(r.get("kl_to_true", "0") or 0.0),
                    tv_gap_true_to_parry=float(r["tv_gap_true_to_parry"]),
                    kl_eps_95=float(r.get("kl_eps_95", "0") or 0.0),
                    kl_bound_95=float(r.get("kl_bound_95", "0") or 0.0),
                    tv_eps_95=float(r["tv_eps_95"]),
                    tv_bound_95=float(r["tv_bound_95"]),
                    unique_types=int(r["unique_types"]),
                )
            )
    return out


def mean(xs: List[float]) -> float:
    return sum(xs) / float(len(xs)) if xs else 0.0


def std(xs: List[float]) -> float:
    if not xs:
        return 0.0
    if len(xs) == 1:
        return 0.0
    mu = mean(xs)
    v = sum((x - mu) ** 2 for x in xs) / float(len(xs) - 1)
    return v**0.5


def group_stats(rows: List[Row]) -> Dict[Tuple[str, int, int], Tuple[float, float, float, float]]:
    """Key: (alpha_name, m, N) -> (mean_tv, std_tv, mean_kl, std_kl) over (beta,x0)."""
    buckets: Dict[Tuple[str, int, int], List[Row]] = {}
    for r in rows:
        k = (r.alpha_name, r.m, r.N)
        buckets.setdefault(k, []).append(r)
    out: Dict[Tuple[str, int, int], Tuple[float, float, float, float]] = {}
    for k, rs in buckets.items():
        tvs = [x.tv for x in rs]
        kls = [x.kl for x in rs]
        out[k] = (mean(tvs), std(tvs), mean(kls), std(kls))
    return out


def group_dn_star_upper(rows: List[Row]) -> Dict[Tuple[str, int, int], float]:
    """Key: (alpha_name, m, N) -> a representative D_N^* upper bound."""
    out: Dict[Tuple[str, int, int], float] = {}
    for r in rows:
        if r.DN_star_upper_bound is None:
            continue
        k = (r.alpha_name, r.m, r.N)
        if k not in out:
            out[k] = r.DN_star_upper_bound
    return out


def group_dn_star_exact(rows: List[Row]) -> Dict[Tuple[str, int, int], Tuple[float, float]]:
    """Key: (alpha_name, m, N) -> (mean_exact, std_exact) over x0."""
    buckets: Dict[Tuple[str, int, int], List[float]] = {}
    for r in rows:
        if r.DN_star_exact is None:
            continue
        k = (r.alpha_name, r.m, r.N)
        buckets.setdefault(k, []).append(r.DN_star_exact)
    out: Dict[Tuple[str, int, int], Tuple[float, float]] = {}
    for k, xs in buckets.items():
        out[k] = (mean(xs), std(xs))
    return out


def group_multiscale_residual(rows: List[Row]) -> Dict[Tuple[str, int, int], Tuple[float, float]]:
    """Key: (alpha_name, m, N) -> (mean_E, std_E) over (beta,x0), when available."""
    buckets: Dict[Tuple[str, int, int], List[float]] = {}
    for r in rows:
        if r.tv_multiscale_residual is None:
            continue
        k = (r.alpha_name, r.m, r.N)
        buckets.setdefault(k, []).append(r.tv_multiscale_residual)
    out: Dict[Tuple[str, int, int], Tuple[float, float]] = {}
    for k, xs in buckets.items():
        out[k] = (mean(xs), std(xs))
    return out


def latex_escape_text(s: str) -> str:
    """Escape minimal LaTeX special chars for plain text fields."""
    return s.replace("_", "\\_")


def write_fig_tex(fig_name: str, png_rel: str, caption: str, label: str) -> None:
    p = generated_dir() / f"{fig_name}.tex"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(
        "\\begin{figure}[H]\n"
        "\\centering\n"
        f"\\includegraphics[width=0.92\\linewidth]{{{png_rel}}}\n"
        f"\\caption{{{caption}}}\n"
        f"\\label{{{label}}}\n"
        "\\end{figure}\n",
        encoding="utf-8",
    )


def write_table_summary(rows: List[Row], out_name: str, N_pick: int) -> None:
    ms = sorted({r.m for r in rows})
    alpha_names = sorted({r.alpha_name for r in rows})
    gs = group_stats(rows)

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{3pt}")
    lines.append("\\caption{旋转扫描模型：折叠后稳定类型直方图与 Parry(PF) 基准的偏差（对 $\\beta,x_0$ 取平均）。}")
    lines.append("\\label{tab:rotation_fold_vs_parry_summary}")
    lines.append("\\resizebox{\\linewidth}{!}{%")
    lines.append("\\begin{tabular}{lrr" + "rr" * len(alpha_names) + "}")
    lines.append("\\toprule")

    hdr = ["$m$", "$N$", "golden $D_N^*$ upper"]
    for a in alpha_names:
        a_tex = latex_escape_text(a)
        hdr.extend([f"{a_tex} $D_\\mathrm{{TV}}$", f"{a_tex} $D_\\mathrm{{KL}}$"])
    lines.append(" & ".join(hdr) + "\\\\")
    lines.append("\\midrule")

    for m in ms:
        # Use golden bound from any golden row, if present.
        golden_bound = None
        for r in rows:
            if r.alpha_name == "golden" and r.m == m and r.N == N_pick and r.DN_star_upper_bound is not None:
                golden_bound = r.DN_star_upper_bound
                break
        gb_str = f"{golden_bound:.3g}" if golden_bound is not None else "--"

        row_cells = [str(m), str(N_pick), gb_str]
        for a in alpha_names:
            tv_mu, _, kl_mu, _ = gs.get((a, m, N_pick), (0.0, 0.0, 0.0, 0.0))
            row_cells.append(f"{tv_mu:.3g}")
            row_cells.append(f"{kl_mu:.3g}")
        lines.append(" & ".join(row_cells) + "\\\\")

    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("}%")
    lines.append("\\end{table}")
    (generated_dir() / f"{out_name}.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_table_multiscale_residual(rows: List[Row], out_name: str, N_pick: int) -> None:
    gs_e = group_multiscale_residual(rows)
    dn_exact = group_dn_star_exact(rows)
    alpha_names = sorted({r.alpha_name for r in rows})
    ms = sorted({r.m for r in rows if r.N == N_pick and r.tv_multiscale_residual is not None})

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{4pt}")
    lines.append(
        "\\caption{旋转扫描模型：跨分辨率一致性残差 $E_m:=D_\\mathrm{TV}(\\hat\\pi_{m,N},\\pi_{m+1\\to m*}\\hat\\pi_{m+1,N})$（对 $(\\beta,x_0)$ 取平均）。同时给出代表性的星差异度 $D_N^*$（对 $x_0$ 取平均）。}"
    )
    lines.append("\\label{tab:rotation_multiscale_residual_summary}")
    lines.append("\\resizebox{\\linewidth}{!}{%")
    lines.append("\\begin{tabular}{rr" + "r" * (1 + len(alpha_names)) + "}")
    lines.append("\\toprule")

    hdr = ["$m$", "$N$", "$\\overline{D_N^*}$"]
    for a in alpha_names:
        hdr.append(f"{latex_escape_text(a)} $\\overline{{E_m}}$")
    lines.append(" & ".join(hdr) + "\\\\")
    lines.append("\\midrule")

    for m in ms:
        dn_cell = "--"
        # Use any available exact D_N^* at this (m,N) (independent of beta).
        for a in alpha_names:
            k = (a, m, N_pick)
            if k in dn_exact:
                dn_cell = f"{dn_exact[k][0]:.3g}"
                break

        row_cells = [str(m), str(N_pick), dn_cell]
        for a in alpha_names:
            k = (a, m, N_pick)
            if k in gs_e:
                mu, _ = gs_e[k]
                row_cells.append(f"{mu:.3g}")
            else:
                row_cells.append("--")
        lines.append(" & ".join(row_cells) + "\\\\")

    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("}%")
    lines.append("\\end{table}")
    (generated_dir() / f"{out_name}.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_table_iid_ci(rows: List[IidRow], out_name: str, m_pick: int, N_pick: int) -> None:
    models = sorted({r.model for r in rows})
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{4pt}")
    lines.append(
        "\\caption{IID 块采样基线：折叠后稳定类型直方图到 Parry(PF) 基线的偏差，以及 95\\% TV 证书（对 seed 取平均）。}"
    )
    lines.append("\\label{tab:iid_sources_fold_vs_parry_ci}")
    lines.append("\\begin{tabular}{lrrrrrr}")
    lines.append("\\toprule")
    lines.append(
        "model & $D_\\mathrm{TV}$ & gap & $\\varepsilon^{\\mathrm{TV}}_{0.95}$ & bound$^{\\mathrm{TV}}_{0.95}$ & $D_\\mathrm{KL}(\\hat p\\|p_{\\mathrm{true}})$ & $\\varepsilon^{\\mathrm{KL}}_{0.95}$\\\\"
    )
    lines.append("\\midrule")

    for model in models:
        rs = [r for r in rows if r.model == model and r.m == m_pick and r.N == N_pick]
        if not rs:
            continue
        tv_mu = mean([r.tv_to_parry for r in rs])
        gap_mu = mean([r.tv_gap_true_to_parry for r in rs])
        eps_mu = mean([r.tv_eps_95 for r in rs])
        bnd_mu = mean([r.tv_bound_95 for r in rs])
        kl_true_mu = mean([r.kl_to_true for r in rs])
        kl_eps_mu = mean([r.kl_eps_95 for r in rs])
        lines.append(
            f"{latex_escape_text(model)} & {tv_mu:.3g} & {gap_mu:.3g} & {eps_mu:.3g} & {bnd_mu:.3g} & {kl_true_mu:.3g} & {kl_eps_mu:.3g}\\\\"
        )

    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    (generated_dir() / f"{out_name}.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


def plot_tv_vs_m(rows: List[Row], N_pick: int, out_png: Path) -> None:
    gs = group_stats(rows)
    ms = sorted({r.m for r in rows})
    alpha_names = sorted({r.alpha_name for r in rows})

    plt.figure(figsize=(7.2, 4.2))
    for a in alpha_names:
        xs = [m for m in ms if (a, m, N_pick) in gs]
        ys = [gs[(a, m, N_pick)][0] for m in xs]
        yerr = [gs[(a, m, N_pick)][1] for m in xs]
        plt.errorbar(xs, ys, yerr=yerr, marker="o", capsize=3, linewidth=1.5, label=a)
    plt.xlabel("m")
    plt.ylabel("TV distance to Parry baseline")
    plt.title(f"Rotation scan: $D_{{TV}}(\\hat{{\\pi}}_m,\\pi_m)$ vs m (N={N_pick})")
    plt.grid(True, alpha=0.3)
    plt.legend()
    out_png.parent.mkdir(parents=True, exist_ok=True)
    plt.tight_layout()
    plt.savefig(out_png, dpi=200)
    plt.close()


def plot_kl_vs_m(rows: List[Row], N_pick: int, out_png: Path) -> None:
    gs = group_stats(rows)
    ms = sorted({r.m for r in rows})
    alpha_names = sorted({r.alpha_name for r in rows})

    plt.figure(figsize=(7.2, 4.2))
    for a in alpha_names:
        xs = [m for m in ms if (a, m, N_pick) in gs]
        ys = [gs[(a, m, N_pick)][2] for m in xs]
        yerr = [gs[(a, m, N_pick)][3] for m in xs]
        plt.errorbar(xs, ys, yerr=yerr, marker="o", capsize=3, linewidth=1.5, label=a)
    plt.xlabel("m")
    plt.ylabel("KL divergence to Parry baseline")
    plt.title(f"Rotation scan: $D_{{KL}}(\\hat{{\\pi}}_m\\|\\pi_m)$ vs m (N={N_pick})")
    plt.grid(True, alpha=0.3)
    plt.legend()
    out_png.parent.mkdir(parents=True, exist_ok=True)
    plt.tight_layout()
    plt.savefig(out_png, dpi=200)
    plt.close()


def plot_tv_vs_n(rows: List[Row], m_pick: int, out_png: Path) -> None:
    gs = group_stats(rows)
    gb = group_dn_star_upper(rows)
    Ns = sorted({r.N for r in rows})
    alpha_names = sorted({r.alpha_name for r in rows})

    plt.figure(figsize=(7.2, 4.2))
    for a in alpha_names:
        xs = [N for N in Ns if (a, m_pick, N) in gs]
        ys = [gs[(a, m_pick, N)][0] for N in xs]
        yerr = [gs[(a, m_pick, N)][1] for N in xs]
        plt.errorbar(xs, ys, yerr=yerr, marker="o", capsize=3, linewidth=1.5, label=a)

        # Theory envelope (finite-sample term): (m+1) * D_N^* upper bound.
        bx = [N for N in xs if (a, m_pick, N) in gb]
        if bx:
            by = [(m_pick + 1) * gb[(a, m_pick, N)] for N in bx]
            # Avoid legend explosion: don't add these envelopes to the legend.
            plt.plot(bx, by, linestyle="--", linewidth=1.0, alpha=0.6, label="_nolegend_")
    plt.xscale("log")
    plt.yscale("log")
    plt.xlabel("N (log)")
    plt.ylabel("TV distance to Parry baseline (log)")
    plt.title(f"Rotation scan: $D_{{TV}}(\\hat{{\\pi}}_m,\\pi_m)$ vs N (m={m_pick})")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    out_png.parent.mkdir(parents=True, exist_ok=True)
    plt.tight_layout()
    plt.savefig(out_png, dpi=200)
    plt.close()


def plot_kl_vs_n(rows: List[Row], m_pick: int, out_png: Path) -> None:
    gs = group_stats(rows)
    Ns = sorted({r.N for r in rows})
    alpha_names = sorted({r.alpha_name for r in rows})

    plt.figure(figsize=(7.2, 4.2))
    for a in alpha_names:
        xs = [N for N in Ns if (a, m_pick, N) in gs]
        ys = [gs[(a, m_pick, N)][2] for N in xs]
        yerr = [gs[(a, m_pick, N)][3] for N in xs]
        plt.errorbar(xs, ys, yerr=yerr, marker="o", capsize=3, linewidth=1.5, label=a)
    plt.xscale("log")
    plt.yscale("log")
    plt.xlabel("N (log)")
    plt.ylabel("KL divergence to Parry baseline (log)")
    plt.title(f"Rotation scan: $D_{{KL}}(\\hat{{\\pi}}_m\\|\\pi_m)$ vs N (m={m_pick})")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    out_png.parent.mkdir(parents=True, exist_ok=True)
    plt.tight_layout()
    plt.savefig(out_png, dpi=200)
    plt.close()


def plot_iid_tv_vs_n(rows: List[IidRow], m_pick: int, out_png: Path) -> None:
    Ns = sorted({r.N for r in rows if r.m == m_pick})
    models = sorted({r.model for r in rows})

    plt.figure(figsize=(7.2, 4.2))
    for model in models:
        xs = [N for N in Ns if any(r.model == model and r.N == N and r.m == m_pick for r in rows)]
        ys: List[float] = []
        yb: List[float] = []
        for N in xs:
            rs = [r for r in rows if r.model == model and r.N == N and r.m == m_pick]
            ys.append(mean([r.tv_to_parry for r in rs]))
            yb.append(mean([r.tv_bound_95 for r in rs]))
        plt.plot(xs, ys, marker="o", linewidth=1.6, label=f"{model} TV")
        plt.plot(xs, yb, linestyle="--", linewidth=1.2, alpha=0.8, label=f"{model} bound95")

    plt.xscale("log")
    plt.yscale("log")
    plt.xlabel("N (log)")
    plt.ylabel("TV to Parry baseline (log)")
    plt.title(f"IID blocks: TV to Parry vs N (m={m_pick})")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    out_png.parent.mkdir(parents=True, exist_ok=True)
    plt.tight_layout()
    plt.savefig(out_png, dpi=200)
    plt.close()


def write_table_phi_m_entropy(csv_path: Path, out_name: str) -> None:
    with csv_path.open("r", encoding="utf-8") as f:
        rd = csv.DictReader(f)
        rows = list(rd)
    if not rows:
        raise SystemExit("[exp_generated_tex] empty phi_m_sofic_entropy input")

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{4pt}")
    lines.append("\\caption{Sofic 图像 $Y_m$ 的右解析最小化表示规模与拓扑熵（脚本生成）。}")
    lines.append("\\label{tab:phi_m_sofic_entropy}")
    lines.append("\\begin{tabular}{rrrrrr}")
    lines.append("\\toprule")
    lines.append("$m$ & det states & min states & ess states & det edges & $h_{\\mathrm{top}}$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r['m']} & {r['det_states']} & {r['min_states']} & {r['ess_states']} & {r['det_edges']} & {float(r['h_top']):.6g}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    (generated_dir() / f"{out_name}.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


def load_arity_payload() -> dict:
    path = export_dir() / "sync_kernel_real_input_40_arity.json"
    if not path.is_file():
        raise SystemExit(f"[exp_generated_tex] missing arity payload: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def arity_counts(payload: dict) -> Dict[str, List[List[int]]]:
    counts = payload.get("arity_class_counts", {})
    if counts:
        return counts
    legacy: Dict[str, List[List[int]]] = {}
    for m in (2, 3, 5):
        key = f"arity_class_counts_m{m}"
        if key in payload:
            legacy[str(m)] = payload[key]
    return legacy


def arity_m_values(payload: dict, counts: Dict[str, List[List[int]]]) -> List[int]:
    m_vals = payload.get("m_values", [])
    if isinstance(m_vals, list) and m_vals:
        return [int(v) for v in m_vals]
    return sorted(int(k) for k in counts.keys())


def plot_arity_class_density(payload: dict, out_png: Path) -> None:
    counts_all = arity_counts(payload)
    if not counts_all:
        raise SystemExit("[exp_generated_tex] missing arity class counts")
    p_n = payload.get("p_n", [])
    if not p_n:
        raise SystemExit("[exp_generated_tex] missing p_n in arity payload")
    max_n = min(int(payload.get("max_n", len(p_n))), len(p_n))
    m_values = arity_m_values(payload, counts_all)
    if not m_values:
        raise SystemExit("[exp_generated_tex] empty m_values for arity plots")

    ncols = 3
    nrows = math.ceil(len(m_values) / ncols)
    fig, axes = plt.subplots(nrows, ncols, figsize=(4.4 * ncols, 3.2 * nrows), sharey=True)
    axes_list = list(axes.flat) if hasattr(axes, "flat") else [axes]
    ns = list(range(1, max_n + 1))

    for idx, m in enumerate(m_values):
        ax = axes_list[idx]
        counts = counts_all[str(m)]
        for r in range(m):
            ys = []
            for i in range(max_n):
                denom = float(p_n[i]) if p_n[i] else 1.0
                ys.append(float(counts[i][r]) / denom)
            ax.plot(ns, ys, marker="o", linewidth=1.1, markersize=3, label=f"r={r}")
        ax.set_title(f"m={m}")
        ax.set_xlabel("n")
        if idx % ncols == 0:
            ax.set_ylabel("class density")
        ax.set_ylim(0.0, 1.0)
        ax.grid(True, alpha=0.25)
        legend_cols = 2 if m <= 7 else 3
        ax.legend(fontsize=7, ncol=legend_cols, frameon=False)

    for j in range(len(m_values), len(axes_list)):
        axes_list[j].axis("off")

    fig.suptitle("Arity-class densities N_{n,r}/p_n", y=1.02)
    out_png.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(out_png, dpi=200)
    plt.close(fig)


def plot_arity_class_logM(payload: dict, out_png: Path) -> None:
    logM = payload.get("arity_class_logM", {})
    if not logM:
        raise SystemExit("[exp_generated_tex] missing arity_class_logM in payload")
    m_values = sorted(int(k) for k in logM.keys())
    if not m_values:
        raise SystemExit("[exp_generated_tex] empty m_values for logM plot")

    ncols = 3
    nrows = math.ceil(len(m_values) / ncols)
    fig, axes = plt.subplots(nrows, ncols, figsize=(4.4 * ncols, 3.1 * nrows), sharey=False)
    axes_list = list(axes.flat) if hasattr(axes, "flat") else [axes]

    for idx, m in enumerate(m_values):
        ax = axes_list[idx]
        vals = [float(logM[str(m)][str(r)]) for r in range(m)]
        rs = list(range(m))
        ax.plot(rs, vals, marker="o", linewidth=1.2, markersize=3)
        ax.axhline(0.0, color="gray", linewidth=0.8, alpha=0.6)
        ax.set_title(f"m={m}")
        ax.set_xlabel("r")
        if idx % ncols == 0:
            ax.set_ylabel("log M_r")
        ax.grid(True, alpha=0.25)
        ax.set_xticks(rs)

    for j in range(len(m_values), len(axes_list)):
        axes_list[j].axis("off")

    fig.suptitle("Arity-class Abel constants (log M_r)", y=1.02)
    out_png.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(out_png, dpi=200)
    plt.close(fig)


def main() -> None:
    csv_in = export_dir() / "rotation_fold_vs_parry.csv"
    rows = read_rows(csv_in)
    if not rows:
        raise SystemExit("[exp_generated_tex] empty input")

    Ns = sorted({r.N for r in rows})
    N_pick = Ns[-1]
    ms = sorted({r.m for r in rows})
    m_pick = 12 if 12 in ms else ms[len(ms) // 2]

    png_tv = export_dir() / "rotation_tv_vs_m.png"
    png_kl = export_dir() / "rotation_kl_vs_m.png"
    png_tv_n = export_dir() / "rotation_tv_vs_n.png"
    png_kl_n = export_dir() / "rotation_kl_vs_n.png"
    plot_tv_vs_m(rows, N_pick=N_pick, out_png=png_tv)
    plot_kl_vs_m(rows, N_pick=N_pick, out_png=png_kl)
    plot_tv_vs_n(rows, m_pick=m_pick, out_png=png_tv_n)
    plot_kl_vs_n(rows, m_pick=m_pick, out_png=png_kl_n)

    write_fig_tex(
        fig_name="fig_rotation_tv_vs_m",
        png_rel="artifacts/export/rotation_tv_vs_m.png",
        caption="旋转扫描模型下，折叠后稳定类型直方图与 Parry(PF) 基准柱分布的总变差距离随 $m$ 的变化（对 $\\beta,x_0$ 取平均）。",
        label="fig:rotation_tv_vs_m",
    )
    write_fig_tex(
        fig_name="fig_rotation_kl_vs_m",
        png_rel="artifacts/export/rotation_kl_vs_m.png",
        caption="旋转扫描模型下，折叠后稳定类型直方图与 Parry(PF) 基准柱分布的相对熵随 $m$ 的变化（对 $\\beta,x_0$ 取平均）。",
        label="fig:rotation_kl_vs_m",
    )

    write_fig_tex(
        fig_name="fig_rotation_tv_vs_n",
        png_rel="artifacts/export/rotation_tv_vs_n.png",
        caption=f"旋转扫描模型下，固定分辨率 $m={m_pick}$ 时，折叠后稳定类型直方图与 Parry(PF) 基准柱分布的总变差距离随样本量 $N$ 的收敛（对 $\\beta,x_0$ 取平均；误差线为样本标准差；虚线为 $(m+1)D_N^*$ 的差异度上界络线；双对数坐标）。",
        label="fig:rotation_tv_vs_n",
    )
    write_fig_tex(
        fig_name="fig_rotation_kl_vs_n",
        png_rel="artifacts/export/rotation_kl_vs_n.png",
        caption=f"旋转扫描模型下，固定分辨率 $m={m_pick}$ 时，折叠后稳定类型直方图与 Parry(PF) 基准柱分布的相对熵随样本量 $N$ 的收敛（对 $\\beta,x_0$ 取平均；误差线为样本标准差；双对数坐标）。",
        label="fig:rotation_kl_vs_n",
    )

    write_table_summary(rows, out_name="tab_rotation_fold_vs_parry_summary", N_pick=N_pick)
    write_table_multiscale_residual(rows, out_name="tab_rotation_multiscale_residual_summary", N_pick=N_pick)

    # IID baselines (Bernoulli / Parry blocks) with confidence envelopes.
    iid_csv = export_dir() / "iid_sources_fold_vs_parry.csv"
    iid_rows = read_iid_rows(iid_csv)
    if not iid_rows:
        raise SystemExit("[exp_generated_tex] empty iid input")

    ms_iid = sorted({r.m for r in iid_rows})
    m_pick_iid = 10 if 10 in ms_iid else ms_iid[len(ms_iid) // 2]
    png_iid = export_dir() / "iid_tv_vs_n.png"
    plot_iid_tv_vs_n(iid_rows, m_pick=m_pick_iid, out_png=png_iid)
    write_fig_tex(
        fig_name="fig_iid_tv_vs_n",
        png_rel="artifacts/export/iid_tv_vs_n.png",
        caption=f"IID 块采样基线下，固定分辨率 $m={m_pick_iid}$ 时，折叠后稳定类型直方图到 Parry(PF) 基线的 TV 偏差随样本量 $N$ 的变化，并叠加 95\\% TV 证书上界（对 seed 取平均；双对数坐标）。",
        label="fig:iid_tv_vs_n",
    )
    write_table_iid_ci(iid_rows, out_name="tab_iid_sources_fold_vs_parry_ci", m_pick=m_pick_iid, N_pick=30_000)

    write_table_phi_m_entropy(
        csv_path=export_dir() / "phi_m_sofic_entropy.csv",
        out_name="tab_phi_m_sofic_entropy",
    )

    arity_payload = load_arity_payload()
    png_density = export_dir() / "arity_class_density_by_m.png"
    png_logm = export_dir() / "arity_class_logM_by_m.png"
    plot_arity_class_density(arity_payload, out_png=png_density)
    plot_arity_class_logM(arity_payload, out_png=png_logm)

    m_values = arity_m_values(arity_payload, arity_counts(arity_payload))
    m_tag = ",".join(str(m) for m in m_values)
    write_fig_tex(
        fig_name="fig_arity_class_density",
        png_rel="artifacts/export/arity_class_density_by_m.png",
        caption=f"真实输入 40 状态核下，arity 类密度 $N_{{n,r}}^{{(m)}}/p_n$ 随 $n$ 的变化（$m\\in\\{{{m_tag}\\}}$）。",
        label="fig:arity_class_density",
    )
    write_fig_tex(
        fig_name="fig_arity_class_logM",
        png_rel="artifacts/export/arity_class_logM_by_m.png",
        caption=f"真实输入 40 状态核下，arity 类 Abel 常数 $\\log\\mathfrak{{M}}_r^{{(m)}}$ 的分布（$m\\in\\{{{m_tag}\\}}$）。",
        label="fig:arity_class_logM",
    )

    print("[exp_generated_tex] OK", flush=True)


if __name__ == "__main__":
    main()

