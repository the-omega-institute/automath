#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Paley–Zygmund lower envelope for the Fold multiplicity multifractal discussion.

Given audited moment growth bases r_q (Table: tab_fold_collision_renyi_spectrum_mod_dp_q20),
we compute, for each integer q>=2 with 2q in range:
  gamma_q  = (log r_q - log phi) / q,
  f_lower  = 2 log r_q - log r_{2q},
  delta(q) = log phi - f_lower.

These are derived quantities that require *no new DP*; they are computed by reading
the already-generated TeX table for r_q.

We also plot a discrete Legendre upper bound (using the same finite r_q list):
  f_upper(gamma) = min_p (log r_p - p * gamma),
and overlay the Paley–Zygmund points (gamma_q, f_lower).

Inputs (default):
  - sections/generated/tab_fold_collision_renyi_spectrum_mod_dp_q20.tex

Outputs (default):
  - artifacts/export/fold_collision_multifractal_envelope_pz_q10.json
  - artifacts/export/fold_collision_multifractal_envelope_pz_q10.png
  - sections/generated/tab_fold_collision_multifractal_envelope_pz_q10.tex
  - sections/generated/fig_fold_collision_multifractal_envelope_pz_q10.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib.pyplot as plt
import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import PHI


_ROW_RE = re.compile(r"^\s*(\d+)\s*&\s*([0-9]+(?:\.[0-9]+)?)\s*&")


def parse_rq_from_tex_table(path: Path) -> Dict[int, float]:
    """Parse r_q values from the generated TeX table (first numeric column)."""
    text = path.read_text(encoding="utf-8")
    out: Dict[int, float] = {}
    for line in text.splitlines():
        m = _ROW_RE.match(line)
        if not m:
            continue
        q = int(m.group(1))
        rq = float(m.group(2))
        if q >= 2 and rq > 0.0:
            out[q] = rq
    if not out:
        raise RuntimeError(f"Failed to parse any r_q rows from: {path}")
    return out


@dataclass(frozen=True)
class Row:
    q: int
    r_q: float
    r_2q: float
    gamma_q: float
    f_lower: float
    delta: float


def _write_tex_table(path: Path, rows: List[Row], source_tex: str) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    # Use \detokenize to safely render filenames with underscores in text mode.
    source_tex_tt = "\\texttt{\\detokenize{" + source_tex + "}}"
    lines.append(
        "\\caption{Paley--Zygmund lower-envelope points derived from the audited $r_q$ table "
        f"(source: {source_tex_tt}). "
        "We report $\\gamma_q=(\\log r_q-\\log\\varphi)/q$, "
        "$\\underline f(q)=2\\log r_q-\\log r_{2q}$, and "
        "$\\delta(q)=\\log\\varphi-\\underline f(q)$ (all logs are natural).}"
    )
    lines.append("\\label{tab:fold_collision_multifractal_envelope_pz_q10}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append("$q$ & $r_q$ & $r_{2q}$ & $\\gamma_q$ & $\\underline f(q)$ & $\\delta(q)$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.q} & {r.r_q:.12f} & {r.r_2q:.12f} & {r.gamma_q:.6f} & {r.f_lower:.6f} & {r.delta:.6f}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_fig_tex(path: Path, png_rel: str, caption: str, label: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\\begin{figure}[H]\n"
        "\\centering\n"
        f"\\includegraphics[width=0.92\\linewidth]{{{png_rel}}}\n"
        f"\\caption{{{caption}}}\n"
        f"\\label{{{label}}}\n"
        "\\end{figure}\n",
        encoding="utf-8",
    )


def _legendre_upper_curve(gammas: np.ndarray, rq: Dict[int, float], q_max: int) -> np.ndarray:
    """Compute f_upper(gamma)=min_{2<=p<=q_max}(log r_p - p*gamma) on a gamma grid."""
    ps = [p for p in sorted(rq.keys()) if 2 <= p <= q_max]
    if not ps:
        raise ValueError("No p in range for Legendre upper curve")
    p_arr = np.array(ps, dtype=np.float64)
    logr_arr = np.array([math.log(float(rq[p])) for p in ps], dtype=np.float64)
    vals = logr_arr[None, :] - gammas[:, None] * p_arr[None, :]
    return np.min(vals, axis=1)


def main() -> None:
    ap = argparse.ArgumentParser(description="Compute Paley–Zygmund multifractal envelope points from audited r_q table.")
    ap.add_argument(
        "--rq-tex",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_renyi_spectrum_mod_dp_q20.tex"),
        help="Input TeX table that contains r_q values (first numeric column).",
    )
    ap.add_argument("--q-lower-max", type=int, default=10, help="Compute PZ points for q=2..q_lower_max.")
    ap.add_argument("--q-upper-max", type=int, default=20, help="Use r_q up to this q for the Legendre upper bound.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_multifractal_envelope_pz_q10.json"),
        help="Output JSON path.",
    )
    ap.add_argument(
        "--png-out",
        type=str,
        default=str(export_dir() / "fold_collision_multifractal_envelope_pz_q10.png"),
        help="Output PNG path.",
    )
    ap.add_argument(
        "--tex-table-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_multifractal_envelope_pz_q10.tex"),
        help="Output TeX table path.",
    )
    ap.add_argument(
        "--tex-fig-out",
        type=str,
        default=str(generated_dir() / "fig_fold_collision_multifractal_envelope_pz_q10.tex"),
        help="Output TeX figure wrapper path.",
    )
    args = ap.parse_args()

    rq_tex = Path(str(args.rq_tex))
    rq = parse_rq_from_tex_table(rq_tex)

    q_lower_max = int(args.q_lower_max)
    q_upper_max = int(args.q_upper_max)
    if q_lower_max < 2:
        raise SystemExit("Require q_lower_max >= 2")
    if q_upper_max < 2:
        raise SystemExit("Require q_upper_max >= 2")

    logphi = math.log(float(PHI))
    rows: List[Row] = []
    for q in range(2, q_lower_max + 1):
        if q not in rq or (2 * q) not in rq:
            raise SystemExit(f"Missing r_q or r_2q for q={q}: need r_{q} and r_{2*q}")
        r_q = float(rq[q])
        r_2q = float(rq[2 * q])
        gamma_q = (math.log(r_q) - logphi) / float(q)
        f_lower = 2.0 * math.log(r_q) - math.log(r_2q)
        delta = logphi - f_lower
        rows.append(Row(q=q, r_q=r_q, r_2q=r_2q, gamma_q=gamma_q, f_lower=f_lower, delta=delta))

    # Write derived table.
    tex_table_out = Path(str(args.tex_table_out))
    _write_tex_table(tex_table_out, rows, source_tex=rq_tex.name)

    # Plot envelope: Legendre upper bound from finite q list + PZ points.
    gammas = np.array([r.gamma_q for r in rows], dtype=np.float64)
    g_min = float(np.min(gammas))
    g_max = float(np.max(gammas))
    margin = 0.012
    grid = np.linspace(g_min - margin, g_max + margin, num=400, dtype=np.float64)

    f_upper = _legendre_upper_curve(grid, rq=rq, q_max=q_upper_max)
    # Plot-friendly clipping (f is in [0, log phi] by definition).
    f_upper_plot = np.clip(f_upper, 0.0, logphi)

    fig = plt.figure(figsize=(7.8, 4.6))
    ax = fig.add_subplot(1, 1, 1)
    ax.plot(grid, f_upper_plot, linewidth=1.8, color="#1E88E5", label=f"Legendre upper bound (q≤{q_upper_max})")
    ax.axhline(y=logphi, color="#444444", linestyle="--", linewidth=1.0, label=r"ceiling: $\log\varphi$")
    ax.scatter(gammas, np.array([r.f_lower for r in rows], dtype=np.float64), s=28, color="#E53935", label="PZ lower points")
    for r in rows:
        ax.annotate(str(r.q), (r.gamma_q, r.f_lower), textcoords="offset points", xytext=(5, 4), fontsize=8, color="#E53935")
    ax.set_xlabel(r"$\gamma$")
    ax.set_ylabel(r"$f(\gamma)$")
    ax.set_title(r"Two-sided multifractal envelope from $(r_q,r_{2q})$ (Paley--Zygmund + Legendre)")
    ax.grid(True, alpha=0.25)
    ax.legend(loc="best", fontsize=9)
    out_png = Path(str(args.png_out))
    out_png.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(out_png, dpi=160)
    plt.close(fig)

    # TeX figure wrapper.
    rel_png = f"artifacts/export/{out_png.name}"
    tex_fig_out = Path(str(args.tex_fig_out))
    _write_fig_tex(
        tex_fig_out,
        png_rel=rel_png,
        caption=(
            r"Two-sided envelope near the high-degeneracy tail: "
            r"Paley--Zygmund lower points $(\gamma_q,\underline f(q))$ for $q=2,\dots,"
            + str(q_lower_max)
            + r"$ overlaid with the Legendre upper bound $f(\gamma)\le \inf_{q\ge2}(\log r_q-q\gamma)$ computed on $q\le "
            + str(q_upper_max)
            + r"$. All quantities are derived from the audited $r_q$ table (no new DP)."
        ),
        label="fig:fold-collision-multifractal-envelope-pz",
    )

    payload = {
        "source_rq_tex": str(rq_tex),
        "phi": float(PHI),
        "rows": [asdict(r) for r in rows],
        "q_lower_max": q_lower_max,
        "q_upper_max": q_upper_max,
        "outputs": {
            "json": str(args.json_out),
            "png": str(out_png),
            "tex_table": str(tex_table_out),
            "tex_fig": str(tex_fig_out),
        },
        "notes": {
            "gamma_q": "(log r_q - log phi)/q",
            "f_lower": "2 log r_q - log r_{2q}",
            "delta": "log phi - f_lower",
            "f_upper": "min_p (log r_p - p*gamma) using p in [2..q_upper_max] available in the input table",
        },
    }
    jout = Path(str(args.json_out))
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[pz-envelope] wrote {jout}", flush=True)
    print(f"[pz-envelope] wrote {tex_table_out}", flush=True)
    print(f"[pz-envelope] wrote {tex_fig_out}", flush=True)
    print(f"[pz-envelope] wrote {out_png}", flush=True)


if __name__ == "__main__":
    main()

