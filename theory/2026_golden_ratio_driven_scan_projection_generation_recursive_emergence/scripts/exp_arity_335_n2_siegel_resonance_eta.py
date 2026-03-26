#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Siegel-like resonance length-scale diagnostics for ((3,3,p)) with third axis N2 mod p.

Given the selection-law scan output (spectral radii only):
  rho_{3,3,p} := max_{(j1,j2,j3) != (0,0,0)} rho(M_{j1,j2,j3}),
  rho_ratio   := rho_{3,3,p}/lambda,
we define:
  delta_p := 1 - rho_ratio,
  eta_p   := 1 / delta_p,              (gap-based "resonance length scale")
  tau_mix := 1 / (-log rho_ratio).     (exact exponential time scale)

Near-coboundary small-angle theory predicts:
  delta_p ~ kappa_inf * (2π/p)^2  as p→∞,
hence:
  eta_p ~ p^2 / (4π^2 kappa_inf).

Inputs (default):
  - artifacts/export/arity_335_n2_selection_law_primes.json
  - artifacts/export/arity_335_n2_master_curve.json   (for kappa_inf)

Outputs (default):
  - artifacts/export/arity_335_n2_siegel_resonance_eta.json
  - sections/generated/tab_real_input_40_arity_335_n2_siegel_resonance_eta.tex

All stdout is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir, paper_root


def _load_json(path_or_rel: str) -> dict:
    p = Path(path_or_rel)
    if p.is_absolute():
        return json.loads(p.read_text(encoding="utf-8"))
    return json.loads((paper_root() / path_or_rel).read_text(encoding="utf-8"))


@dataclass(frozen=True)
class Row:
    p: int
    rho_ratio: float
    delta: float
    eta_gap: float
    tau_mix: float
    eta_pred: float
    eta_ratio: float
    argmax: List[List[int]]


def _safe_tau_mix(rho_ratio: float) -> float:
    if rho_ratio <= 0.0 or rho_ratio >= 1.0:
        return float("inf")
    return 1.0 / (-math.log(rho_ratio))


def main() -> None:
    parser = argparse.ArgumentParser(description="Siegel-like resonance length-scale table for ((3,3,p)) (third axis N2).")
    parser.add_argument(
        "--selection-json",
        type=str,
        default="artifacts/export/arity_335_n2_selection_law_primes.json",
        help="Input selection-law JSON (relative to paper root unless absolute).",
    )
    parser.add_argument(
        "--master-json",
        type=str,
        default="artifacts/export/arity_335_n2_master_curve.json",
        help="Input master-curve JSON containing kappa_inf (relative to paper root unless absolute).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "arity_335_n2_siegel_resonance_eta.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_arity_335_n2_siegel_resonance_eta.tex"),
        help="Output LaTeX table path.",
    )
    args = parser.parse_args()

    sel = _load_json(str(args.selection_json))
    master = _load_json(str(args.master_json))
    kappa_inf = float(master["kappa_inf"])
    if not (kappa_inf > 0.0):
        raise SystemExit("invalid kappa_inf (must be positive)")

    c0 = 4.0 * (math.pi**2) * kappa_inf  # predicted constant for g(p) = delta_p * p^2

    rows: List[Row] = []
    for r in sel.get("rows", []):
        p = int(r["p"])
        rho_ratio = float(r["rho_ratio"])
        delta = float(r["gap"])
        eta_gap = (1.0 / delta) if delta > 0.0 else float("inf")
        tau_mix = _safe_tau_mix(rho_ratio)
        eta_pred = (float(p * p) / c0) if c0 > 0.0 else float("inf")
        eta_ratio = (eta_gap / eta_pred) if (eta_pred > 0.0 and math.isfinite(eta_gap)) else float("nan")
        argmax = r.get("argmax", [])
        rows.append(
            Row(
                p=p,
                rho_ratio=rho_ratio,
                delta=delta,
                eta_gap=eta_gap,
                tau_mix=tau_mix,
                eta_pred=eta_pred,
                eta_ratio=eta_ratio,
                argmax=argmax,
            )
        )

    payload: Dict[str, object] = {
        "third_axis": "N2",
        "kappa_inf": kappa_inf,
        "c0": c0,
        "rows": [asdict(rr) for rr in rows],
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[siegel-eta] wrote {jout}", flush=True)

    # LaTeX table.
    tex = Path(args.tex_out)
    tex.parent.mkdir(parents=True, exist_ok=True)
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Siegel 型共振长度尺度诊断：第三轴取 $c=N_2(\\gamma)\\bmod p$ 的 $((3,3,p))$ 最坏扭曲谱比 "
        "$\\rho_{3,3,p}/\\lambda$ 定义 $\\delta_p:=1-\\rho/\\lambda$ 与 $\\eta_p:=1/\\delta_p$，并与二次律预测 "
        f"$\\eta_p\\approx p^2/(4\\pi^2\\kappa_\\infty)$ 对照（此处 $\\kappa_\\infty\\approx {kappa_inf:.12f}$）。"
        "}"
    )
    lines.append("\\label{tab:real_input_40_arity_335_n2_siegel_resonance_eta}")
    lines.append("\\begin{tabular}{r r r r r r l}")
    lines.append("\\toprule")
    lines.append(
        "$p$ & $\\delta_p$ & $\\eta_p=1/\\delta_p$ & $\\tau_{\\mathrm{mix}}$ & $\\eta_{\\mathrm{pred}}$ & "
        "$\\eta_p/\\eta_{\\mathrm{pred}}$ & argmax $j$\\\\"
    )
    lines.append("\\midrule")
    for rr in rows:
        jtxt = ",\\ ".join([f"({a},{b},{c})" for (a, b, c) in (rr.argmax or [])]) if rr.argmax else "-"
        lines.append(
            f"{rr.p} & {rr.delta:.12f} & {rr.eta_gap:.3f} & {rr.tau_mix:.3f} & {rr.eta_pred:.3f} & {rr.eta_ratio:.6f} & ${jtxt}$\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tex.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[siegel-eta] wrote {tex}", flush=True)


if __name__ == "__main__":
    main()

