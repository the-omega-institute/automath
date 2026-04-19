#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Window-6 rough-visibility audit.

Outputs:
  - artifacts/export/window6_rough_visibility_audit.json
  - sections/generated/tab_window6_rough_visibility_audit.tex
"""

from __future__ import annotations

import argparse
import json
from itertools import combinations
from pathlib import Path
from typing import Dict, List, Sequence

import numpy as np

from common_paths import export_dir, generated_dir
from common_window6_audit import trajectory, trajectory_modes, window6_data


def _display_name(mode: str) -> str:
    mapping = {
        "visible_only": "visible only",
        "visible_boundary": "visible + boundary",
        "full": "visible + boundary + ledger",
    }
    return mapping.get(mode, mode)


def _dyadic_oscillation(y: np.ndarray, depth: int) -> float:
    blocks = 1 << int(depth)
    step = y.size // blocks
    if step < 2:
        raise ValueError("sampling grid too coarse for requested dyadic depth")
    osc = 0.0
    for r in range(blocks):
        seg = y[r * step : (r + 1) * step]
        osc = max(osc, float(np.max(seg) - np.min(seg)))
    return float(osc)


def _p_variation(y: np.ndarray, p: float) -> float:
    diff = np.abs(np.diff(y))
    return float(np.sum(diff**float(p)))


def _summary_stats(values: Sequence[float]) -> Dict[str, float]:
    arr = np.asarray(values, dtype=np.float64)
    return {
        "mean": float(np.mean(arr)),
        "std": float(np.std(arr)),
        "min": float(np.min(arr)),
        "max": float(np.max(arr)),
    }


def _write_table_tex(
    path: Path,
    *,
    depths: Sequence[int],
    p_values: Sequence[float],
    osc_summary: Dict[str, Dict[int, Dict[str, float]]],
    pvar_summary: Dict[str, Dict[float, Dict[str, float]]],
    pairwise_sup: Dict[str, Dict[str, float]],
) -> None:
    depth_headers = " & ".join([f"$\\mathrm{{Osc}}_{{J,{d}}}$" for d in depths])
    p_headers = " & ".join([f"$V_{{{p:g}}}$" for p in p_values])
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append("\\caption{Window-6 rough-visibility audit: mean dyadic oscillation, mean discrete $p$-variation, and pairwise sup-norm separation proxies over all microstates.}")
    lines.append("\\label{tab:window6_rough_visibility_audit}")
    lines.append("\\begin{tabular}{l " + " ".join(["r"] * (len(depths) + len(p_values) + 1)) + "}")
    lines.append("\\toprule")
    lines.append(f"mode & {depth_headers} & {p_headers} & pairwise $\\|\\cdot\\|_\\infty$ mean\\\\")
    lines.append("\\midrule")
    sup_mean = {mode: "" for mode in trajectory_modes()}
    for key, stats in pairwise_sup.items():
        left, right = key.split("__vs__")
        sup_mean[right] = f"vs {_display_name(left)}: {stats['mean']:.6f}"
    for mode in trajectory_modes():
        osc_cells = " & ".join([f"{osc_summary[mode][int(d)]['mean']:.6f}" for d in depths])
        p_cells = " & ".join([f"{pvar_summary[mode][float(p)]['mean']:.6f}" for p in p_values])
        lines.append(f"{_display_name(mode)} & {osc_cells} & {p_cells} & {sup_mean[mode]}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit rough visible trajectories for the window-6 example.")
    ap.add_argument("--J", type=int, default=10, help="Truncation depth.")
    ap.add_argument("--a", type=float, default=0.72, help="Amplitude ratio.")
    ap.add_argument("--num-samples", type=int, default=4096, help="Number of samples on [0,1).")
    ap.add_argument("--depths", type=str, default="4,6,8", help="Comma-separated dyadic depths.")
    ap.add_argument("--p-values", type=str, default="1.5,2.0,3.0", help="Comma-separated p values.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "window6_rough_visibility_audit.json"),
    )
    ap.add_argument(
        "--tex-tab-out",
        type=str,
        default=str(generated_dir() / "tab_window6_rough_visibility_audit.tex"),
    )
    args = ap.parse_args()

    depths = tuple(int(x) for x in args.depths.split(",") if x.strip())
    p_values = tuple(float(x) for x in args.p_values.split(",") if x.strip())
    if args.num_samples <= (1 << max(depths)):
        raise SystemExit("num-samples must exceed the finest dyadic partition size")

    wd = window6_data()
    t = np.linspace(0.0, 1.0, int(args.num_samples), endpoint=False)
    modes = trajectory_modes()
    traces: Dict[str, Dict[int, np.ndarray]] = {mode: {} for mode in modes}

    for mode in modes:
        for n in range(1 << wd.m):
            traces[mode][n] = trajectory(n, mode=mode, J=args.J, a=args.a, t=t, data=wd)

    osc_summary: Dict[str, Dict[int, Dict[str, float]]] = {mode: {} for mode in modes}
    pvar_summary: Dict[str, Dict[float, Dict[str, float]]] = {mode: {} for mode in modes}
    pairwise_sup: Dict[str, Dict[str, float]] = {}

    for mode in modes:
        for depth in depths:
            vals = [_dyadic_oscillation(traces[mode][n], depth) for n in range(1 << wd.m)]
            osc_summary[mode][int(depth)] = _summary_stats(vals)
        for p in p_values:
            vals = [_p_variation(traces[mode][n], p) for n in range(1 << wd.m)]
            pvar_summary[mode][float(p)] = _summary_stats(vals)

    for left, right in combinations(modes, 2):
        key = f"{left}__vs__{right}"
        vals = [float(np.max(np.abs(traces[left][n] - traces[right][n]))) for n in range(1 << wd.m)]
        pairwise_sup[key] = _summary_stats(vals)

    rep_n = wd.representative_microstates["boundary_upper"]
    representative = {
        "microstate": int(rep_n),
        "bits": format(int(rep_n), f"0{wd.m}b"),
        "stable_word": next(w for w, ns in wd.preimages.items() if rep_n in ns),
        "zoom_window": [0.125, 0.25],
    }
    rep_traces = {mode: traces[mode][rep_n] for mode in modes}

    payload = {
        "window": 6,
        "parameters": {
            "J": int(args.J),
            "a": float(args.a),
            "num_samples": int(args.num_samples),
            "depths": list(depths),
            "p_values": list(p_values),
        },
        "representative": representative,
        "mode_order": list(modes),
        "oscillation_summary": {
            mode: {str(depth): osc_summary[mode][int(depth)] for depth in depths} for mode in modes
        },
        "p_variation_summary": {
            mode: {f"{p:g}": pvar_summary[mode][float(p)] for p in p_values} for mode in modes
        },
        "pairwise_supnorm_summary": pairwise_sup,
        "representative_trace_preview": {
            mode: {
                "t": [float(v) for v in t[::64]],
                "y": [float(v) for v in rep_traces[mode][::64]],
            }
            for mode in modes
        },
    }
    out_json = Path(args.json_out)
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    _write_table_tex(
        Path(args.tex_tab_out),
        depths=depths,
        p_values=p_values,
        osc_summary=osc_summary,
        pvar_summary=pvar_summary,
        pairwise_sup=pairwise_sup,
    )

    print("[window6-rough-visibility] wrote JSON and TeX table artifacts", flush=True)


if __name__ == "__main__":
    main()
