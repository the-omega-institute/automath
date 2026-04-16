#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Window-6 block-collision and mixed-collision audit.

Outputs:
  - artifacts/export/window6_block_collision_audit.json
  - sections/generated/tab_window6_block_collision_audit.tex
"""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from itertools import product
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Sequence, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_window6_audit import trajectory, trajectory_modes, window6_data


Block = Tuple[int, ...]


def _quantize(y: np.ndarray, *, amplitude_bound: float, num_bins: int) -> np.ndarray:
    inner = np.linspace(-float(amplitude_bound), float(amplitude_bound), int(num_bins) + 1)[1:-1]
    q = np.digitize(y, inner, right=False)
    return np.clip(q.astype(np.int64), 0, int(num_bins) - 1)


def _empirical_distribution(samples: Iterable[int]) -> Dict[int, float]:
    counts = Counter(int(x) for x in samples)
    total = float(sum(counts.values()))
    return {int(k): float(v) / total for k, v in sorted(counts.items())}


def _block_distribution(sequences: Sequence[np.ndarray], ell: int) -> Dict[Block, float]:
    counts: Counter[Block] = Counter()
    total = 0
    for seq in sequences:
        limit = int(seq.size) - int(ell) + 1
        for start in range(limit):
            key = tuple(int(v) for v in seq[start : start + ell])
            counts[key] += 1
            total += 1
    if total <= 0:
        raise ValueError("empty block sample")
    return {k: float(v) / float(total) for k, v in counts.items()}


def _iid_block_distribution(one_body: Mapping[int, float], ell: int, num_bins: int) -> Dict[Block, float]:
    dist: Dict[Block, float] = {}
    for block in product(range(int(num_bins)), repeat=int(ell)):
        p = 1.0
        for x in block:
            p *= float(one_body.get(int(x), 0.0))
        if p > 0.0:
            dist[tuple(int(x) for x in block)] = float(p)
    return dist


def _collision(dist: Mapping[Block, float] | Mapping[int, float], q: float) -> float:
    return float(sum(float(v) ** float(q) for v in dist.values()))


def _mixed_collision(dist0: Mapping[Block, float], dist1: Mapping[Block, float], q: float) -> float:
    keys = set(dist0) | set(dist1)
    total = 0.0
    qq = float(q)
    for key in keys:
        total += (float(dist0.get(key, 0.0)) ** qq) * (float(dist1.get(key, 0.0)) ** qq)
    return float(total)


def _write_table_tex(
    path: Path,
    *,
    q_values: Sequence[int],
    ell_values: Sequence[int],
    delta_full: Dict[int, Dict[int, float]],
    xi_values: Dict[str, Dict[int, float]],
) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append("\\caption{Window-6 block-collision audit: selected block-gap and mixed-collision similarity values.}")
    lines.append("\\label{tab:window6_block_collision_audit}")
    lines.append("\\begin{tabular}{l r}")
    lines.append("\\toprule")
    lines.append("quantity & value\\\\")
    lines.append("\\midrule")
    for ell in ell_values:
        for q in q_values:
            lines.append(
                f"$\\Delta_{{{q}}}^{{({ell})}}(\\mathrm{{full}})$ & {delta_full[int(ell)][int(q)]:.6f}\\\\"
            )
    lines.append("\\midrule")
    for name, vals in xi_values.items():
        rhs = {
            "full_vs_iid": "\\mathrm{full},\\mathrm{iid}",
            "full_vs_visible_only": "\\mathrm{full},\\mathrm{vis}",
            "full_vs_visible_boundary": "\\mathrm{full},\\mathrm{vis+bdry}",
        }[name]
        for q in q_values:
            quantity = f"$\\Xi_{{{q}}}^{{(0,1)}}({rhs})$"
            lines.append(f"{quantity} & {vals[int(q)]:.6f}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit block collisions for the window-6 rough-visibility family.")
    ap.add_argument("--J", type=int, default=10, help="Truncation depth.")
    ap.add_argument("--a", type=float, default=0.72, help="Amplitude ratio.")
    ap.add_argument("--num-samples", type=int, default=1024, help="Samples per microstate trajectory.")
    ap.add_argument("--num-bins", type=int, default=12, help="Uniform quantization bins.")
    ap.add_argument("--ell-values", type=str, default="2,3,4", help="Comma-separated block lengths.")
    ap.add_argument("--q-values", type=str, default="2,3,4,6,8", help="Comma-separated q values.")
    ap.add_argument("--xi-ell", type=int, default=3, help="Block length used for Xi comparisons.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "window6_block_collision_audit.json"),
    )
    ap.add_argument(
        "--tex-tab-out",
        type=str,
        default=str(generated_dir() / "tab_window6_block_collision_audit.tex"),
    )
    args = ap.parse_args()

    ell_values = tuple(int(x) for x in args.ell_values.split(",") if x.strip())
    q_values = tuple(int(x) for x in args.q_values.split(",") if x.strip())
    if int(args.xi_ell) not in ell_values:
        raise SystemExit("xi-ell must be one of ell-values")

    wd = window6_data()
    t = np.linspace(0.0, 1.0, int(args.num_samples), endpoint=False)
    amplitude_bound = sum(float(args.a) ** float(j) for j in range(int(args.J) + 1))
    modes = trajectory_modes()

    sequences: Dict[str, List[np.ndarray]] = {mode: [] for mode in modes}
    one_body: Dict[str, Dict[int, float]] = {}
    block_dist: Dict[str, Dict[int, Dict[Block, float]]] = {mode: {} for mode in modes}

    for mode in modes:
        for n in range(1 << wd.m):
            y = trajectory(n, mode=mode, J=args.J, a=args.a, t=t, data=wd)
            sequences[mode].append(_quantize(y, amplitude_bound=amplitude_bound, num_bins=int(args.num_bins)))
        one_body[mode] = _empirical_distribution(np.concatenate(sequences[mode]))
        for ell in ell_values:
            block_dist[mode][int(ell)] = _block_distribution(sequences[mode], int(ell))

    iid_name = "iid_from_full_marginal"
    iid_one_body = one_body["full"]
    block_dist[iid_name] = {}
    for ell in ell_values:
        block_dist[iid_name][int(ell)] = _iid_block_distribution(iid_one_body, int(ell), int(args.num_bins))

    delta: Dict[str, Dict[int, Dict[int, float]]] = {mode: {} for mode in (*modes, iid_name)}
    for mode in (*modes, iid_name):
        col1 = {int(q): _collision(one_body["full"] if mode == iid_name else one_body[mode], int(q)) for q in q_values}
        for ell in ell_values:
            delta[mode][int(ell)] = {}
            for q in q_values:
                col_ell = _collision(block_dist[mode][int(ell)], int(q))
                delta[mode][int(ell)][int(q)] = float(math.log(col_ell) - float(ell) * math.log(col1[int(q)]))

    xi_pairs = {
        "full_vs_iid": ("full", iid_name),
        "full_vs_visible_only": ("full", "visible_only"),
        "full_vs_visible_boundary": ("full", "visible_boundary"),
    }
    xi: Dict[str, Dict[int, float]] = {}
    for name, (left, right) in xi_pairs.items():
        xi[name] = {}
        dist_left = block_dist[left][int(args.xi_ell)]
        dist_right = block_dist[right][int(args.xi_ell)]
        for q in q_values:
            num = _mixed_collision(dist_left, dist_right, int(q))
            den = math.sqrt(_mixed_collision(dist_left, dist_left, int(q)) * _mixed_collision(dist_right, dist_right, int(q)))
            xi[name][int(q)] = float(num / den if den > 0.0 else 0.0)

    preview_rep = wd.representative_microstates["boundary_upper"]
    preview = {mode: [int(v) for v in sequences[mode][preview_rep][:64]] for mode in modes}

    payload = {
        "window": 6,
        "parameters": {
            "J": int(args.J),
            "a": float(args.a),
            "num_samples": int(args.num_samples),
            "num_bins": int(args.num_bins),
            "ell_values": list(ell_values),
            "q_values": list(q_values),
            "xi_ell": int(args.xi_ell),
            "amplitude_bound": float(amplitude_bound),
        },
        "mode_order": list(modes) + [iid_name],
        "one_body_marginal": {
            mode: {str(k): float(v) for k, v in sorted(dist.items())}
            for mode, dist in {**one_body, iid_name: iid_one_body}.items()
        },
        "block_support_size": {
            mode: {str(ell): len(block_dist[mode][int(ell)]) for ell in ell_values}
            for mode in (*modes, iid_name)
        },
        "delta_q_ell": {
            mode: {
                str(ell): {str(q): float(delta[mode][int(ell)][int(q)]) for q in q_values}
                for ell in ell_values
            }
            for mode in (*modes, iid_name)
        },
        "xi_q": {name: {str(q): float(vals[int(q)]) for q in q_values} for name, vals in xi.items()},
        "preview_sequences": preview,
    }
    out_json = Path(args.json_out)
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    _write_table_tex(
        Path(args.tex_tab_out),
        q_values=q_values,
        ell_values=ell_values,
        delta_full=delta["full"],
        xi_values=xi,
    )

    print("[window6-block-collision] wrote JSON and TeX table artifacts", flush=True)


if __name__ == "__main__":
    main()
