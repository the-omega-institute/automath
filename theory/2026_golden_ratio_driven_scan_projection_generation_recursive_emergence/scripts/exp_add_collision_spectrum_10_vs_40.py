#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Addition-as-projection collision spectrum: 10-state vs real-input 40-state.

We build deterministic transducers for the map

  (x,y) ∈ {0,1}^Z × {0,1}^Z  ↦  Fold∞(x+y) ∈ X∞,

implemented by the 10-state sync-kernel (input digit d=x+y ∈ {0,1,2}, output bit e ∈ {0,1}).

Two variants:
1) unconstrained input: (x_t,y_t) ∈ {0,1}^2 i.i.d. (full 4-symbol input shift);
2) real input: (x_t) and (y_t) are Zeckendorf-legal (forbid '11' in each stream). This is
   encoded by a 40-state skew-product extension (kernel-state × previous input bits).

We then compute k-collision moment kernels A_k for output-collisions (all tracks emit the same
output symbol each step), and estimate r_k = rho(A_k) using histogram-DP + power iteration.

Outputs:
- artifacts/export/add_collision_spectrum_10_vs_40.json
- sections/generated/tab_add_collision_spectrum_10_vs_40.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Hashable, List, Mapping, Sequence, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from common_moment_kernel_hist import (
    DeterministicTransducer,
    build_collision_moment_kernel_sparse,
    estimate_spectral_radius_sparse,
)

from exp_sync_kernel_10_state_uniform_input_fingerprint import STATES as SYNC10_STATES
from exp_sync_kernel_10_state_uniform_input_fingerprint import build_edges as build_sync10_edges
from exp_sync_kernel_real_input_40 import build_kernel_edges, build_kernel_map, build_real_input_states

InSym = Tuple[int, int]
OutSym = Hashable

INPUT_PAIRS: Tuple[InSym, ...] = ((0, 0), (0, 1), (1, 0), (1, 1))


def _sync10_map() -> Dict[Tuple[str, int], Tuple[str, int]]:
    m: Dict[Tuple[str, int], Tuple[str, int]] = {}
    for e in build_sync10_edges():
        m[(e.src, int(e.d))] = (e.dst, int(e.e))
    # Sanity: deterministic total map for each state × digit.
    expected = len(SYNC10_STATES) * 3
    if len(m) != expected:
        raise RuntimeError(f"unexpected sync10 transition count: got {len(m)}, want {expected}")
    return m


def build_add_transducer_unconstrained() -> DeterministicTransducer:
    idx = {s: i for i, s in enumerate(SYNC10_STATES)}
    tmap = _sync10_map()
    trans: Dict[Tuple[int, InSym], Tuple[int, OutSym]] = {}
    for s in SYNC10_STATES:
        for a in INPUT_PAIRS:
            x, y = a
            d = int(x + y)
            s2, e = tmap[(s, d)]
            trans[(idx[s], a)] = (idx[s2], int(e))
    return DeterministicTransducer(
        states=tuple(SYNC10_STATES),
        input_symbols=tuple(INPUT_PAIRS),
        output_symbols=(0, 1),
        trans=trans,
    )


@dataclass(frozen=True)
class _Real40State:
    k: str
    px: int
    py: int

    def name(self) -> str:
        return f"{self.k}|{self.px}{self.py}"


def build_add_transducer_real_input_40(*, include_sink: bool = True) -> DeterministicTransducer:
    # Kernel map on sync10 states driven by digit d ∈ {0,1,2}.
    kmap = build_kernel_map(build_kernel_edges())  # (kernel_state, d) -> (next_kernel_state, out_bit)

    # Real-input (prev-bit) extension states.
    states40_raw = [_Real40State(k=s, px=int(px), py=int(py)) for (s, px, py) in build_real_input_states()]
    sink = "SINK"

    all_states: List[str] = [st.name() for st in states40_raw]
    if include_sink:
        all_states.append(sink)
    idx = {nm: i for i, nm in enumerate(all_states)}

    trans: Dict[Tuple[int, InSym], Tuple[int, OutSym]] = {}
    for st in states40_raw:
        src = st.name()
        for a in INPUT_PAIRS:
            x, y = a
            if (st.px == 1 and x == 1) or (st.py == 1 and y == 1):
                if not include_sink:
                    raise RuntimeError("include_sink=False is not supported for a total transducer")
                trans[(idx[src], a)] = (idx[sink], "BAD")
                continue
            d = int(x + y)
            k2, e = kmap[(st.k, d)]
            dst = _Real40State(k=k2, px=int(x), py=int(y)).name()
            trans[(idx[src], a)] = (idx[dst], int(e))

    if include_sink:
        for a in INPUT_PAIRS:
            trans[(idx[sink], a)] = (idx[sink], "BAD")

    # Determinism + completeness sanity.
    expected = len(all_states) * len(INPUT_PAIRS)
    if len(trans) != expected:
        raise RuntimeError(f"real40 transducer not total: got {len(trans)} transitions, want {expected}")

    return DeterministicTransducer(
        states=tuple(all_states),
        input_symbols=tuple(INPUT_PAIRS),
        output_symbols=(0, 1, "BAD") if include_sink else (0, 1),
        trans=trans,
    )


def _spectral_radius_collision(
    transducer: DeterministicTransducer,
    k: int,
    *,
    output_symbols: Sequence[OutSym] = (0, 1),
    iters: int = 8000,
    tol: float = 1e-13,
    lump: bool = True,
    prog: Progress | None = None,
) -> float:
    if prog is not None:
        prog.tick(f"build A_{k} histogram kernel (|Q|={transducer.n_states()})")
    _states, rows = build_collision_moment_kernel_sparse(
        transducer,
        k,
        output_symbols=output_symbols,
        lump_by_collision_counts=bool(lump),
    )
    if prog is not None:
        prog.tick(f"power-iterate rho(A_{k}) (n={len(rows)})")
    return float(estimate_spectral_radius_sparse(rows, iters=int(iters), tol=float(tol)))


def _fmt(x: float, digits: int = 12) -> str:
    return f"{x:.{digits}g}"


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _make_table(data: Mapping[str, Any]) -> str:
    # Keep it as an input-able LaTeX fragment.
    r2_u = float(data["unconstrained"]["r2"])
    r3_u = float(data["unconstrained"]["r3"])
    r2_r = float(data["real_input_40"]["r2"])

    # Derived (per-step) collision entropy rates under the full 4-symbol input baseline.
    # For q=2: H2/m = log(16/r2). For q=3: (1/2)log(64/r3).
    h2_u = math.log(16.0 / r2_u)
    h3_u = 0.5 * math.log(64.0 / r3_u)
    h2_r = math.log(16.0 / r2_r)

    ratio = r2_u / r2_r if r2_r > 0 else float("inf")

    lines: List[str] = []
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\small")
    lines.append(r"\setlength{\tabcolsep}{6pt}")
    lines.append(r"\renewcommand{\arraystretch}{1.15}")
    lines.append(
        r"\caption{加法作为一次投影的碰撞谱常数：无约束输入（10 状态同步核驱动）与真实输入约束（40 状态核）对比。"
        r"数值由脚本 \texttt{scripts/exp\_add\_collision\_spectrum\_10\_vs\_40.py} 生成。}"
    )
    lines.append(r"\label{tab:add-collision-spectrum-10-vs-40}")
    lines.append(r"\begin{tabular}{@{}lccc@{}}")
    lines.append(r"\toprule")
    lines.append(r"核/输入约束 & $r^{\mathrm{add}}_2$ & $r^{\mathrm{add}}_3$ & $\log(16/r^{\mathrm{add}}_2)$ \\")
    lines.append(r"\midrule")
    lines.append(
        r"$K_{\mathrm{sync}}$（无约束 $\{0,1\}^2$ 输入） & "
        + _fmt(r2_u, 12)
        + " & "
        + _fmt(r3_u, 12)
        + " & "
        + _fmt(h2_u, 12)
        + r" \\"
    )
    lines.append(
        r"$K_{\mathrm{real}}$（真实输入，$|\Sigma|=40$） & "
        + _fmt(r2_r, 12)
        + " & --- & "
        + _fmt(h2_r, 12)
        + r" \\"
    )
    lines.append(r"\midrule")
    lines.append(r"$r^{\mathrm{add}}_2$ 比值（sync/real） & \multicolumn{3}{c}{" + _fmt(ratio, 12) + r"} \\")
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute addition collision spectrum for sync10 vs real-input 40-state kernel")
    parser.add_argument(
        "--output-json",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/add_collision_spectrum_10_vs_40.json)",
    )
    parser.add_argument(
        "--output-tex",
        type=str,
        default="",
        help="Output TeX fragment path (default: sections/generated/tab_add_collision_spectrum_10_vs_40.tex)",
    )
    parser.add_argument("--no-tex", action="store_true", help="Do not write the TeX fragment")
    parser.add_argument("--iters", type=int, default=8000, help="Power iteration steps")
    parser.add_argument("--tol", type=float, default=1e-13, help="Power iteration relative tolerance")
    args = parser.parse_args()

    prog = Progress("add-collision-spectrum")

    trans_u = build_add_transducer_unconstrained()
    r2_u = _spectral_radius_collision(trans_u, 2, iters=args.iters, tol=args.tol, prog=prog)
    r3_u = _spectral_radius_collision(trans_u, 3, iters=args.iters, tol=args.tol, prog=prog)

    trans_r = build_add_transducer_real_input_40(include_sink=True)
    r2_r = _spectral_radius_collision(trans_r, 2, iters=args.iters, tol=args.tol, prog=prog)

    data: Dict[str, Any] = {
        "unconstrained": {
            "r2": r2_u,
            "r3": r3_u,
            "input_alphabet_size": 4,
            "states_kernel": trans_u.n_states(),
        },
        "real_input_40": {
            "r2": r2_r,
            "input_alphabet_size": 4,
            "states_kernel": 40,
            "states_transducer_total": trans_r.n_states(),
            "includes_sink_state_for_totality": True,
            "collision_output_symbols": [0, 1],
        },
        "notes": {
            "output_collision_symbols": [0, 1],
            "method": "histogram-DP moment-kernel + power iteration",
        },
    }

    out_json = Path(args.output_json) if args.output_json else (export_dir() / "add_collision_spectrum_10_vs_40.json")
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    prog.tick(f"wrote {out_json}")

    if not args.no_tex:
        out_tex = Path(args.output_tex) if args.output_tex else (generated_dir() / "tab_add_collision_spectrum_10_vs_40.tex")
        _write_text(out_tex, _make_table(data))
        prog.tick(f"wrote {out_tex}")


if __name__ == "__main__":
    main()

