#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Compute a 2D pressure surface P(k,u) for the sync10 collision moment-kernel.

We build a *weighted* collision moment-kernel A_k(u) on the histogram state space H_k
(symmetric quotient of Q^k), by assigning each base transducer transition a weight:

  w(q,a;u) = u^{E(q,a)},   with u in (0,1],

and enforcing output-collisions (all k tracks emit the same output symbol per step).

We then estimate:
  r_k(u) := rho(A_k(u)),
  P(k,u) := log r_k(u) - k log |A_out|.

This script is a minimal "executable surface" for the paper-side idea that the
moment-spectrum axis (k) and the temperature axis (u) can be unified as a single,
computable pressure surface.

Outputs (default):
  - artifacts/export/moment_pressure_surface_sync10.json
  - artifacts/export/moment_pressure_surface_sync10.png (if --plot and matplotlib available)
  - sections/generated/fig_moment_pressure_surface_sync10.tex (if --plot and matplotlib available)

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

try:
    import matplotlib.pyplot as plt
except Exception:  # pragma: no cover - optional plotting dependency
    plt = None  # type: ignore[assignment]

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from common_moment_kernel_hist import (
    DeterministicTransducer,
    build_collision_moment_kernel_sparse_weighted,
    build_transducer_from_edges,
    estimate_spectral_radius_sparse,
    histogram_state_count,
    pressure_from_rho,
)


def _parse_int_list(s: str) -> List[int]:
    out: List[int] = []
    for p in str(s).split(","):
        p = p.strip()
        if not p:
            continue
        out.append(int(p))
    return out


def _parse_float_list(s: str) -> List[float]:
    out: List[float] = []
    for p in str(s).split(","):
        p = p.strip()
        if not p:
            continue
        out.append(float(p))
    return out


def _sync10_transducer() -> DeterministicTransducer:
    # Reuse the audited edge list from the uniform-input fingerprint script.
    import exp_sync_kernel_10_state_uniform_input_fingerprint as sync10

    edges = sync10.build_edges()
    states = list(sync10.STATES)
    input_symbols = sorted({int(e.d) for e in edges})
    return build_transducer_from_edges(
        states=states,
        input_symbols=input_symbols,
        edges=edges,
        src_attr="src",
        dst_attr="dst",
        in_attr="d",
        out_attr="e",
    )


def _write_fig_tex(fig_name: str, png_rel: str, caption: str, label: str) -> None:
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


@dataclass(frozen=True)
class Row:
    k: int
    u: float
    dim_Hk: int
    rho_est: float
    pressure: float
    seconds_build: float
    seconds_power_iter: float


def main() -> None:
    ap = argparse.ArgumentParser(description="Compute pressure surface P(k,u) for sync10 collision moment-kernels.")
    ap.add_argument("--k-list", type=str, default="2,3,4,5,6", help="Comma list of moment orders k (>=1).")
    ap.add_argument("--u-grid", type=str, default="1,0.8,0.6,0.4,0.2", help="Comma list of u in (0,1].")
    ap.add_argument(
        "--energy",
        choices=["output", "input", "neg_state"],
        default="output",
        help="Edge energy E(q,a): output bit, input symbol, or 1_{dst has '-'}.",
    )
    ap.add_argument("--iters", type=int, default=2500, help="Power-iteration max iterations.")
    ap.add_argument("--tol", type=float, default=1e-13, help="Relative tolerance for power iteration.")
    ap.add_argument("--max-dim", type=int, default=50_000, help="Safety cap on |H_k| (use --force to override).")
    ap.add_argument("--force", action="store_true", help="Override --max-dim safety cap.")
    ap.add_argument("--plot", action="store_true", help="Write a PNG heatmap and a TeX include snippet (requires matplotlib).")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "moment_pressure_surface_sync10.json"),
        help="Output JSON path.",
    )
    ap.add_argument(
        "--png-out",
        type=str,
        default=str(export_dir() / "moment_pressure_surface_sync10.png"),
        help="Output PNG path (only when --plot).",
    )
    ap.add_argument(
        "--fig-tex-out",
        type=str,
        default=str(generated_dir() / "fig_moment_pressure_surface_sync10.tex"),
        help="Output TeX include path (only when --plot).",
    )
    args = ap.parse_args()

    k_list = sorted(set(_parse_int_list(args.k_list)))
    u_grid = sorted(set(_parse_float_list(args.u_grid)))
    if not k_list:
        raise SystemExit("Empty --k-list")
    if not u_grid:
        raise SystemExit("Empty --u-grid")
    if any(k < 1 for k in k_list):
        raise SystemExit("All k must be >= 1")
    for u in u_grid:
        if not (0.0 < float(u) <= 1.0) or (not math.isfinite(float(u))):
            raise SystemExit("All u must be finite and in (0,1]")

    T = _sync10_transducer()
    outA = int(len(T.output_symbols))
    if outA <= 1:
        raise SystemExit(f"Invalid output alphabet size: {outA}")

    # Dimension safety cap.
    dim_by_k: Dict[int, int] = {int(k): int(histogram_state_count(int(k), int(T.n_states()))) for k in k_list}
    worst_k = max(dim_by_k, key=lambda kk: dim_by_k[kk])
    worst_dim = dim_by_k[worst_k]
    if (not args.force) and worst_dim > int(args.max_dim):
        raise SystemExit(
            f"Safety cap: worst |H_k|={worst_dim} at k={worst_k} exceeds --max-dim={int(args.max_dim)}. "
            "Rerun with --force or reduce --k-list."
        )

    # Precompute integer energies per transition (state_idx, input_symbol) -> E >= 0.
    E: Dict[Tuple[int, object], int] = {}
    for (s, a), (s2, b) in T.trans.items():
        if str(args.energy) == "output":
            e = int(b)
        elif str(args.energy) == "input":
            e = int(a)  # input symbols are ints for sync10
        else:  # neg_state
            dst = str(T.states[int(s2)])
            e = 1 if ("-" in dst) else 0
        if e < 0:
            raise RuntimeError("internal error: negative energy")
        E[(int(s), a)] = int(e)

    prog = Progress(label="moment-surface-sync10", every_seconds=20.0)
    rows: List[Row] = []

    total_cases = len(k_list) * len(u_grid)
    case_i = 0
    t_global0 = time.time()
    for k in k_list:
        dim = dim_by_k[int(k)]
        for u in u_grid:
            case_i += 1
            prog.tick(f"case {case_i}/{total_cases}: k={k} u={u:.6g} |H_k|={dim}")

            def w_fn(state_idx: int, a_sym: object, *, _u: float = float(u)) -> float:
                ee = E[(int(state_idx), a_sym)]
                return float(_u**int(ee))

            t0 = time.time()
            _states, A_rows = build_collision_moment_kernel_sparse_weighted(T, k=int(k), weight_fn=w_fn)
            t1 = time.time()
            rho = float(estimate_spectral_radius_sparse(A_rows, iters=int(args.iters), tol=float(args.tol)))
            t2 = time.time()
            P = float(pressure_from_rho(float(rho), k=int(k), out_alphabet_size=outA))

            rows.append(
                Row(
                    k=int(k),
                    u=float(u),
                    dim_Hk=int(dim),
                    rho_est=float(rho),
                    pressure=float(P),
                    seconds_build=float(t1 - t0),
                    seconds_power_iter=float(t2 - t1),
                )
            )

    t_global1 = time.time()

    payload = {
        "kernel": "sync10",
        "energy": str(args.energy),
        "k_list": [int(k) for k in k_list],
        "u_grid": [float(u) for u in u_grid],
        "out_alphabet_size": int(outA),
        "params": {"iters": int(args.iters), "tol": float(args.tol)},
        "timing": {"seconds_total": float(t_global1 - t_global0)},
        "rows": [asdict(r) for r in rows],
        "notes": {
            "semantics": "Weighted collision moment-kernel on histogram state space H_k (symmetric quotient).",
            "pressure_definition": "P(k,u)=log rho(A_k(u)) - k log |A_out|.",
            "weight_definition": "w(q,a;u)=u^{E(q,a)} with E chosen by --energy.",
        },
    }

    out_json = Path(str(args.json_out))
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[moment-surface-sync10] wrote {out_json}", flush=True)

    if args.plot:
        if plt is None:
            raise SystemExit("--plot requested but matplotlib is not available")

        # Build a dense matrix for plotting: shape (len(k_list), len(u_grid)).
        idx_k = {int(k): i for i, k in enumerate(k_list)}
        idx_u = {float(u): j for j, u in enumerate(u_grid)}
        Z = [[float("nan") for _ in u_grid] for _ in k_list]
        for r in rows:
            Z[idx_k[int(r.k)]][idx_u[float(r.u)]] = float(r.pressure)

        fig, ax = plt.subplots(1, 1, figsize=(8.2, 4.6))
        im = ax.imshow(Z, aspect="auto", origin="lower")
        ax.set_xlabel("u (temperature weight)")
        ax.set_ylabel("k (moment order)")
        ax.set_xticks(list(range(len(u_grid))))
        ax.set_xticklabels([f"{u:.3g}" for u in u_grid])
        ax.set_yticks(list(range(len(k_list))))
        ax.set_yticklabels([str(k) for k in k_list])
        ax.set_title("sync10: pressure surface P(k,u)")
        cbar = fig.colorbar(im, ax=ax, fraction=0.046, pad=0.04)
        cbar.set_label("P(k,u)")
        plt.tight_layout()

        out_png = Path(str(args.png_out))
        out_png.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(out_png, dpi=180)
        plt.close(fig)
        print(f"[moment-surface-sync10] wrote {out_png}", flush=True)

        fig_tex_path = Path(str(args.fig_tex_out))
        _write_fig_tex(
            fig_name=fig_tex_path.stem,
            png_rel="artifacts/export/moment_pressure_surface_sync10.png",
            caption=(
                r"sync10 二维压力热图：加权碰撞 moment-kernel 的压力曲面。"
                r"每个格点报告 $P(q,u)=\log\rho(A_q(u)) - q\log|A_{\mathrm{out}}|$。"
            ),
            label="fig:moment-pressure-surface-sync10",
        )
        print(f"[moment-surface-sync10] wrote {fig_tex_path}", flush=True)

    print("[moment-surface-sync10] done", flush=True)


if __name__ == "__main__":
    main()

