#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Addition-as-projection collision spectrum for sync10 vs real-input40.

We treat Zeckendorf addition as a deterministic transducer:
  - Input alphabet: bit pairs (x,y) in {0,1}^2 (4 symbols).
  - Output alphabet: normalized Zeckendorf bit e in {0,1}.

Two models:
  (A) sync10 (10-state normalization kernel) with unconstrained inputs (full shift on {0,1}^2).
  (B) real-input40 (40-state kernel) encoding the Zeckendorf legality constraints
      (no adjacent 11 in each input stream) as one-step memory in the state.

For each order q>=2, define the q-collision moment:
  S_q(m) := sum_{y} d_m(y)^q,
where d_m(y) is the number of length-m input words mapping to output word y.

By the paper's moment-kernel construction, S_q(m)=Theta(r_q^m) where r_q is the
Perron root of the q-collision moment-kernel A_q (a finite nonnegative matrix).

Outputs (default):
  - artifacts/export/sync_kernel_addition_collision_spectrum.json
  - sections/generated/tab_sync_kernel_addition_collision_spectrum.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Hashable, List, Sequence, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_moment_kernel_hist import (
    DeterministicTransducer,
    build_collision_moment_kernel_sparse,
    estimate_spectral_radius_sparse,
)
from exp_sync_kernel_real_input_40 import KERNEL_STATES, build_kernel_edges, build_kernel_map


InSym = Hashable
OutSym = Hashable


@dataclass(frozen=True)
class CollisionResult:
    model: str
    q: int
    r_q: float


def _dense_spectral_radius(rows: Sequence[List[Tuple[int, float]]]) -> float:
    n = len(rows)
    if n == 0:
        return 0.0
    A = np.zeros((n, n), dtype=np.float64)
    for i, row in enumerate(rows):
        for j, w in row:
            A[i, int(j)] = float(w)
    vals = np.linalg.eigvals(A)
    return float(np.max(np.abs(vals)))


def _build_sync10_add_transducer() -> DeterministicTransducer:
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)

    states = tuple(KERNEL_STATES)
    idx = {s: i for i, s in enumerate(states)}

    input_symbols: Tuple[InSym, ...] = ((0, 0), (0, 1), (1, 0), (1, 1))
    output_symbols: Tuple[OutSym, ...] = (0, 1)

    trans: Dict[Tuple[int, InSym], Tuple[int, OutSym]] = {}
    for s in states:
        for a in input_symbols:
            x, y = a  # type: ignore[misc]
            d = int(x) + int(y)
            s2, e = kernel_map[(s, d)]
            trans[(idx[s], a)] = (idx[s2], int(e))

    return DeterministicTransducer(
        states=states,
        input_symbols=input_symbols,
        output_symbols=output_symbols,
        trans=trans,
    )


def _build_real_input40_add_transducer() -> DeterministicTransducer:
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)

    # State = (sync_state, px, py) where px=x_{k-1}, py=y_{k-1}.
    base_states = tuple(KERNEL_STATES)
    states: List[Tuple[str, int, int]] = []
    for s in base_states:
        for px in (0, 1):
            for py in (0, 1):
                states.append((s, px, py))

    idx = {st: i for i, st in enumerate(states)}
    input_symbols: Tuple[InSym, ...] = ((0, 0), (0, 1), (1, 0), (1, 1))
    # We add a dummy output symbol "X" to encode illegal inputs and keep a total function.
    output_symbols: Tuple[OutSym, ...] = (0, 1, "X")

    trans: Dict[Tuple[int, InSym], Tuple[int, OutSym]] = {}
    for s, px, py in states:
        src = idx[(s, px, py)]
        for a in input_symbols:
            x, y = a  # type: ignore[misc]
            if (px == 1 and x == 1) or (py == 1 and y == 1):
                # Illegal under Zeckendorf input constraint: emit dummy symbol and stay put.
                trans[(src, a)] = (src, "X")
                continue
            d = int(x) + int(y)
            s2, e = kernel_map[(s, d)]
            dst = idx[(s2, int(x), int(y))]
            trans[(src, a)] = (dst, int(e))

    # Use stable, human-readable state labels for JSON readability (not used in math).
    state_names = tuple(f"{s},{px}{py}" for (s, px, py) in states)
    return DeterministicTransducer(
        states=state_names,
        input_symbols=input_symbols,
        output_symbols=output_symbols,
        trans=trans,
    )


def _compute_rq(
    transducer: DeterministicTransducer,
    *,
    q: int,
    output_symbols: Sequence[OutSym],
    use_dense: bool,
) -> Tuple[float, int]:
    _hst, rows = build_collision_moment_kernel_sparse(
        transducer,
        q,
        output_symbols=output_symbols,
        progress_every=0,
        lump_by_collision_counts=True,
    )
    n = len(rows)
    if use_dense:
        return _dense_spectral_radius(rows), n
    return estimate_spectral_radius_sparse(rows, iters=20000, tol=1e-14), n


def _write_tex_table(path: Path, results: Sequence[CollisionResult]) -> None:
    # Format results into a compact comparison table.
    r10_2 = next(r.r_q for r in results if r.model == "sync10_fullshift" and r.q == 2)
    r10_3 = next(r.r_q for r in results if r.model == "sync10_fullshift" and r.q == 3)
    r40_2 = next(r.r_q for r in results if r.model == "real_input40" and r.q == 2)
    ratio = r10_2 / r40_2 if r40_2 > 0 else float("nan")

    h2_10 = math.log((4.0**2) / r10_2)
    h3_10 = math.log((4.0**3) / r10_3)

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_addition_collision_spectrum.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Addition-as-projection collision spectrum for the sync10 normalization kernel (unconstrained inputs) "
        "versus the real-input40 kernel (Zeckendorf input constraint encoded as state memory). "
        "Here $r_q$ is the Perron root of the $q$-collision moment-kernel for the induced transducer "
        "$(x_k,y_k)\\mapsto e_k$. For the unconstrained model we also report $h_q=\\log(4^q/r_q)$.}"
    )
    lines.append("\\label{tab:sync-kernel-addition-collision-spectrum}")
    lines.append("\\begin{tabular}{l r r r r l}")
    lines.append("\\toprule")
    lines.append("model & $r_2$ & $r_3$ & $r_2$ ratio & $h_2$ & note\\\\")
    lines.append("\\midrule")
    lines.append(
        f"sync10 (full shift on $\\{{0,1\\}}^2$) & {r10_2:.12f} & {r10_3:.12f} & {ratio:.6f} & {h2_10:.12f} & $h_3={h3_10:.12f}$\\\\"
    )
    lines.append(
        f"real-input40 (Zeckendorf guard) & {r40_2:.12f} & --- & --- & --- & $q=2$ (real-input constraint encoded in state)\\\\"
    )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Addition-as-projection collision spectrum (sync10 vs real-input40).")
    parser.add_argument(
        "--no-output",
        action="store_true",
        help="Skip writing JSON/TeX outputs (still computes the constants).",
    )
    parser.add_argument(
        "--dense-eig",
        action="store_true",
        help="Use dense eigenvalue computation (fast for the small kernels here).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_addition_collision_spectrum.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_addition_collision_spectrum.tex"),
    )
    args = parser.parse_args()

    T10 = _build_sync10_add_transducer()
    T40 = _build_real_input40_add_transducer()

    results: List[CollisionResult] = []

    r2_10, n2_10 = _compute_rq(T10, q=2, output_symbols=[0, 1], use_dense=bool(args.dense_eig))
    r3_10, n3_10 = _compute_rq(T10, q=3, output_symbols=[0, 1], use_dense=bool(args.dense_eig))
    r2_40, n2_40 = _compute_rq(T40, q=2, output_symbols=[0, 1], use_dense=bool(args.dense_eig))

    results += [
        CollisionResult(model="sync10_fullshift", q=2, r_q=float(r2_10)),
        CollisionResult(model="sync10_fullshift", q=3, r_q=float(r3_10)),
        CollisionResult(model="real_input40", q=2, r_q=float(r2_40)),
    ]

    payload = {
        "results": [asdict(r) for r in results],
        "meta": {
            "sync10_hist_state_count_q2": int(n2_10),
            "sync10_hist_state_count_q3": int(n3_10),
            "real_input40_hist_state_count_q2": int(n2_40),
            "dense_eig": bool(args.dense_eig),
        },
    }

    if not args.no_output:
        jout = Path(args.json_out)
        jout.parent.mkdir(parents=True, exist_ok=True)
        jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

        _write_tex_table(Path(args.tex_out), results)

        print(f"[add-collision] wrote {jout}", flush=True)
        print(f"[add-collision] wrote {args.tex_out}", flush=True)

    # Small stdout summary (stable for CI logs).
    print(f"[add-collision] sync10 r2={r2_10:.12f} r3={r3_10:.12f}", flush=True)
    print(f"[add-collision] real-input40 r2={r2_40:.12f}", flush=True)


if __name__ == "__main__":
    main()

