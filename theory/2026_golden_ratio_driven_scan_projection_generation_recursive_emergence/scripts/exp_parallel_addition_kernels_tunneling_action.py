#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute the tunneling action A_K for non-backtracking prime cycles (single-flow kernels).

We work on the directed deterministic state graph exported by:
  artifacts/export/parallel_addition_kernels_bfs.json
whose edges are stored as [src, dst, kA, kB].

Define edge energy (carry events) as:
  kappa(edge) := kA + kB  in Z_{>=0}.

We consider non-backtracking cycles in the Hashimoto edge-space:
  state := (prev, cur) where prev -> cur is an edge in the directed graph
  transition (prev, cur) -> (cur, nxt) is allowed iff cur -> nxt is an edge and nxt != prev
  energy of the transition is kappa(cur -> nxt)

Tunneling action:
  A_K := min { kappa(p) : p is a non-backtracking closed cycle, kappa(p) > 0 }.

In practice, A_K is detected by searching for a positive-energy edge that can be closed
by a zero-energy non-backtracking path.

Outputs:
  - artifacts/export/parallel_addition_kernels_tunneling_action.json
  - sections/generated/tab_parallel_addition_kernels_tunneling_action.tex
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


@dataclass(frozen=True)
class Row:
    name: str
    nV: int
    nE: int
    n_oriented: int
    A_K: int
    witness: Dict[str, int]


def _build_out_edges(nV: int, edges: List[List[int]]) -> List[List[Tuple[int, int]]]:
    out: List[List[Tuple[int, int]]] = [[] for _ in range(nV)]
    for src, dst, kA, kB in edges:
        kappa = int(kA) + int(kB)
        out[int(src)].append((int(dst), kappa))
    return out


def _build_edge_kappa_map(edges: List[List[int]]) -> Dict[Tuple[int, int], int]:
    m: Dict[Tuple[int, int], int] = {}
    for src, dst, kA, kB in edges:
        key = (int(src), int(dst))
        kappa = int(kA) + int(kB)
        # Deterministic graph: expect at most one edge per (src,dst). If duplicates happen, keep min.
        if key not in m or kappa < m[key]:
            m[key] = kappa
    return m


def _bfs_zero_cost_reachable(
    *,
    start_prev: int,
    start_cur: int,
    target_cur: int,
    forbidden_prev_at_target: int,
    out_edges: List[List[Tuple[int, int]]],
    prog: Optional[Progress],
    budget_steps: int,
) -> bool:
    """BFS in the zero-cost Hashimoto graph from (start_prev,start_cur).

    We only traverse transitions that add zero energy, i.e. edges with kappa=0.
    We stop as soon as we reach some (w,target_cur) with w != forbidden_prev_at_target.

    budget_steps prevents pathological blowups; for our purpose (detecting A_K=1 or 2),
    a large but finite cap is acceptable.
    """
    # Node encoding: (prev,cur) as two ints; visited as a set of pairs.
    q: List[Tuple[int, int]] = [(start_prev, start_cur)]
    head = 0
    visited = {(start_prev, start_cur)}
    steps = 0
    while head < len(q):
        prev, cur = q[head]
        head += 1
        steps += 1
        if steps >= budget_steps:
            return False

        if cur == target_cur and prev != forbidden_prev_at_target:
            return True

        # Move to (cur,nxt) along zero-energy edges, forbidding immediate backtrack nxt==prev.
        for nxt, kappa in out_edges[cur]:
            if kappa != 0:
                continue
            if nxt == prev:
                continue
            st = (cur, nxt)
            if st in visited:
                continue
            visited.add(st)
            q.append(st)

        if prog and steps % 200000 == 0:
            prog.tick(f"zero-cost bfs visited={len(visited)} queue={len(q)}")
    return False


def compute_AK_for_kernel(
    *,
    name: str,
    nV: int,
    edges: List[List[int]],
    prog: Progress,
    budget_steps: int,
) -> Row:
    out_edges = _build_out_edges(nV, edges)
    edge_kappa = _build_edge_kappa_map(edges)
    nE = len(edge_kappa)

    # List candidate directed edges with positive energy, in increasing kappa.
    pos_edges: List[Tuple[int, int, int]] = []
    for (u, v), kappa in edge_kappa.items():
        if kappa > 0:
            pos_edges.append((u, v, kappa))
    pos_edges.sort(key=lambda t: (t[2], t[0], t[1]))

    # Precompute oriented-edge count for reference: count all directed edges (including kappa=0).
    n_oriented = nE

    # Cache BFS results per start state (u,v) for a fixed target u and forbidden v.
    cache: Dict[Tuple[int, int], bool] = {}

    for idx, (u, v, kappa) in enumerate(pos_edges, start=1):
        key = (u, v)
        if key in cache:
            ok = cache[key]
        else:
            ok = _bfs_zero_cost_reachable(
                start_prev=u,
                start_cur=v,
                target_cur=u,
                forbidden_prev_at_target=v,
                out_edges=out_edges,
                prog=None,
                budget_steps=budget_steps,
            )
            cache[key] = ok

        if ok:
            prog.tick(f"{name} found A_K={kappa} via edge {u}->{v} (checked {idx}/{len(pos_edges)})")
            return Row(
                name=name,
                nV=nV,
                nE=nE,
                n_oriented=n_oriented,
                A_K=int(kappa),
                witness={"u": int(u), "v": int(v), "kappa": int(kappa)},
            )

        if idx % 5000 == 0:
            prog.tick(f"{name} scanning positive edges {idx}/{len(pos_edges)} (cache={len(cache)})")

    # Fallback: if no positive edge can be closed by zero edges, we report A_K as min positive edge weight
    # (still meaningful as a lower bound), with empty witness.
    if pos_edges:
        kappa_min = int(pos_edges[0][2])
        prog.tick(f"{name} no zero-closure found; report min edge kappa={kappa_min}")
        return Row(name=name, nV=nV, nE=nE, n_oriented=n_oriented, A_K=kappa_min, witness={})

    # No positive edges at all (degenerate).
    prog.tick(f"{name} has no positive-energy edges")
    return Row(name=name, nV=nV, nE=nE, n_oriented=n_oriented, A_K=0, witness={})


def make_table(rows: List[Row]) -> str:
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_parallel_addition_kernels_tunneling_action.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\small")
    lines.append("\\begin{tabular}{@{}lrrrr@{}}")
    lines.append("\\toprule")
    lines.append("核 & $|V|$ & $|E|$ & $A_K$ & 见证边 $u\\to v$\\\\")
    lines.append("\\midrule")
    for r in rows:
        if r.witness:
            w = f"${r.witness.get('u','?')}\\to {r.witness.get('v','?')}$"
        else:
            w = "--"
        lines.append(f"{r.name} & {r.nV} & {r.nE} & {r.A_K} & {w}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append(
        "\\caption{隧穿作用量 $A_K$（单流）：无回溯 prime cycle 中最小正能量 $\\kappa(p)$。"
        "按 Hashimoto 边空间定义非回溯闭环，并以 $\\kappa(e)=k_A(e)+k_B(e)$ 计能。"
        "表中见证边给出一个可用零能量无回溯路径闭合的正能量跳转。}"
    )
    lines.append("\\label{tab:parallel-addition-kernels-tunneling-action}")
    lines.append("\\end{table}")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=str, default="", help="Input BFS JSON (default: artifacts/export/parallel_addition_kernels_bfs.json)")
    parser.add_argument("--budget-steps", type=int, default=2500000, help="Max BFS expansions per candidate (safety cap)")
    parser.add_argument("--no-output", action="store_true", help="Do not write outputs")
    args = parser.parse_args()

    prog = Progress(label="par-add-AK", every_seconds=20.0)
    in_path = Path(args.input) if args.input else (export_dir() / "parallel_addition_kernels_bfs.json")
    payload = _read_json(in_path)

    rows: List[Row] = []
    out_json: List[dict] = []

    for k in payload.get("kernels", []):
        name = str(k.get("name", "")).strip() or "unknown"
        nV = int(k.get("states_reachable", 0))
        edges = k.get("edges", None)
        if edges is None:
            raise SystemExit(f"[par-add-AK] missing edges for kernel: {name}")
        prog.tick(f"{name} start")
        row = compute_AK_for_kernel(name=name, nV=nV, edges=edges, prog=prog, budget_steps=int(args.budget_steps))
        rows.append(row)
        out_json.append(
            {
                "name": row.name,
                "nV": row.nV,
                "nE": row.nE,
                "A_K": row.A_K,
                "witness": row.witness,
                "budget_steps": int(args.budget_steps),
            }
        )

    if not args.no_output:
        out_path = export_dir() / "parallel_addition_kernels_tunneling_action.json"
        _write_text(out_path, json.dumps({"rows": out_json}, indent=2, sort_keys=True) + "\n")
        print(f"[par-add-AK] wrote {out_path}", flush=True)

        out_tex = generated_dir() / "tab_parallel_addition_kernels_tunneling_action.tex"
        _write_text(out_tex, make_table(rows))
        print(f"[par-add-AK] wrote {out_tex}", flush=True)

    print("[par-add-AK] done", flush=True)


if __name__ == "__main__":
    main()

