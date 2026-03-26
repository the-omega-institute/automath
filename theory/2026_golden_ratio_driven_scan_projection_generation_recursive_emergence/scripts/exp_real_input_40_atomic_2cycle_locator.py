#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Enumerate all length-2 branch-cycles with total output E=1 in the real-input
40-state kernel (output potential u = exp(theta_e)).

Here we treat each admissible input pair (x,y) as a separate branch, so that a
2-step loop corresponds to an explicit pair of transitions labelled by
  (x0,y0) then (x1,y1),
with accumulated output E = e0 + e1.

This provides a concrete, script-auditable list of all (|tau|,E)=(2,1) loops in
the (x,y)-branch graph induced by the 40-state construction.

Outputs:
  - artifacts/export/real_input_40_atomic_2cycle.json
  - sections/generated/eq_real_input_40_atomic_2cycle_states.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

from common_paths import export_dir, generated_dir


KERNEL_STATES = [
    "000",
    "001",
    "002",
    "010",
    "100",
    "101",
    "0-12",
    "1-12",
    "01-1",
    "11-1",
]


@dataclass(frozen=True)
class KernelEdge:
    src: str
    dst: str
    d: int
    e: int


def build_kernel_edges() -> List[KernelEdge]:
    edges: List[KernelEdge] = []
    for d in (0, 1, 2):
        edges.append(KernelEdge("000", f"00{d}", d, 0))
    for d in (0, 1, 2):
        edges.append(KernelEdge("100", f"00{d}", d, 1))
    edges += [
        KernelEdge("001", "010", 0, 0),
        KernelEdge("001", "100", 1, 0),
        KernelEdge("001", "101", 2, 0),
        KernelEdge("002", "11-1", 0, 0),
        KernelEdge("002", "000", 1, 1),
        KernelEdge("002", "001", 2, 1),
        KernelEdge("010", "100", 0, 0),
        KernelEdge("010", "101", 1, 0),
        KernelEdge("010", "0-12", 2, 1),
        KernelEdge("101", "010", 0, 1),
        KernelEdge("101", "100", 1, 1),
        KernelEdge("101", "101", 2, 1),
        KernelEdge("0-12", "01-1", 0, 0),
        KernelEdge("0-12", "010", 1, 0),
        KernelEdge("0-12", "100", 2, 0),
        KernelEdge("1-12", "01-1", 0, 1),
        KernelEdge("1-12", "010", 1, 1),
        KernelEdge("1-12", "100", 2, 1),
        KernelEdge("01-1", "001", 0, 0),
        KernelEdge("01-1", "002", 1, 0),
        KernelEdge("01-1", "1-12", 2, 0),
        KernelEdge("11-1", "001", 0, 1),
        KernelEdge("11-1", "002", 1, 1),
        KernelEdge("11-1", "1-12", 2, 1),
    ]
    return edges


def build_kernel_map(edges: Sequence[KernelEdge]) -> Dict[Tuple[str, int], Tuple[str, int]]:
    return {(edge.src, edge.d): (edge.dst, edge.e) for edge in edges}


def build_real_input_states() -> List[Tuple[str, int, int]]:
    out: List[Tuple[str, int, int]] = []
    for s in KERNEL_STATES:
        for px in (0, 1):
            for py in (0, 1):
                out.append((s, px, py))
    return out


@dataclass(frozen=True)
class Step:
    src_idx: int
    dst_idx: int
    src_state: Tuple[str, int, int]
    dst_state: Tuple[str, int, int]
    x: int
    y: int
    d: int
    e: int


def outgoing_steps(
    states: Sequence[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
    i: int,
) -> List[Step]:
    s, px, py = states[i]
    out: List[Step] = []
    for x in (0, 1):
        if px == 1 and x == 1:
            continue
        for y in (0, 1):
            if py == 1 and y == 1:
                continue
            d = x + y
            dst_s, e = kernel_map[(s, d)]
            dst = (dst_s, x, y)
            j = states_index[dst]
            out.append(
                Step(
                    src_idx=i,
                    dst_idx=j,
                    src_state=states[i],
                    dst_state=dst,
                    x=x,
                    y=y,
                    d=d,
                    e=e,
                )
            )
    return out


@dataclass(frozen=True)
class Payload:
    orbit_count_len2_E1: int
    oriented_count_len2_E1: int
    orbits: List[dict]


def step_to_dict(s: Step) -> dict:
    return {
        "src_idx": s.src_idx,
        "dst_idx": s.dst_idx,
        "src_state": list(s.src_state),
        "dst_state": list(s.dst_state),
        "x": s.x,
        "y": s.y,
        "d": s.d,
        "e": s.e,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Locate the atomic (2,1) primitive orbit in real-input-40.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_atomic_2cycle.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_real_input_40_atomic_2cycle_states.tex"),
    )
    args = parser.parse_args()

    kernel_map = build_kernel_map(build_kernel_edges())
    states = build_real_input_states()

    global states_index
    states_index = {st: i for i, st in enumerate(states)}

    out_steps: List[List[Step]] = [outgoing_steps(states, kernel_map, i) for i in range(len(states))]

    # Enumerate all oriented 2-cycles i->j->i, i!=j, and keep E=1.
    oriented: List[Tuple[Step, Step]] = []
    for i in range(len(states)):
        for s1 in out_steps[i]:
            j = s1.dst_idx
            if j == i:
                continue
            for s2 in out_steps[j]:
                if s2.dst_idx != i:
                    continue
                if s1.e + s2.e == 1:
                    oriented.append((s1, s2))

    def orbit_key(s1: Step, s2: Step) -> Tuple:
        # Canonicalize up to cyclic rotation (swap the two steps).
        a = (s1.src_state, s1.x, s1.y, s1.dst_state, s2.x, s2.y)
        b = (s2.src_state, s2.x, s2.y, s2.dst_state, s1.x, s1.y)
        return a if a <= b else b

    orbits: Dict[Tuple, Tuple[Step, Step]] = {}
    for s1, s2 in oriented:
        orbits.setdefault(orbit_key(s1, s2), (s1, s2))

    # Deterministic expectation (audited separately in the paper's unweighted primitive table):
    # p_2(1)=7, and in this u-weighting p_2(u) has coefficient 7 at u^1, hence 7 distinct (2,1) loops.
    if len(orbits) != 7:
        raise SystemExit(f"Expected 7 distinct (len=2,E=1) orbits, got {len(orbits)}.")

    payload = Payload(
        orbit_count_len2_E1=len(orbits),
        oriented_count_len2_E1=len(oriented),
        orbits=[
            {"step1": step_to_dict(s1), "step2": step_to_dict(s2)}
            for _, (s1, s2) in sorted(orbits.items(), key=lambda kv: str(kv[0]))
        ],
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[atomic-2cycle] wrote {jout}", flush=True)

    # TeX snippet (English-only prose).
    def fmt_state(st: Tuple[str, int, int]) -> str:
        s, px, py = st
        # In TeX text mode, '_' must be escaped.
        return f"({s};p\\_x={px},p\\_y={py})"

    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_real_input_40_atomic_2cycle_locator.py")
    lines.append("\\begin{equation*}")
    lines.append(
        "\\boxed{\\ \\text{Branch-level }(|\\tau|,E)=(2,1)\\text{ loops: count }=7\\ }"
    )
    lines.append("\\end{equation*}")
    lines.append("\\noindent Each loop is a 2-step cycle in the (x,y)-branch graph (u-weights via edge-output e).")
    lines.append("\\begin{align*}")
    for k, item in enumerate(payload.orbits, start=1):
        s1 = item["step1"]
        s2 = item["step2"]

        lines.append(f"&\\textbf{{(\\#{k})}}\\quad\\begin{{aligned}}[t]")
        lines.append(
            "v_0&="
            + f"\\text{{{fmt_state(tuple(s1['src_state']))}}}\\ (\\# {s1['src_idx']})\\\\"
        )
        lines.append(
            "&\\xrightarrow{(x,y)="
            + f"({s1['x']},{s1['y']}),\\ d={s1['d']},\\ e={s1['e']}"
            + "} "
            + "v_1="
            + f"\\text{{{fmt_state(tuple(s1['dst_state']))}}}\\ (\\# {s1['dst_idx']})\\\\"
        )
        lines.append(
            "&\\xrightarrow{(x,y)="
            + f"({s2['x']},{s2['y']}),\\ d={s2['d']},\\ e={s2['e']}"
            + "} "
            + "v_0="
            + f"\\text{{{fmt_state(tuple(s2['dst_state']))}}}\\ (\\# {s2['dst_idx']}),\\ \\ E=1."
        )
        lines.append("\\end{aligned}\\\\[4pt]")
    lines.append("\\end{align*}")
    lines.append("")

    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[atomic-2cycle] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

