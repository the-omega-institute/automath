#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit: holonomy accumulation path-independence for the E/LIFT swap.

This script exercises the projection-word normalizer in two different
rewrite-priority strategies and checks whether:
  - normal forms match
  - accumulated holonomy (sum of swap certificates) matches

This is the executable form of the "swap failure -> residual -> signature"
holonomy/cocycle prediction discussed in the manuscript.

Outputs (default):
  - artifacts/export/pom_holonomy_cocycle_audit.json

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir

import exp_pom_projword_lift_proj_normalizer_demo as lp


@dataclass(frozen=True)
class Case:
    word: str
    nf1: str
    nf2: str
    hol1: Dict[str, int]
    hol2: Dict[str, int]
    steps1: int
    steps2: int


def _parse_int_list(s: str) -> List[int]:
    out: List[int] = []
    for p in str(s).split(","):
        p = p.strip()
        if not p:
            continue
        out.append(int(p))
    return out


def random_word(
    rng: random.Random,
    *,
    length: int,
    m_max: int,
    group_orders: List[int],
    pz_prob: float,
    proj_prob: float,
) -> str:
    toks: List[str] = []
    for _ in range(length):
        u = rng.random()
        if u < pz_prob:
            toks.append("PZ")
            continue
        if u < pz_prob + proj_prob:
            toks.append("PROJ[u]")
            continue
        # remaining mass: E or LIFT
        if rng.random() < 0.55:
            m = rng.randint(1, max(1, int(m_max)))
            toks.append(f"E{m}")
        else:
            n = rng.choice(group_orders) if group_orders else 3
            n = max(1, int(n))
            toks.append(f"LIFT[C{n}]")
    return " ".join(toks)


def run(
    *,
    samples: int,
    seed: int,
    min_len: int,
    max_len: int,
    m_max: int,
    group_orders: List[int],
    pz_prob: float,
    proj_prob: float,
    keep: int,
) -> Tuple[dict, List[Case]]:
    rng = random.Random(int(seed))
    nf_mismatches: List[Case] = []
    hol_mismatches: List[Case] = []

    for _ in range(int(samples)):
        L = rng.randint(int(min_len), int(max_len))
        w = random_word(
            rng,
            length=L,
            m_max=m_max,
            group_orders=group_orders,
            pz_prob=float(pz_prob),
            proj_prob=float(proj_prob),
        )
        toks = lp.parse_word(w)

        nf1, tr1, hol1, _certs1 = lp.normalize_with_holonomy(toks, strategy="tower_first")
        nf2, tr2, hol2, _certs2 = lp.normalize_with_holonomy(toks, strategy="swap_first")

        s_nf1 = lp.word_to_str(nf1)
        s_nf2 = lp.word_to_str(nf2)
        case = Case(
            word=w,
            nf1=s_nf1,
            nf2=s_nf2,
            hol1=hol1,
            hol2=hol2,
            steps1=len(tr1),
            steps2=len(tr2),
        )
        if s_nf1 != s_nf2:
            if len(nf_mismatches) < int(keep):
                nf_mismatches.append(case)
            continue
        if hol1 != hol2:
            if len(hol_mismatches) < int(keep):
                hol_mismatches.append(case)

    summary = {
        "samples": int(samples),
        "seed": int(seed),
        "word_len": {"min": int(min_len), "max": int(max_len)},
        "m_max": int(m_max),
        "group_orders": [int(x) for x in group_orders],
        "pz_prob": float(pz_prob),
        "proj_prob": float(proj_prob),
        "nf_mismatch_count": int(len(nf_mismatches)),
        "holonomy_mismatch_count": int(len(hol_mismatches)),
    }
    # If NF mismatches exist, holonomy mismatches are less meaningful; still report both.
    return summary, (nf_mismatches + hol_mismatches)


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit holonomy cocycle: compare two rewrite strategies.")
    ap.add_argument("--samples", type=int, default=500)
    ap.add_argument("--seed", type=int, default=20260205)
    ap.add_argument("--min-len", type=int, default=6)
    ap.add_argument("--max-len", type=int, default=22)
    ap.add_argument("--m-max", type=int, default=12, help="Max m for E[m] tokens.")
    ap.add_argument("--group-orders", type=str, default="2,3,4,5", help="Comma list for cyclic group orders in LIFT[Cn].")
    ap.add_argument("--pz-prob", type=float, default=0.15, help="Per-token probability of PZ.")
    ap.add_argument("--proj-prob", type=float, default=0.10, help="Per-token probability of PROJ[u].")
    ap.add_argument("--keep", type=int, default=8, help="Max mismatch cases to keep in JSON.")
    ap.add_argument(
        "--output",
        type=str,
        default=str(export_dir() / "pom_holonomy_cocycle_audit.json"),
        help="Output JSON path.",
    )
    args = ap.parse_args()

    group_orders = _parse_int_list(args.group_orders)
    summary, cases = run(
        samples=int(args.samples),
        seed=int(args.seed),
        min_len=int(args.min_len),
        max_len=int(args.max_len),
        m_max=int(args.m_max),
        group_orders=group_orders,
        pz_prob=float(args.pz_prob),
        proj_prob=float(args.proj_prob),
        keep=int(args.keep),
    )

    payload = {
        "summary": summary,
        "cases": [
            {
                "word": c.word,
                "nf_tower_first": c.nf1,
                "nf_swap_first": c.nf2,
                "hol_tower_first": c.hol1,
                "hol_swap_first": c.hol2,
                "steps_tower_first": c.steps1,
                "steps_swap_first": c.steps2,
            }
            for c in cases
        ],
    }
    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(
        f"[pom-holonomy-cocycle] samples={summary['samples']} "
        f"nf_mismatch={summary['nf_mismatch_count']} hol_mismatch={summary['holonomy_mismatch_count']}",
        flush=True,
    )
    print(f"[pom-holonomy-cocycle] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

