#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Local conjugacy threshold check for Phi_m = Fold_m sliding-block factor.

We use the subset-filter (power-set) automaton induced by the labeled graph G_m:
  - Start state is the full vertex set V_m (unknown (m-1)-suffix).
  - On reading an output symbol a in X_m, the filter updates by
      S' = { v' : exists edge v->v' with label a, with v in S }.

Key finite check (per fixed m):
  If all reachable filter states after exactly m output symbols are singletons,
  then every length-m output word determines a unique length-(2m-1) input block.
  Combined with left-resolving of G_m, this yields a sliding-block inverse for Phi_m
  with memory (m-1) and anticipation 0 (hence Phi_m is a topological conjugacy
  onto its image Y_m).

This script generates a small, auditable certificate table for m in a range.

Outputs (English-only, reproducible artifacts):
  - artifacts/export/phi_m_conjugacy_threshold.json
  - sections/generated/tab_phi_m_conjugacy_threshold.tex
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Set, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fold_m


def _int_to_bits(x: int, m: int) -> List[int]:
    return [(x >> (m - 1 - i)) & 1 for i in range(m)]


def _pack_bits_to_int(bits: Iterable[int], m: int) -> int:
    x = 0
    for b in bits:
        x = (x << 1) | (1 if b else 0)
    return x & ((1 << m) - 1)


def build_fold_map(m: int, prog: Progress) -> List[int]:
    size = 1 << m
    out = [0] * size
    for w in range(size):
        bits = _int_to_bits(w, m)
        folded = fold_m(bits)
        out[w] = _pack_bits_to_int(folded, m)
        prog.tick(f"build_fold_map m={m} w={w}/{size}")
    return out


def build_Gm_edges(m: int, fold_map: List[int]) -> Tuple[int, List[Dict[int, int]]]:
    """Return (num_vertices, trans[v][label] = bitmask-of-target-vertices)."""
    if m <= 1:
        nV = 1
    else:
        nV = 1 << (m - 1)
    maskV = nV - 1

    trans: List[Dict[int, int]] = [dict() for _ in range(nV)]
    for v in range(nV):
        for b in (0, 1):
            if m <= 1:
                window = b
                tgt = 0
            else:
                window = ((v << 1) | b) & ((1 << m) - 1)
                tgt = ((v << 1) | b) & maskV
            a = fold_map[window] if m >= 1 else 0
            trans[v][a] = trans[v].get(a, 0) | (1 << tgt)
    return nV, trans


def determinize(nV: int, trans: List[Dict[int, int]], prog: Progress) -> Tuple[List[int], List[Dict[int, int]]]:
    """Determinize G_m into the subset-filter automaton.

    Returns (subset_masks, det) where:
      subset_masks[sid] is a bitmask of V_m representing the subset state,
      det[sid][label] = sid' is the deterministic transition on that label.
    """
    start_mask = (1 << nV) - 1
    q: List[int] = [start_mask]
    qi = 0
    id_of: Dict[int, int] = {start_mask: 0}
    masks: List[int] = [start_mask]
    det: List[Dict[int, int]] = []

    t0 = time.time()
    while qi < len(q):
        S = q[qi]
        qi += 1
        sid = id_of[S]
        while len(det) <= sid:
            det.append({})

        next_by_label: Dict[int, int] = {}
        vv = S
        while vv:
            lsb = vv & -vv
            v = lsb.bit_length() - 1
            vv -= lsb
            for a, tgt_mask in trans[v].items():
                next_by_label[a] = next_by_label.get(a, 0) | tgt_mask

        for a, T in next_by_label.items():
            if T not in id_of:
                id_of[T] = len(masks)
                masks.append(T)
                q.append(T)
            det[sid][a] = id_of[T]

        # Periodic progress output for larger m.
        if sid % 200 == 0:
            elapsed = time.time() - t0
            prog.tick(f"determinize nV={nV} states={len(masks)} queue={len(q)-qi} elapsed={elapsed:.1f}s")

    return masks, det


def reachable_exact(det: List[Dict[int, int]], steps: int) -> Set[int]:
    cur: Set[int] = {0}
    for _ in range(steps):
        nxt: Set[int] = set()
        for sid in cur:
            for tid in det[sid].values():
                nxt.add(tid)
        cur = nxt
    return cur


def _is_singleton_mask(mask: int) -> bool:
    return mask != 0 and (mask & (mask - 1)) == 0


def periodic_distinct_count(m: int, fold_map: List[int], n: int) -> int:
    """Count distinct Phi_m images among all n-periodic {0,1} inputs (small n only)."""
    if n <= 0:
        return 0
    seen: Set[Tuple[int, ...]] = set()
    for x in range(1 << n):
        bits = [(x >> (n - 1 - i)) & 1 for i in range(n)]
        out: List[int] = []
        for t in range(n):
            w = 0
            for i in range(m):
                w = (w << 1) | bits[(t + i) % n]
            out.append(fold_map[w])
        seen.add(tuple(out))
    return len(seen)


@dataclass(frozen=True)
class Row:
    m: int
    det_states: int
    det_edges: int
    Rm1_states: int
    non_singleton_ends_m1: int
    Rm_states: int
    non_singleton_ends: int
    periodic_formula: str
    periodic_ok_up_to_n: int


def write_table_tex(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Conjugacy threshold certificate for the sliding-block factor $\\Phi_m$. "
        "We build the subset-filter automaton from the labeled graph $G_m$ and compute "
        "$R_{m-1}$ and $R_m$, the sets of reachable filter states after exactly $m-1$ and $m$ output symbols. "
        "If all states in $R_m$ are singletons, then each length-$m$ output word has a unique "
        "length-$(2m-1)$ preimage block, yielding a finite-window inverse (memory $m-1$). "
        "The non-singleton count in $R_{m-1}$ provides a sharpness witness for the sync delay. "
        "We also cross-check periodic-point counts up to a small $n$.}"
    )
    lines.append("\\label{tab:phi_m_conjugacy_threshold}")
    lines.append("\\begin{tabular}{r r r r r r r l r}")
    lines.append("\\toprule")
    lines.append("$m$ & det states & det edges & $|R_{m-1}|$ & non-singleton ends $(m-1)$ & $|R_m|$ & non-singleton ends $(m)$ & periodic $\\#\\mathrm{Fix}_n$ & checked $n$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.m} & {r.det_states} & {r.det_edges} & {r.Rm1_states} & {r.non_singleton_ends_m1} & {r.Rm_states} & {r.non_singleton_ends} & {r.periodic_formula} & {r.periodic_ok_up_to_n}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Certificate: local conjugacy threshold for Phi_m.")
    parser.add_argument("--m-min", type=int, default=2, help="Minimum m (>=2).")
    parser.add_argument("--m-max", type=int, default=12, help="Maximum m.")
    parser.add_argument("--periodic-n-max", type=int, default=8, help="Cross-check periodic points up to n.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "phi_m_conjugacy_threshold.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_phi_m_conjugacy_threshold.tex"),
    )
    args = parser.parse_args()

    m_min = int(args.m_min)
    m_max = int(args.m_max)
    n_max = int(args.periodic_n_max)
    if m_min < 2:
        raise SystemExit("Require m_min >= 2")
    if m_max < m_min:
        raise SystemExit("Require m_max >= m_min")
    if n_max < 1:
        raise SystemExit("Require periodic_n_max >= 1")

    prog = Progress("exp_phi_m_conjugacy_threshold", every_seconds=20.0)
    rows: List[Row] = []

    t0_all = time.time()
    for m in range(m_min, m_max + 1):
        fold_map = build_fold_map(m, prog)
        nV, trans = build_Gm_edges(m, fold_map)
        masks, det = determinize(nV, trans, prog)

        det_edges = sum(len(d) for d in det)
        Rm1 = reachable_exact(det, steps=m - 1)
        non_single_m1 = sum(1 for sid in Rm1 if not _is_singleton_mask(masks[sid]))
        Rm = reachable_exact(det, steps=m)
        non_single = sum(1 for sid in Rm if not _is_singleton_mask(masks[sid]))

        # Periodic-point sanity checks (small n only).
        if m >= 3:
            formula = "$2^n$"
            expected = lambda n: (1 << n)
        else:
            formula = "$2^n-1$"
            expected = lambda n: (1 << n) - 1

        ok_up_to = 0
        for n in range(1, n_max + 1):
            cnt = periodic_distinct_count(m, fold_map, n)
            if cnt != expected(n):
                break
            ok_up_to = n

        rows.append(
            Row(
                m=m,
                det_states=len(det),
                det_edges=det_edges,
                Rm1_states=len(Rm1),
                non_singleton_ends_m1=non_single_m1,
                Rm_states=len(Rm),
                non_singleton_ends=non_single,
                periodic_formula=formula,
                periodic_ok_up_to_n=ok_up_to,
            )
        )

        print(
            f"[phi_m_conjugacy] m={m} det_states={len(det)} Rm={len(Rm)} non_single_end={non_single} periodic_ok_n={ok_up_to}/{n_max}",
            flush=True,
        )

    payload = {"rows": [asdict(r) for r in rows], "args": {"m_min": m_min, "m_max": m_max, "periodic_n_max": n_max}}
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[phi_m_conjugacy] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[phi_m_conjugacy] wrote {tout}", flush=True)

    dt_all = time.time() - t0_all
    print(f"[phi_m_conjugacy] DONE in {dt_all:.2f}s", flush=True)


if __name__ == "__main__":
    main()

