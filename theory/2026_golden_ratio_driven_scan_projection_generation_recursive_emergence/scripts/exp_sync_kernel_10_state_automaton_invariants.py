#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Automaton / semigroup invariants of the 10-state synchronization kernel.

We view the kernel as a deterministic automaton on Q with input alphabet {0,1,2},
forgetting the Mealy outputs. This script computes:

- shortest reset word length and per-target reset depth ℓ(t);
- a reproducible witness reset word for each target state t;
- the size and basic structure of the transition semigroup ⟨f_0,f_1,f_2⟩ ⊂ Q^Q.

Outputs (default):
- artifacts/export/sync_kernel_10_state_automaton_invariants.json
- sections/generated/tab_sync_kernel_reset_targets.tex
- sections/generated/tab_sync_kernel_transition_semigroup_invariants.tex

No external deps beyond the stdlib.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from exp_sync_kernel_real_input_40 import KERNEL_STATES, build_kernel_edges


@dataclass(frozen=True)
class ResetTarget:
    state: str
    reset_len: int
    witness_word: str


def latex_state_name(s: str) -> str:
    # Kernel uses "-1" in state strings; paper uses \overline{1}.
    # Examples: "0-12" -> "0\overline{1}2", "01-1" -> "01\overline{1}".
    return s.replace("-1", r"\overline{1}")


def build_delta() -> Tuple[List[str], Dict[Tuple[str, int], str]]:
    edges = build_kernel_edges()
    Q = list(KERNEL_STATES)
    delta: Dict[Tuple[str, int], str] = {}
    for e in edges:
        key = (e.src, int(e.d))
        if key in delta:
            raise RuntimeError(f"non-deterministic transition at {key}")
        delta[key] = e.dst
    # Validate totality.
    for s in Q:
        for d in (0, 1, 2):
            if (s, d) not in delta:
                raise RuntimeError(f"missing transition for {(s, d)}")
    return Q, delta


def subset_bfs_reset_targets(
    Q: List[str],
    delta: Dict[Tuple[str, int], str],
) -> Tuple[int, List[ResetTarget], Dict[str, object]]:
    """BFS on the power-set automaton starting from the full set Q.

    Returns:
    - minimal reset length (to any singleton),
    - list of per-target ResetTarget (one witness word each),
    - extra diagnostics payload.
    """
    n = len(Q)
    idx = {s: i for i, s in enumerate(Q)}
    full_mask = (1 << n) - 1

    def step_mask(mask: int, d: int) -> int:
        mm = 0
        x = mask
        while x:
            lsb = x & -x
            i = lsb.bit_length() - 1
            s = Q[i]
            t = delta[(s, d)]
            mm |= 1 << idx[t]
            x -= lsb
        return mm

    dist: Dict[int, int] = {full_mask: 0}
    prev: Dict[int, int | None] = {full_mask: None}
    prev_d: Dict[int, int | None] = {full_mask: None}
    q = deque([full_mask])

    while q:
        m = q.popleft()
        for d in (0, 1, 2):
            mm = step_mask(m, d)
            if mm not in dist:
                dist[mm] = dist[m] + 1
                prev[mm] = m
                prev_d[mm] = d
                q.append(mm)

    def word_of(mask: int) -> str:
        w: List[str] = []
        cur = mask
        while prev[cur] is not None:
            w.append(str(prev_d[cur]))
            cur = int(prev[cur])
        return "".join(reversed(w))

    # minimal reset length
    min_reset_len = min(dist[m] for m in dist if m & (m - 1) == 0)

    targets: List[ResetTarget] = []
    for s in Q:
        m = 1 << idx[s]
        if m not in dist:
            raise RuntimeError(f"singleton {s} not reachable (unexpected)")
        targets.append(ResetTarget(state=s, reset_len=dist[m], witness_word=word_of(m)))

    # Some handy diagnostics for the paper.
    img_after_one_zero = sorted({delta[(s, 0)] for s in Q})
    cur_mask = full_mask
    for _ in range(4):
        cur_mask = step_mask(cur_mask, 0)
    img_after_0000 = [Q[i] for i in range(n) if (cur_mask >> i) & 1]

    diag: Dict[str, object] = {
        "min_reset_length": int(min_reset_len),
        "image_after_one_zero": img_after_one_zero,
        "image_after_0000": img_after_0000,
        "reset_targets": {
            t.state: {"len": int(t.reset_len), "witness": t.witness_word} for t in targets
        },
    }
    return int(min_reset_len), targets, diag


def transition_semigroup_invariants(
    Q: List[str],
    delta: Dict[Tuple[str, int], str],
) -> Dict[str, object]:
    n = len(Q)
    idx = {s: i for i, s in enumerate(Q)}

    # Letter maps f_d: Q -> Q as tuples of indices.
    f = {d: tuple(idx[delta[(s, d)]] for s in Q) for d in (0, 1, 2)}

    def compose(g: Tuple[int, ...], t: Tuple[int, ...]) -> Tuple[int, ...]:
        # (g ∘ t)(i) = g(t(i))
        return tuple(g[t[i]] for i in range(n))

    id_map = tuple(range(n))
    seen = {id_map}
    prev: Dict[Tuple[int, ...], Tuple[int, ...] | None] = {id_map: None}
    prev_d: Dict[Tuple[int, ...], int | None] = {id_map: None}
    dist: Dict[Tuple[int, ...], int] = {id_map: 0}
    q = deque([id_map])

    while q:
        t = q.popleft()
        for d in (0, 1, 2):
            nt = compose(f[d], t)
            if nt not in seen:
                seen.add(nt)
                prev[nt] = t
                prev_d[nt] = d
                dist[nt] = dist[t] + 1
                q.append(nt)

    def word_of(t: Tuple[int, ...]) -> str:
        w: List[str] = []
        cur = t
        while prev[cur] is not None:
            w.append(str(prev_d[cur]))
            cur = prev[cur]  # type: ignore[assignment]
        return "".join(reversed(w))

    def rank(t: Tuple[int, ...]) -> int:
        return len(set(t))

    def max_cycle_len(t: Tuple[int, ...]) -> int:
        best = 1
        vis = [False] * n
        for i in range(n):
            if vis[i]:
                continue
            cur = i
            step: Dict[int, int] = {}
            k = 0
            while not vis[cur]:
                vis[cur] = True
                step[cur] = k
                k += 1
                cur = t[cur]
                if cur in step:
                    best = max(best, k - step[cur])
                    break
        return best

    units = [t for t in seen if rank(t) == n]
    rank_counts = Counter(rank(t) for t in seen)
    max_cyc = max(max_cycle_len(t) for t in seen)

    # 2-cycle witnesses: shortest word producing each distinct 2-cycle pair.
    best_pair_witness: Dict[Tuple[int, int], Tuple[int, str]] = {}
    two_cycle_elements = 0
    for t in seen:
        pairs: List[Tuple[int, int]] = []
        for a in range(n):
            b = t[a]
            if a < b and t[b] == a:
                pairs.append((a, b))
        if not pairs:
            continue
        two_cycle_elements += 1
        wlen = dist[t]
        w = word_of(t)
        for a, b in pairs:
            cur = best_pair_witness.get((a, b))
            if cur is None or wlen < cur[0]:
                best_pair_witness[(a, b)] = (wlen, w)

    pair_witnesses = [
        {
            "pair": (Q[a], Q[b]),
            "wlen": int(wlen),
            "word": w,
        }
        for (a, b), (wlen, w) in sorted(best_pair_witness.items(), key=lambda kv: (kv[1][0], kv[0]))
    ]

    return {
        "semigroup_size": int(len(seen)),
        "units_count": int(len(units)),
        "rank_counts": {int(k): int(v) for k, v in sorted(rank_counts.items())},
        "max_cycle_length": int(max_cyc),
        "two_cycle_elements_count": int(two_cycle_elements),
        "two_cycle_pair_witnesses": pair_witnesses,
    }


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_reset_targets_table(path: Path, *, targets: List[ResetTarget]) -> None:
    # Sort by (reset_len, stable order in Q)
    targets_sorted = sorted(targets, key=lambda t: (t.reset_len, t.state))

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_10_state_automaton_invariants.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.15}")
    lines.append(
        "\\caption{Reset depth by target state for the 10-state synchronization kernel, "
        "viewed as a deterministic automaton on $Q$ with input alphabet $\\{0,1,2\\}$. "
        "Here $\\ell(t)=\\min\\{|w|:\\,\\delta(Q,w)=\\{t\\}\\}$ and the witness word is given in \\texttt{012}-notation.}"
    )
    lines.append("\\label{tab:sync-kernel-reset-target-depth}")
    lines.append("\\begin{tabular}{l r l}")
    lines.append("\\toprule")
    lines.append("target $t$ & $\\ell(t)$ & witness reset word $w$\\\\")
    lines.append("\\midrule")
    for t in targets_sorted:
        st = latex_state_name(t.state)
        lines.append(f"$({st})$ & {t.reset_len} & \\texttt{{{t.witness_word}}}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_semigroup_table(path: Path, *, semigroup: Dict[str, object]) -> None:
    rank_counts = semigroup.get("rank_counts", {})
    if not isinstance(rank_counts, dict):
        raise RuntimeError("rank_counts must be a dict")
    rank_profile = ", ".join(f"{r}:{rank_counts[r]}" for r in sorted(rank_counts))

    # 2-cycle witness summary (keep short for TeX readability).
    pairs = semigroup.get("two_cycle_pair_witnesses", [])
    pairs_tex = ""
    if isinstance(pairs, list) and pairs:
        show = pairs[:4]
        parts: List[str] = []
        for p in show:
            if not isinstance(p, dict):
                continue
            a, b = p.get("pair", ("?", "?"))
            w = str(p.get("word", ""))
            parts.append(
                f"$({latex_state_name(str(a))})\\leftrightarrow({latex_state_name(str(b))})$ via \\texttt{{{w}}}"
            )
        if len(pairs) > len(show):
            parts.append(f"\\textit{{(+{len(pairs) - len(show)} more)}}")
        pairs_tex = "; ".join(parts)

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_10_state_automaton_invariants.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.15}")
    lines.append(
        "\\caption{Transition semigroup invariants for the 10-state synchronization kernel. "
        "We form $f_d:q\\mapsto\\delta(q,d)$ and take the generated transformation monoid "
        "$\\mathcal{S}=\\langle f_0,f_1,f_2\\rangle\\subseteq Q^Q$. "
        "The \\texttt{rank} is $|\\mathrm{Im}(f)|$.}"
    )
    lines.append("\\label{tab:sync-kernel-transition-semigroup-invariants}")
    lines.append("\\begin{tabular}{l p{0.72\\linewidth}}")
    lines.append("\\toprule")
    lines.append("quantity & value\\\\")
    lines.append("\\midrule")
    lines.append(f"$|\\mathcal{{S}}|$ & {int(semigroup['semigroup_size'])}\\\\")
    lines.append(f"\\# units (global permutations) & {int(semigroup['units_count'])}\\\\")
    lines.append(f"max cycle length (in elements) & {int(semigroup['max_cycle_length'])}\\\\")
    lines.append(
        f"\\# elements containing a 2-cycle & {int(semigroup.get('two_cycle_elements_count', 0))}\\\\"
    )
    lines.append(
        "rank profile ($r:\\#\\{f:\\mathrm{rank}(f)=r\\}$) & " + rank_profile + "\\\\"
    )
    if pairs_tex:
        lines.append("\\midrule")
        lines.append("shortest 2-cycle witnesses & " + pairs_tex + "\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Automaton / semigroup invariants for the 10-state sync kernel"
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_10_state_automaton_invariants.json"),
    )
    parser.add_argument(
        "--tex-reset-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_reset_targets.tex"),
    )
    parser.add_argument(
        "--tex-semigroup-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_transition_semigroup_invariants.tex"),
    )
    args = parser.parse_args()

    Q, delta = build_delta()
    min_len, targets, diag = subset_bfs_reset_targets(Q, delta)
    semi = transition_semigroup_invariants(Q, delta)

    payload: Dict[str, object] = {
        "states": Q,
        "automaton": diag,
        "transition_semigroup": semi,
    }
    write_json(Path(args.json_out), payload)
    write_reset_targets_table(Path(args.tex_reset_out), targets=targets)
    write_semigroup_table(Path(args.tex_semigroup_out), semigroup=semi)

    print(
        f"[sync10-automaton] min_reset_length={min_len} |S|={semi['semigroup_size']} units={semi['units_count']}",
        flush=True,
    )


if __name__ == "__main__":
    main()

