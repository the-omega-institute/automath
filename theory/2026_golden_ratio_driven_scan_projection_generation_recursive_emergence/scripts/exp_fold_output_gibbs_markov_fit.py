#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Fit a finite-state transfer matrix to the intrinsic output weights pi_m(x)=d_m(x)/2^m.

We work with the Fold_m map on microstates Omega_m={0,1}^m and its fiber multiplicities:
  d_m(x) = |Fold_m^{-1}(x)|,  x in X_m.
Under the uniform microstate baseline on Omega_m, the Fold-output distribution is
  pi_m(x) = d_m(x) / 2^m.

This script provides an auditable "intrinsic Gibbs / transfer-matrix" protocol:
  - Enumerate pi_m exactly for a moderate m (default m=18).
  - Compute the pi_m-weighted empirical distribution of length-ell blocks inside x.
  - Build the (ell-1)-step Markov maximum-likelihood model from these block frequencies.
  - Report the implied 1-step transition probabilities and compare to the Parry baseline
    (golden-mean SFT adjacency A=[[1,1],[1,0]]).

Outputs (default):
  - artifacts/export/fold_output_gibbs_markov_fit.json
  - sections/generated/tab_fold_output_gibbs_markov_fit.tex
  - sections/generated/eq_fold_output_gibbs_entropy_gap.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from itertools import product
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fold_m, word_to_str


def legal_golden(word: str) -> bool:
    return "11" not in word


def parry_transition_golden() -> Dict[str, Dict[str, float]]:
    """Return Parry transition P(bit_next | bit_current) for golden mean shift."""
    # States are bits '0' and '1'. Adjacency: 0->0,0->1,1->0.
    # Parry: P_{ij} = A_{ij} v_j / (phi v_i) with right PF eigenvector v.
    phi = (1.0 + 5.0**0.5) / 2.0
    # Right eigenvector for A: solve A v = phi v.
    # Take v = [phi, 1] (up to scale).
    v0, v1 = phi, 1.0
    # Transition probabilities.
    P00 = 1.0 * v0 / (phi * v0)  # = 1/phi
    P01 = 1.0 * v1 / (phi * v0)  # = 1/phi^2
    P10 = 1.0 * v0 / (phi * v1)  # = 1
    return {"0": {"0": P00, "1": P01}, "1": {"0": P10, "1": 0.0}}


def enumerate_pi_m(m: int, prog: Progress) -> Dict[str, float]:
    counts: Dict[str, int] = {}
    total = 1 << m
    for i, bits in enumerate(product([0, 1], repeat=m), start=1):
        x = word_to_str(fold_m(bits))
        counts[x] = counts.get(x, 0) + 1
        prog.tick(f"m={m} i={i}/{total} |X_m|={len(counts)}")
    # Normalize to pi_m.
    inv = 1.0 / float(total)
    return {x: c * inv for x, c in counts.items()}


def weighted_block_frequencies(pi_m: Dict[str, float], ell: int) -> Dict[str, float]:
    if ell < 1:
        raise ValueError("ell must be >= 1")
    freq: Dict[str, float] = {}
    for x, px in pi_m.items():
        if len(x) < ell:
            continue
        denom = float(len(x) - ell + 1)
        w = px / denom
        for i in range(0, len(x) - ell + 1):
            b = x[i : i + ell]
            freq[b] = freq.get(b, 0.0) + w
    return freq


def build_markov_from_blocks(freq_ell: Dict[str, float], ell: int) -> Tuple[List[str], Dict[str, Dict[str, float]]]:
    """Return (states, P) where states are (ell-1)-blocks and P gives next-bit probabilities."""
    if ell < 2:
        raise ValueError("ell must be >= 2 for Markov fit")
    k = ell - 1
    # Aggregate prefix counts.
    pref: Dict[str, float] = {}
    for b, w in freq_ell.items():
        if len(b) != ell:
            continue
        s = b[:k]
        pref[s] = pref.get(s, 0.0) + w

    states = sorted([s for s, w in pref.items() if w > 0.0])
    P: Dict[str, Dict[str, float]] = {s: {"0": 0.0, "1": 0.0} for s in states}
    for b, w in freq_ell.items():
        if len(b) != ell:
            continue
        s = b[:k]
        nxt = b[-1]
        if s not in pref or pref[s] <= 0:
            continue
        P[s][nxt] += w / pref[s]

    # For any missing probability mass (numerical), renormalize.
    for s in states:
        z = P[s]["0"] + P[s]["1"]
        if z <= 0:
            continue
        P[s]["0"] /= z
        P[s]["1"] /= z
    return states, P


def stationary_distribution(states: List[str], P: Dict[str, Dict[str, float]], iters: int = 20000) -> Dict[str, float]:
    """Power iteration on the state Markov chain induced by shifting + next bit."""
    if not states:
        return {}
    k = len(states[0])
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    v = [1.0 / n] * n
    for _ in range(iters):
        w = [0.0] * n
        for s in states:
            i = idx[s]
            for bit in ("0", "1"):
                p = P[s].get(bit, 0.0)
                if p <= 0:
                    continue
                t = (s + bit)[-k:]
                if t not in idx:
                    continue
                w[idx[t]] += v[i] * p
        ssum = sum(w)
        if ssum > 0:
            v = [x / ssum for x in w]
    return {states[i]: v[i] for i in range(n)}


def implied_one_step(stationary: Dict[str, float], P: Dict[str, Dict[str, float]]) -> Dict[str, Dict[str, float]]:
    """Aggregate to P(bit_next | bit_current) by averaging over (ell-1)-states."""
    if not stationary:
        return {}
    k = len(next(iter(stationary.keys())))
    # Current bit is last bit of the state.
    mass = {"0": 0.0, "1": 0.0}
    trans = {"0": {"0": 0.0, "1": 0.0}, "1": {"0": 0.0, "1": 0.0}}
    for s, ps in stationary.items():
        cur = s[-1]
        mass[cur] += ps
        for nxt in ("0", "1"):
            trans[cur][nxt] += ps * P[s].get(nxt, 0.0)
    # Normalize.
    out = {"0": {"0": 0.0, "1": 0.0}, "1": {"0": 0.0, "1": 0.0}}
    for cur in ("0", "1"):
        if mass[cur] <= 0:
            continue
        out[cur]["0"] = trans[cur]["0"] / mass[cur]
        out[cur]["1"] = trans[cur]["1"] / mass[cur]
    return out


def tv_distance_row(P: Dict[str, Dict[str, float]], Q: Dict[str, Dict[str, float]], row: str) -> float:
    return 0.5 * (abs(P[row]["0"] - Q[row]["0"]) + abs(P[row]["1"] - Q[row]["1"]))


def stationary_two_state(P: Dict[str, Dict[str, float]]) -> Dict[str, float]:
    """Solve stationary distribution for a 2-state Markov chain on {'0','1'}.

    Returns {'0': pi0, '1': pi1}. Assumes a well-defined chain with P11 != 1.
    """
    p01 = float(P["0"]["1"])
    p11 = float(P["1"]["1"])
    denom = (1.0 - p11) + p01
    if denom <= 0:
        raise ValueError("Degenerate 2-state chain: cannot solve stationary distribution.")
    pi0 = (1.0 - p11) / denom
    pi1 = 1.0 - pi0
    return {"0": pi0, "1": pi1}


def entropy_rate_two_state(P: Dict[str, Dict[str, float]], pi: Dict[str, float]) -> float:
    """Shannon entropy rate in nats per symbol."""
    h = 0.0
    for cur in ("0", "1"):
        for nxt in ("0", "1"):
            p = float(P[cur][nxt])
            if p > 0.0:
                h -= float(pi[cur]) * p * math.log(p)
    return h


def kl_rate_two_state(
    P: Dict[str, Dict[str, float]], Q: Dict[str, Dict[str, float]], pi: Dict[str, float]
) -> float:
    """KL divergence rate D(P||Q) in nats per symbol (same support assumed)."""
    d = 0.0
    for cur in ("0", "1"):
        for nxt in ("0", "1"):
            p = float(P[cur][nxt])
            if p <= 0.0:
                continue
            q = float(Q[cur][nxt])
            if q <= 0.0:
                raise ValueError(f"Support mismatch: Q[{cur}][{nxt}] = {q} but P has mass {p}.")
            d += float(pi[cur]) * p * math.log(p / q)
    return d


def _sci_tex(x: float, sig: int = 6) -> str:
    if x == 0.0:
        return "0"
    s = f"{x:.{sig}e}"
    mant, exp_s = s.split("e")
    exp = int(exp_s)
    mant = mant.rstrip("0").rstrip(".")
    return f"{mant}\\times 10^{{{exp}}}"


def write_entropy_gap_tex(path: Path, payload: Dict[str, object]) -> None:
    # Pull computed scalars.
    h_fit = float(payload["entropy_rate_fit_nats_per_symbol"])
    h_parry = float(payload["entropy_rate_parry_nats_per_symbol"])
    gap_nats = float(payload["entropy_gap_nats_per_symbol"])
    gap_bits = float(payload["entropy_gap_bits_per_symbol"])
    kl_rate = float(payload["kl_rate_fit_vs_parry_nats_per_symbol"])
    gap_minus_kl = float(payload["entropy_gap_minus_kl_rate_nats_per_symbol"])

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_fold_output_gibbs_markov_fit.py")
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append(f"h_{{\\mathrm{{fit}}}}&\\approx {h_fit:.12f}\\ \\text{{nats/symbol}},\\\\")
    lines.append(f"\\log\\varphi&\\approx {h_parry:.12f}\\ \\text{{nats/symbol}},\\\\")
    lines.append(
        f"\\Delta h:=\\log\\varphi-h_{{\\mathrm{{fit}}}}"
        f"&\\approx {_sci_tex(gap_nats, sig=6)}\\ \\text{{nats/symbol}}"
        f"\\approx {_sci_tex(gap_bits, sig=6)}\\ \\text{{bits/symbol}},\\\\"
    )
    lines.append(
        f"D_{{\\mathrm{{KL}}}}^{{\\mathrm{{rate}}}}(P_{{\\mathrm{{fit}}}}\\|P_{{\\mathrm{{Parry}}}})"
        f"&\\approx {_sci_tex(kl_rate, sig=6)}\\ \\text{{nats/symbol}},\\\\"
    )
    lines.append(f"\\Delta h-D_{{\\mathrm{{KL}}}}^{{\\mathrm{{rate}}}}(P_{{\\mathrm{{fit}}}}\\|P_{{\\mathrm{{Parry}}}})")
    lines.append(f"&\\approx {_sci_tex(gap_minus_kl, sig=3)}\\ \\text{{nats/symbol}}.")
    lines.append("\\end{aligned}")
    lines.append("\\]")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_table_tex(path: Path, payload: Dict[str, object]) -> None:
    m = int(payload["m"])
    ell = int(payload["ell"])
    p_fit = payload["implied_one_step_fit"]  # type: ignore[assignment]
    p_parry = payload["parry_one_step"]  # type: ignore[assignment]

    def f(row: str, col: str, Pobj: object) -> float:
        return float(Pobj[row][col])  # type: ignore[index]

    tv0 = float(payload["tv_row0"])
    tv1 = float(payload["tv_row1"])
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Intrinsic output weights as a finite-state transfer-matrix fit. "
        "We enumerate $\\pi_m(x)=d_m(x)/2^m$ exactly on $X_m$, build the $(\\ell{-}1)$-step Markov model "
        "from $\\pi_m$-weighted length-$\\ell$ block frequencies, and report the implied 1-step transitions "
        "compared to the Parry baseline of the golden-mean SFT.}"
    )
    lines.append("\\label{tab:fold_output_gibbs_markov_fit}")
    lines.append("\\begin{tabular}{l r r}")
    lines.append("\\toprule")
    lines.append("Quantity & fitted from $\\pi_m$ & Parry baseline\\\\")
    lines.append("\\midrule")
    lines.append(f"$m$ & {m} & {m}\\\\")
    lines.append(f"$\\ell$ & {ell} & {ell}\\\\")
    lines.append(
        f"$P(1\\mid 0)$ & {f('0','1',p_fit):.12f} & {f('0','1',p_parry):.12f}\\\\"
    )
    lines.append(
        f"$P(0\\mid 0)$ & {f('0','0',p_fit):.12f} & {f('0','0',p_parry):.12f}\\\\"
    )
    lines.append(
        f"$P(0\\mid 1)$ & {f('1','0',p_fit):.12f} & {f('1','0',p_parry):.12f}\\\\"
    )
    lines.append(f"TV row $0$ & {tv0:.3e} & 0\\\\")
    lines.append(f"TV row $1$ & {tv1:.3e} & 0\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Fit a Markov transfer matrix to the intrinsic Fold-output weights pi_m.")
    ap.add_argument("--m", type=int, default=18, help="Window length m for exact enumeration (pi_m).")
    ap.add_argument("--ell", type=int, default=4, help="Block length ell for Markov fit (>=2).")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_output_gibbs_markov_fit.json"),
        help="Output JSON path.",
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_output_gibbs_markov_fit.tex"),
        help="Output LaTeX table path.",
    )
    ap.add_argument(
        "--tex-entropy-out",
        type=str,
        default=str(generated_dir() / "eq_fold_output_gibbs_entropy_gap.tex"),
        help="Output LaTeX equation snippet path (entropy/KL gap).",
    )
    args = ap.parse_args()

    if args.m < 2:
        raise SystemExit("Require m>=2")
    if args.ell < 2 or args.ell > args.m:
        raise SystemExit("Require 2 <= ell <= m")

    prog = Progress("gibbs-markov-fit", every_seconds=20.0)
    pi_m = enumerate_pi_m(args.m, prog)
    # Defensive check: support should be golden-legal.
    if any(not legal_golden(x) for x in pi_m.keys()):
        raise RuntimeError("Found illegal golden word in Fold output (unexpected).")

    freq_ell = weighted_block_frequencies(pi_m, args.ell)
    states, P_state = build_markov_from_blocks(freq_ell, args.ell)
    stat = stationary_distribution(states, P_state, iters=20000)
    P1 = implied_one_step(stat, P_state)
    P_parry = parry_transition_golden()

    tv0 = tv_distance_row(P1, P_parry, "0")
    tv1 = tv_distance_row(P1, P_parry, "1")

    pi2 = stationary_two_state(P1)
    h_fit = entropy_rate_two_state(P1, pi2)
    phi = (1.0 + 5.0**0.5) / 2.0
    h_parry = math.log(phi)
    gap_nats = h_parry - h_fit
    gap_bits = gap_nats / math.log(2.0)
    kl_rate = kl_rate_two_state(P1, P_parry, pi2)
    gap_minus_kl = gap_nats - kl_rate

    payload: Dict[str, object] = {
        "m": args.m,
        "ell": args.ell,
        "support_size": len(pi_m),
        "parry_one_step": P_parry,
        "implied_one_step_fit": P1,
        "tv_row0": tv0,
        "tv_row1": tv1,
        "num_states": len(states),
        "entropy_rate_fit_nats_per_symbol": h_fit,
        "entropy_rate_parry_nats_per_symbol": h_parry,
        "entropy_gap_nats_per_symbol": gap_nats,
        "entropy_gap_bits_per_symbol": gap_bits,
        "kl_rate_fit_vs_parry_nats_per_symbol": kl_rate,
        "entropy_gap_minus_kl_rate_nats_per_symbol": gap_minus_kl,
    }

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"[gibbs-markov-fit] wrote {jout}", flush=True)

    write_table_tex(Path(args.tex_out), payload)
    print(f"[gibbs-markov-fit] wrote {args.tex_out}", flush=True)

    write_entropy_gap_tex(Path(args.tex_entropy_out), payload)
    print(f"[gibbs-markov-fit] wrote {args.tex_entropy_out}", flush=True)


if __name__ == "__main__":
    main()

