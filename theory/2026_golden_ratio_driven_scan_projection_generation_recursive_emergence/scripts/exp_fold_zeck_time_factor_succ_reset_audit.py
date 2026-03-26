#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit: Zeckendorf-prefix fold time factor (Succ_m) and reset events R_m.

All code is English-only by repository convention.

We extend the Zeckendorf-prefix fold to all N∈N:
  Fold^{zeck}_m(N) := pi_m(Z(N)) ∈ X_m,
where Z(N) are Zeckendorf digits in Fibonacci weights and pi_m truncates to the
first m digits (low-weight side).

We then study the factor dynamics induced by the time advance N -> N+1 on X_m:
  Succ_m(w) := { Fold^{zeck}_m(N+1) : Fold^{zeck}_m(N)=w }.

We also define the reset-event set
  R_m := { N : Fold^{zeck}_m(N)=b_m and Fold^{zeck}_m(N+1)=0^m },
where b_m is the alternating maximal word ending in 0.

This script produces small finite certificates:
  - uniqueness of the branching point b_m and the merging point 0^m,
  - the two-gap return-time spectrum for reset events (audited for m=2..10),
  - a concrete m=6 gap prefix table.

Outputs:
  - artifacts/export/fold_zeck_time_factor_succ_reset_audit.json
  - sections/generated/tab_fold_zeck_succ_unique_branch_audit_m2_m10.tex
  - sections/generated/tab_fold_zeck_reset_event_audit_m2_m10.tex
  - sections/generated/tab_fold_zeck_reset_event_gaps_m6.tex
"""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Set, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import PHI, fib_upto, word_to_str, zeckendorf_digits


def _zeckendorf_digits_full(N: int) -> List[int]:
    """Return Zeckendorf digits (c_1..c_K) for weights F_{k+1}, k=1..K, with K minimal."""
    if N < 0:
        raise ValueError("N must be non-negative")
    if N == 0:
        return []

    # Build Fibonacci numbers F_1.. until the last <= N.
    f = [1, 1]  # F_1, F_2
    while f[-1] <= N:
        f.append(f[-1] + f[-2])
    # Now f[-2] <= N < f[-1], and f[-2] = F_{K+1} for K=len(f)-2.
    K = len(f) - 2
    return zeckendorf_digits(N, K)


def _fold_zeck_prefix_str(N: int, m: int) -> str:
    """Fold^{zeck}_m(N) as an m-bit string (low-weight digits)."""
    if m <= 0:
        raise ValueError("m must be >= 1")
    d = _zeckendorf_digits_full(N)
    if len(d) < m:
        d = d + [0] * (m - len(d))
    return word_to_str(d[:m])


def _Xm_words(m: int) -> List[str]:
    """All binary length-m words with no adjacent '11'."""
    out: List[str] = []

    def rec(prefix: str, last1: bool) -> None:
        if len(prefix) == m:
            out.append(prefix)
            return
        rec(prefix + "0", False)
        if not last1:
            rec(prefix + "1", True)

    rec("", False)
    return out


def _Vm(word: str, fib: List[int]) -> int:
    """Zeckendorf value V_m(w)=sum_{k=1}^m w_k F_{k+1}. fib[i]=F_{i+1} with 0-based i."""
    s = 0
    for k, ch in enumerate(word, start=1):
        if ch == "1":
            s += fib[k]  # F_{k+1}
    return s


def _u_m(m: int) -> str:
    # u_{m,k}=1 iff k+m even
    return "".join("1" if ((k + m) % 2 == 0) else "0" for k in range(1, m + 1))


def _b_m(m: int) -> str:
    # b_{m,k}=1 iff k+m odd
    return "".join("1" if ((k + m) % 2 == 1) else "0" for k in range(1, m + 1))


def _succ_map_predicted(m: int) -> Dict[str, Set[str]]:
    """Predict Succ_m(w) using the two canonical tail representatives (c_{m+1}=0/1)."""
    fib = fib_upto(m + 4)  # need up to F_{m+4}
    # fib_upto returns [F_1..F_{m+4}] in 0-based; weight F_{k+1} is fib[k]
    # F_{m+2} is fib[m+1]
    F_m2 = fib[m + 1]

    succ: Dict[str, Set[str]] = {}
    for w in _Xm_words(m):
        V = _Vm(w, fib)
        sset: Set[str] = set()
        sset.add(_fold_zeck_prefix_str(V + 1, m))

        if w.endswith("0"):
            V1 = V + F_m2
            # Sanity: V1 should still have prefix w.
            if _fold_zeck_prefix_str(V1, m) != w:
                raise RuntimeError(f"Prefix mismatch at m={m}, w={w}: V+F_{m+2} not in fiber")
            sset.add(_fold_zeck_prefix_str(V1 + 1, m))

        succ[w] = sset
    return succ


def _succ_map_observed(m: int, N_scan: int) -> Dict[str, Set[str]]:
    """Observe successors by scanning N in [0,N_scan)."""
    succ: Dict[str, Set[str]] = defaultdict(set)
    for N in range(N_scan):
        w = _fold_zeck_prefix_str(N, m)
        w2 = _fold_zeck_prefix_str(N + 1, m)
        succ[w].add(w2)
    return dict(succ)


def _reset_events(m: int, N_scan: int) -> List[int]:
    b = _b_m(m)
    z = "0" * m
    out: List[int] = []
    for N in range(N_scan):
        if _fold_zeck_prefix_str(N, m) == b and _fold_zeck_prefix_str(N + 1, m) == z:
            out.append(N)
    return out


def _fmt_set_str(items: List[str]) -> str:
    inner = ", ".join(f"\\texttt{{{x}}}" for x in items)
    return f"$\\{{{inner}\\}}$"


def _fmt_int_set(xs: List[int]) -> str:
    inner = ", ".join(str(x) for x in xs)
    return f"$\\{{{inner}\\}}$"


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit Succ_m and reset events for Zeckendorf-prefix fold.")
    ap.add_argument("--m-min", type=int, default=2)
    ap.add_argument("--m-max", type=int, default=10)
    ap.add_argument("--succ-scan-N", type=int, default=500_000)
    ap.add_argument("--reset-scan-N", type=int, default=200_000)
    ap.add_argument("--dev-scan-N", type=int, default=50_000)
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_zeck_time_factor_succ_reset_audit.json"),
        help="Path to JSON audit output.",
    )
    ap.add_argument(
        "--tex-succ-tab-out",
        type=str,
        default=str(generated_dir() / "tab_fold_zeck_succ_unique_branch_audit_m2_m10.tex"),
        help="Path to generated TeX table snippet.",
    )
    ap.add_argument(
        "--tex-reset-tab-out",
        type=str,
        default=str(generated_dir() / "tab_fold_zeck_reset_event_audit_m2_m10.tex"),
        help="Path to generated TeX table snippet.",
    )
    ap.add_argument(
        "--tex-reset-m6-tab-out",
        type=str,
        default=str(generated_dir() / "tab_fold_zeck_reset_event_gaps_m6.tex"),
        help="Path to generated TeX table snippet.",
    )
    args = ap.parse_args()

    m_min = int(args.m_min)
    m_max = int(args.m_max)
    succ_scan_N = int(args.succ_scan_N)
    reset_scan_N = int(args.reset_scan_N)
    dev_scan_N = int(args.dev_scan_N)

    if m_min < 2 or m_max < m_min:
        raise ValueError("Require 2 <= m_min <= m_max")

    audit_rows: List[Dict[str, object]] = []

    # Precompute Fibonacci numbers F_1..F_{m_max+6}.
    fib_all = fib_upto(m_max + 6)

    for m in range(m_min, m_max + 1):
        z = "0" * m
        u = _u_m(m)
        b = _b_m(m)

        succ_pred = _succ_map_predicted(m)
        succ_obs = _succ_map_observed(m, succ_scan_N)

        # Compare observed vs predicted on scanned range.
        obs_ok = True
        extra: Dict[str, List[str]] = {}
        for w, sset in succ_obs.items():
            pred = succ_pred.get(w, set())
            if not sset.issubset(pred):
                obs_ok = False
                extra[w] = sorted(sset - pred)

        # Compute out-degree / in-degree from predicted succ.
        out_deg = {w: len(sset) for w, sset in succ_pred.items()}
        in_pred: Dict[str, Set[str]] = defaultdict(set)
        for w, sset in succ_pred.items():
            for w2 in sset:
                in_pred[w2].add(w)
        in_deg = {w: len(pset) for w, pset in in_pred.items()}

        # Verify the unique-branch / unique-merge structure.
        unique_branch_ok = all((w == b) or (len(succ_pred[w]) == 1) for w in succ_pred.keys())
        b_succ = sorted(succ_pred[b])
        branch_succ_ok = set(b_succ) == {z, ("0" * (m - 1) + "1")}
        merge_ok = (z in in_pred) and (set(in_pred[z]) == {u, b})

        # Reset-event audits.
        reset_events = _reset_events(m, reset_scan_N)
        if len(reset_events) < 3:
            raise RuntimeError(f"Too few reset events for m={m} in scan range; increase reset_scan_N")
        gaps = [reset_events[i + 1] - reset_events[i] for i in range(len(reset_events) - 1)]
        gap_set = sorted(set(gaps))

        # Expected gaps are {F_{m+3},F_{m+4}}.
        # fib_all is [F_1..]; hence F_{m+3}=fib_all[m+2], F_{m+4}=fib_all[m+3].
        F_m3 = fib_all[m + 2]
        F_m4 = fib_all[m + 3]
        gap_ok = set(gap_set) == {F_m3, F_m4}

        # Density/discrepancy audit: max |count - alpha N| for N<=dev_scan_N.
        alpha = float(PHI ** (-(m + 2)))
        count = 0
        max_dev = 0.0
        max_dev_at = 0
        b_word = b
        for N in range(1, dev_scan_N + 1):
            # event at N-1
            if _fold_zeck_prefix_str(N - 1, m) == b_word and _fold_zeck_prefix_str(N, m) == z:
                count += 1
            dev = abs(float(count) - alpha * float(N))
            if dev > max_dev:
                max_dev = dev
                max_dev_at = N
        dev_ok = max_dev <= 1.0 + 1e-12

        audit_rows.append(
            {
                "m": m,
                "b_m": b,
                "u_m": u,
                "zero": z,
                "succ_b_m": b_succ,
                "pred_zero": sorted(in_pred.get(z, set())),
                "unique_branch_ok": unique_branch_ok,
                "branch_succ_ok": branch_succ_ok,
                "merge_ok": merge_ok,
                "succ_observed_scan_ok": obs_ok,
                "succ_observed_extra": extra,
                "reset_event_count_in_scan": len(reset_events),
                "reset_gap_set": gap_set,
                "reset_gap_ok": gap_ok,
                "density_alpha": alpha,
                "max_count_deviation_le_1_ok": dev_ok,
                "max_count_deviation": max_dev,
                "max_count_deviation_at_N": max_dev_at,
            }
        )

    payload: Dict[str, object] = {
        "params": {
            "m_min": m_min,
            "m_max": m_max,
            "succ_scan_N": succ_scan_N,
            "reset_scan_N": reset_scan_N,
            "dev_scan_N": dev_scan_N,
        },
        "rows": audit_rows,
    }

    json_out = Path(str(args.json_out))
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # TeX table: Succ_m unique branch audit.
    tex_succ_out = Path(str(args.tex_succ_tab_out))
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_fold_zeck_time_factor_succ_reset_audit.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\small")
    lines.append("\\setlength{\\tabcolsep}{7pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.10}")
    lines.append(
        "\\caption{Finite audit for the Zeckendorf-prefix successor relation $\\mathrm{Succ}_m$ induced by $N\\mapsto N+1$: "
        "for each $m$ we certify the unique branching point $b_m$ (out-degree $2$), its successor set, and the unique merging point $0^m$ "
        "(in-degree $2$) together with its predecessor set.}"
    )
    lines.append("\\label{tab:fold_zeck_succ_unique_branch_audit_m2_m10}")
    lines.append("\\begin{tabular}{r l l l}")
    lines.append("\\toprule")
    lines.append("$m$ & $b_m$ & $\\mathrm{Succ}_m(b_m)$ & $\\mathrm{Pred}_m(0^m)$\\\\")
    lines.append("\\midrule")
    for r in audit_rows:
        m = int(r["m"])
        b = str(r["b_m"])
        succb = sorted([str(x) for x in r["succ_b_m"]])  # type: ignore[list-item]
        predz = sorted([str(x) for x in r["pred_zero"]])  # type: ignore[list-item]
        lines.append(f"{m} & \\texttt{{{b}}} & {_fmt_set_str(succb)} & {_fmt_set_str(predz)}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")
    tex_succ_out.parent.mkdir(parents=True, exist_ok=True)
    tex_succ_out.write_text("\n".join(lines), encoding="utf-8")

    # TeX table: reset-event gap audit.
    tex_reset_out = Path(str(args.tex_reset_tab_out))
    lines = []
    lines.append("% AUTO-GENERATED by scripts/exp_fold_zeck_time_factor_succ_reset_audit.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\small")
    lines.append("\\setlength{\\tabcolsep}{7pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.10}")
    lines.append(
        "\\caption{Finite audit for the reset-event set $\\mathcal R_m=\\{N:\\ \\mathrm{Fold}^{\\mathrm{zeck}}_m(N)=b_m,\\ "
        "\\mathrm{Fold}^{\\mathrm{zeck}}_m(N+1)=0^m\\}$: observed gap set and the maximal counting deviation "
        "$\\max_{1\\le N\\le N_0}|\\#(\\mathcal R_m\\cap[0,N)) - \\varphi^{-(m+2)}N|$ over a finite scan.}"
    )
    lines.append("\\label{tab:fold_zeck_reset_event_audit_m2_m10}")
    lines.append("\\begin{tabular}{r l r}")
    lines.append("\\toprule")
    lines.append("$m$ & observed $\\{r_{n+1}-r_n\\}$ & $\\max_{N\\le N_0}\\bigl|\\#(\\mathcal R_m\\cap[0,N)) - \\varphi^{-(m+2)}N\\bigr|$\\\\")
    lines.append("\\midrule")
    for r in audit_rows:
        m = int(r["m"])
        gset = [int(x) for x in r["reset_gap_set"]]  # type: ignore[list-item]
        max_dev = float(r["max_count_deviation"])
        lines.append(f"{m} & {_fmt_int_set(sorted(gset))} & {max_dev:.6f}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")
    tex_reset_out.parent.mkdir(parents=True, exist_ok=True)
    tex_reset_out.write_text("\n".join(lines), encoding="utf-8")

    # TeX table: m=6 explicit gap prefix.
    tex_m6_out = Path(str(args.tex_reset_m6_tab_out))
    m = 6
    events = _reset_events(m, reset_scan_N)
    # take a short prefix
    prefix_len = 20
    events = events[: prefix_len + 1]
    gaps = [events[i + 1] - events[i] for i in range(len(events) - 1)]
    # Encode gaps as a Fibonacci word over {A,B} with A=F_{m+4}, B=F_{m+3}.
    fib_m = fib_upto(m + 6)
    A = fib_m[m + 3]  # F_{m+4}
    B = fib_m[m + 2]  # F_{m+3}
    ab = "".join("A" if g == A else "B" for g in gaps)

    lines = []
    lines.append("% AUTO-GENERATED by scripts/exp_fold_zeck_time_factor_succ_reset_audit.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\small")
    lines.append("\\setlength{\\tabcolsep}{7pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.10}")
    lines.append(
        f"\\caption{{Prefix certificate for reset events $\\mathcal R_6$ (Definition~\\ref{{def:terminal-reset-events}}): "
        f"the gap spectrum is $\\lbrace {B},{A}\\rbrace=\\lbrace F_9,F_{{10}}\\rbrace$, "
        f"and the induced letter word (with $A={A}$, $B={B}$) begins as \\texttt{{{ab}}}.}}"
    )
    lines.append("\\label{tab:fold_zeck_reset_event_gaps_m6}")
    lines.append("\\begin{tabular}{r r r}")
    lines.append("\\toprule")
    lines.append("$n$ & $r_n$ & $r_{n+1}-r_n$\\\\")
    lines.append("\\midrule")
    for i in range(prefix_len):
        lines.append(f"{i+1} & {events[i]} & {gaps[i]}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")
    tex_m6_out.parent.mkdir(parents=True, exist_ok=True)
    tex_m6_out.write_text("\n".join(lines), encoding="utf-8")


if __name__ == "__main__":
    main()
