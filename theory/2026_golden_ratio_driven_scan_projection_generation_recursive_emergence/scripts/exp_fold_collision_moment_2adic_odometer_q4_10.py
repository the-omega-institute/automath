#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit 2-adic odometer laws for Fold collision moments S_q(m).

We study:
  S_q(m) = sum_{x in X_m} d_m(x)^q,
and its 2-adic fingerprints:
  - stabilized v2(S_q(m)) and base congruence classes,
  - eventual pure periodicity of m -> S_q(m) mod 2^k after a linear threshold,
  - special zero-orbit structure for q=7.

The script verifies the stated laws by combining:
  (i) exact low-m values computed via modular DP residue counts:
        S_q(m) = sum_{r mod F_{m+2}} c_m(r)^q,
  (ii) exact integer recurrences for S_q(m) (audited elsewhere in the pipeline),
       used here for fast propagation to large m (both over Z and mod 2^k).

Outputs:
  - artifacts/export/fold_collision_moment_2adic_odometer_q4_10.json
  - sections/generated/tab_fold_collision_moment_2adic_odometer_q4_10.tex
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

from common_mod_fib_dp import counts_mod_fib, hist_from_counts
from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


def v2(x: int) -> int:
    """2-adic valuation v2(x) for x>0."""
    if x <= 0:
        raise ValueError("v2 requires x>0")
    t = 0
    while (x & 1) == 0:
        x >>= 1
        t += 1
    return t


def moments_from_counts_hist(vals: "object", freq: "object", q_list: Iterable[int]) -> Dict[int, int]:
    """Compute S_q = sum_r c[r]^q for q in q_list as Python ints, given a histogram."""
    vals_py = [int(v) for v in vals.tolist()]  # type: ignore[attr-defined]
    freq_py = [int(f) for f in freq.tolist()]  # type: ignore[attr-defined]
    out: Dict[int, int] = {}
    for q in q_list:
        s = 0
        for v, f in zip(vals_py, freq_py, strict=True):
            s += f * (v**q)
        out[int(q)] = int(s)
    return out


def enumerate_S_via_moddp(m_max: int, q_list: List[int], prog: Progress) -> Dict[int, Dict[int, int]]:
    """Return S[q][m] for m=0..m_max, computed exactly via modular DP."""
    out: Dict[int, Dict[int, int]] = {int(q): {} for q in q_list}
    for m in range(0, m_max + 1):
        c = counts_mod_fib(m, prog=prog)
        vals, freq = hist_from_counts(c)
        mom = moments_from_counts_hist(vals, freq, q_list=q_list)
        for q in q_list:
            out[int(q)][int(m)] = int(mom[int(q)])
        print(f"[2adic-odometer] moddp computed m={m}", flush=True)
    return out


@dataclass(frozen=True)
class RecSpec:
    q: int
    order: int
    m0: int
    coeffs: List[int]  # S(m)=sum_{i=1..d} coeffs[i-1]*S(m-i), valid for m>=m0


RECS: Dict[int, RecSpec] = {
    # q=4..8 from tab_fold_collision_moment_recursions.tex
    4: RecSpec(q=4, order=5, m0=5, coeffs=[2, 7, 0, 2, -2]),
    5: RecSpec(q=5, order=5, m0=5, coeffs=[2, 11, 8, 20, -10]),
    6: RecSpec(q=6, order=7, m0=7, coeffs=[2, 17, 28, 88, -26, 4, -4]),
    7: RecSpec(q=7, order=7, m0=7, coeffs=[2, 26, 74, 311, -34, 84, -42]),
    8: RecSpec(q=8, order=9, m0=9, coeffs=[2, 40, 174, 969, 2, 428, -174, 4, -4]),
    # q=9,10 from tab_fold_collision_moment_recursions_9_11.tex / _9_17.tex
    9: RecSpec(q=9, order=7, m0=9, coeffs=[2, 62, 386, 2819, 62, 900, -450]),
    10: RecSpec(q=10, order=9, m0=11, coeffs=[2, 96, 830, 7945, 2, 1852, -830, 4, -4]),
}


def extend_sequence_int(seq: List[int], rec: RecSpec, m_max: int) -> List[int]:
    """Extend integer sequence to m_max using the recurrence."""
    if m_max < 0:
        raise ValueError("m_max must be >= 0")
    d = rec.order
    if len(seq) <= m_max:
        seq = list(seq) + [0] * (m_max + 1 - len(seq))
    # Fill missing values up to rec.m0-1 must be already present.
    for m in range(rec.m0, m_max + 1):
        rhs = 0
        for i, c in enumerate(rec.coeffs, start=1):
            rhs += int(c) * int(seq[m - i])
        seq[m] = int(rhs)
    return seq


def extend_sequence_mod(seq: List[int], rec: RecSpec, m_max: int, mod: int) -> List[int]:
    """Extend sequence modulo mod to m_max using the recurrence."""
    if mod <= 0:
        raise ValueError("mod must be positive")
    d = rec.order
    if len(seq) <= m_max:
        seq = list(seq) + [0] * (m_max + 1 - len(seq))
    for m in range(rec.m0, m_max + 1):
        rhs = 0
        for i, c in enumerate(rec.coeffs, start=1):
            rhs += int(c) * int(seq[m - i])
        seq[m] = int(rhs % mod)
    return seq


def periodicity_holds(seq: List[int], start: int, period: int, order: int) -> bool:
    """Check seq[m+period]==seq[m] for m in [start..start+period+order-1]."""
    if period <= 0:
        raise ValueError("period must be positive")
    end = start + period + order
    if end + period > len(seq):
        raise ValueError("sequence too short for periodicity check")
    for m in range(start, end):
        if seq[m + period] != seq[m]:
            return False
    return True


def minimal_power_of_two_period(seq: List[int], start: int, period: int, order: int) -> int:
    """Reduce a power-of-two candidate by halving while periodicity holds."""
    p = int(period)
    while p % 2 == 0:
        half = p // 2
        if half <= 0:
            break
        if periodicity_holds(seq, start=start, period=half, order=order):
            p = half
        else:
            break
    return int(p)


def period_pred(q: int, k: int) -> int:
    if q == 4:
        return 2 ** max(1, k - 7)
    if q in {6, 10}:
        return 2 ** (k - 5)
    if q == 7:
        return 2 ** (k - 4)
    if q == 8:
        if k == 8:
            return 2
        if k in {9, 10}:
            return 4
        return 2 ** (k - 8)
    raise KeyError(f"no period formula for q={q}")


def k_min_pred(q: int) -> int:
    if q == 4:
        return 7
    if q in {6, 7, 10}:
        return 6
    if q == 8:
        return 8
    raise KeyError(f"no k_min for q={q}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit 2-adic odometer laws for Fold collision moments S_q(m).")
    parser.add_argument("--k-min", type=int, default=5)
    parser.add_argument("--k-max", type=int, default=20)
    parser.add_argument("--m-seed-max", type=int, default=20, help="Max m computed via moddp for seeding recurrences.")
    parser.add_argument("--m-v2-max", type=int, default=256, help="Max m for stabilized v2 checks (integer recurrence).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_moment_2adic_odometer_q4_10.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_moment_2adic_odometer_q4_10.tex"),
    )
    args = parser.parse_args()

    k_min = int(args.k_min)
    k_max = int(args.k_max)
    if k_min < 1 or k_max < k_min:
        raise SystemExit("invalid k range")

    # We audit the q-values that admit explicit odometer laws in the paper statements.
    q_formula = [4, 6, 7, 8, 10]
    q_all = list(q_formula)

    # Seed exact values by modular DP on a small m window.
    prog = Progress("2adic-odometer", every_seconds=15.0)
    S_seed = enumerate_S_via_moddp(m_max=int(args.m_seed_max), q_list=q_all, prog=prog)

    # Build integer sequences for stabilized v2 checks.
    S_int: Dict[int, List[int]] = {}
    for q in q_all:
        rec = RECS.get(q)
        if rec is None:
            raise SystemExit(f"missing recurrence for q={q}")
        # Initialize seq with seed values for m=0..m_seed_max, then extend by recurrence.
        m_seed_max = int(args.m_seed_max)
        init = [int(S_seed[q][m]) for m in range(0, m_seed_max + 1)]
        seq = extend_sequence_int(init, rec=rec, m_max=int(args.m_v2_max))
        S_int[q] = seq

    # Stabilized v2 / base congruence checks (as stated in the paper conclusions).
    # q=4
    for m in range(16, int(args.m_v2_max) + 1):
        x = int(S_int[4][m])
        if x % 64 != 32:
            raise SystemExit(f"[2adic-odometer] q=4 base class failed at m={m}: S4 mod64={x%64}")
        if v2(x) != 5:
            raise SystemExit(f"[2adic-odometer] q=4 v2 failed at m={m}: v2={v2(x)}")

    # q=6 and q=10
    for q in (6, 10):
        for m in range(13, int(args.m_v2_max) + 1):
            x = int(S_int[q][m])
            if x % 32 != 16:
                raise SystemExit(f"[2adic-odometer] q={q} base class failed at m={m}: mod32={x%32}")
            if v2(x) != 4:
                raise SystemExit(f"[2adic-odometer] q={q} v2 failed at m={m}: v2={v2(x)}")

    # q=8
    for m in range(19, int(args.m_v2_max) + 1):
        x = int(S_int[8][m])
        if x % 128 != 64:
            raise SystemExit(f"[2adic-odometer] q=8 base class failed at m={m}: mod128={x%128}")
        if v2(x) != 6:
            raise SystemExit(f"[2adic-odometer] q=8 v2 failed at m={m}: v2={v2(x)}")

    # q=7: v2 >= 5 for m>=13, and equality occurs at least once in the checked window.
    seen_eq5 = False
    for m in range(13, int(args.m_v2_max) + 1):
        x = int(S_int[7][m])
        if v2(x) < 5:
            raise SystemExit(f"[2adic-odometer] q=7 v2 lower bound failed at m={m}: v2={v2(x)}")
        if v2(x) == 5:
            seen_eq5 = True
    if not seen_eq5:
        raise SystemExit("[2adic-odometer] q=7: did not observe v2==5 in the checked window")

    # Periodicity / odometer checks.
    checks: Dict[str, object] = {
        "k_min": k_min,
        "k_max": k_max,
        "m_seed_max": int(args.m_seed_max),
        "m_v2_max": int(args.m_v2_max),
        "q_formula": q_formula,
        "results": {},
    }

    for q in q_formula:
        rec = RECS[q]
        d = rec.order
        q_res: Dict[str, object] = {"q": q, "k_checks": []}
        for k in range(k_min, k_max + 1):
            if k < k_min_pred(q):
                continue
            mod = 1 << k
            start = 3 * k - 2
            p_pred = int(period_pred(q, k))
            # Need enough length to check periodicity and minimality.
            m_end = start + 2 * p_pred + d + 5
            # Seed modulo values from exact seed, then extend by recurrence modulo 2^k.
            m_seed_max = int(args.m_seed_max)
            init_mod = [int(S_seed[q][m] % mod) for m in range(0, m_seed_max + 1)]
            seq_mod = extend_sequence_mod(init_mod, rec=rec, m_max=m_end, mod=mod)

            if not periodicity_holds(seq_mod, start=start, period=p_pred, order=d):
                raise SystemExit(f"[2adic-odometer] periodicity failed q={q} k={k} p={p_pred}")
            p_min = minimal_power_of_two_period(seq_mod, start=start, period=p_pred, order=d)
            if p_min != p_pred:
                raise SystemExit(
                    f"[2adic-odometer] minimal period mismatch q={q} k={k}: pred={p_pred} got={p_min}"
                )

            # Threshold minimality check: fail at start-1 for the same (predicted) period.
            if start - 1 >= 0 and periodicity_holds(seq_mod, start=start - 1, period=p_pred, order=d):
                raise SystemExit(f"[2adic-odometer] threshold not minimal at q={q} k={k}: start={start}")

            distinct = len(set(seq_mod[start : start + p_pred]))
            # q=4,6,10 claim injectivity on the orbit (distinct == period) in the stable regime.
            injective_expected = (q in {4, 6, 10} and (q != 4 or k >= 9))
            if injective_expected and distinct != p_pred:
                raise SystemExit(
                    f"[2adic-odometer] distinct count mismatch q={q} k={k}: distinct={distinct} period={p_pred}"
                )

            extra: Dict[str, object] = {}
            if q == 7:
                # Zero-orbit: exactly two solutions in one m-period.
                p_m = p_pred  # = 2^{k-4}
                zeros = [m for m in range(start, start + p_m) if seq_mod[m] == 0]
                residues = sorted({int(m % p_m) for m in zeros})
                # The two stable 2-adic roots (in Z_2) are:
                #   m ≡ 31488   (a nonnegative integer root),
                #   m ≡ -41279  (a genuinely 2-adic root).
                r1 = (31488) % p_m
                r2 = (-41279) % p_m
                expected = sorted({int(r1), int(r2)})
                if residues != expected:
                    raise SystemExit(
                        f"[2adic-odometer] q=7 zero residues mismatch k={k}: got={residues} expected={expected}"
                    )
                # Coverage: values are exactly all multiples of 2^5, each appearing twice.
                counts: Dict[int, int] = {}
                for m in range(start, start + p_m):
                    v = int(seq_mod[m])
                    if v % 32 != 0:
                        raise SystemExit(f"[2adic-odometer] q=7 non-multiple-of-32 at k={k} m={m}: v={v}")
                    counts[v] = counts.get(v, 0) + 1
                if len(counts) != (1 << (k - 5)):
                    raise SystemExit(
                        f"[2adic-odometer] q=7 reachable-class size mismatch k={k}: got={len(counts)}"
                    )
                if any(c != 2 for c in counts.values()):
                    bad = sorted({c for c in counts.values() if c != 2})
                    raise SystemExit(f"[2adic-odometer] q=7 multiplicity mismatch k={k}: bad_counts={bad[:5]}")
                extra["zero_residues_mod_2^(k-4)"] = expected
                extra["reachable_class_size"] = len(counts)

            q_res["k_checks"].append(
                {
                    "k": int(k),
                    "mod": int(mod),
                    "start": int(start),
                    "period_pred": int(p_pred),
                    "period_min": int(p_min),
                    "distinct_in_period": int(distinct),
                    **extra,
                }
            )
            print(f"[2adic-odometer] ok q={q} k={k} start={start} period={p_pred}", flush=True)
        checks["results"][str(q)] = q_res  # type: ignore[index]

    # Write JSON.
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(checks, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[2adic-odometer] wrote {jout}", flush=True)

    # Write summary LaTeX table (English-only by repository convention).
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{2-adic odometer fingerprints for Fold collision moments $S_q(m)$. "
        "We report stabilized $v_2$ and base congruence classes, and the eventual period of "
        "$m\\mapsto S_q(m)\\bmod 2^k$ after the universal threshold $m\\ge 3k-2$ (audited).}"
    )
    lines.append("\\label{tab:fold_collision_moment_2adic_odometer_q4_10}")
    lines.append("\\begin{tabular}{r l l}")
    lines.append("\\toprule")
    lines.append("$q$ & stabilized $v_2$ (large $m$) & eventual period mod $2^k$ (for $m\\ge 3k-2$)\\\\")
    lines.append("\\midrule")
    lines.append("$4$ & $v_2(S_4)=5$, $S_4\\equiv 32\\ (\\mathrm{mod}\\ 64)$ for $m\\ge 16$ & $2^{\\max(1,k-7)}$ ($k\\ge 7$)\\\\")
    lines.append("$6$ & $v_2(S_6)=4$, $S_6\\equiv 16\\ (\\mathrm{mod}\\ 32)$ for $m\\ge 13$ & $2^{k-5}$ ($k\\ge 6$)\\\\")
    lines.append(
        "$7$ & $v_2(S_7)\\ge 5$ for $m\\ge 13$ & $2^{k-4}$ ($k\\ge 6$); zeros at "
        "$m\\equiv 31488,\\,-41279\\ (\\mathrm{mod}\\ 2^{k-4})$\\\\"
    )
    lines.append("$8$ & $v_2(S_8)=6$, $S_8\\equiv 64\\ (\\mathrm{mod}\\ 128)$ for $m\\ge 19$ & $2$ ($k=8$), $4$ ($k=9,10$), $2^{k-8}$ ($k\\ge 11$)\\\\")
    lines.append("$10$ & $v_2(S_{10})=4$, $S_{10}\\equiv 16\\ (\\mathrm{mod}\\ 32)$ for $m\\ge 13$ & $2^{k-5}$ ($k\\ge 6$)\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[2adic-odometer] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

