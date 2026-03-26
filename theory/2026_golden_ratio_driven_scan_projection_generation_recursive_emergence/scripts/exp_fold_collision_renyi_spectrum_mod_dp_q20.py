#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Extend the Fold_m Renyi-q fingerprint to q<=20 using modular DP.

We compute residue counts c_m(r) mod F_{m+2} via:
  c_{i+1} = c_i + shift_{F_{i+2}}(c_i),  i=0..m-1,
then moments:
  S_q(m) = sum_r c_m(r)^q.

From S_q(m) we estimate the exponential base r_q by ratio convergence
and Aitken Δ^2 acceleration on the last three ratios.

Outputs:
  - artifacts/export/fold_collision_renyi_spectrum_mod_dp_q20.json
  - sections/generated/tab_fold_collision_renyi_spectrum_mod_dp_q20.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_mod_fib_dp import counts_mod_fib, hist_from_counts
from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


def moments_from_counts(c: np.ndarray, q_max: int) -> Dict[int, int]:
    if q_max < 2:
        raise ValueError("q_max must be >= 2")
    vals, freq = hist_from_counts(c)
    vals_py = [int(v) for v in vals.tolist()]
    freq_py = [int(f) for f in freq.tolist()]
    out: Dict[int, int] = {}
    for q in range(2, q_max + 1):
        s = 0
        for v, f in zip(vals_py, freq_py, strict=True):
            s += f * (v**q)
        out[q] = int(s)
    return out


def aitken_limit(x0: float, x1: float, x2: float) -> float | None:
    d1 = x1 - x0
    d2 = x2 - x1
    denom = d2 - d1
    if abs(denom) < 1e-18:
        return None
    return x0 - (d1 * d1) / denom


@dataclass(frozen=True)
class Row:
    q: int
    m_max: int
    r_q_est: float
    r_q_ratio_last: float
    h_q: float
    h_over_q: float
    rq_pow_1_over_q: float
    note: str


def write_table_tex(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Extended R\\'enyi fingerprint for Fold$_m$ via modular DP. "
        "We estimate $r_q$ from $S_q(m)=\\sum_x d_m(x)^q$ computed by residue DP modulo $F_{m+2}$, "
        "using ratio convergence and Aitken $\\Delta^2$ acceleration on the last three ratios.}"
    )
    lines.append("\\label{tab:fold_collision_renyi_spectrum_mod_dp_q20}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append("$q$ & $\\widehat r_q$ & $h_q=\\log(2^q/\\widehat r_q)$ & $h_q/q$ & $\\widehat r_q^{1/q}$ & note\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.q} & {r.r_q_est:.12f} & {r.h_q:.12f} & {r.h_over_q:.12f} & {r.rq_pow_1_over_q:.12f} & {r.note}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Extend Fold collision Renyi spectrum by modular DP (q<=20).")
    parser.add_argument("--m-min", type=int, default=8)
    parser.add_argument("--m-max", type=int, default=30)
    parser.add_argument("--q-max", type=int, default=20)
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_renyi_spectrum_mod_dp_q20.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_renyi_spectrum_mod_dp_q20.tex"),
    )
    args = parser.parse_args()

    if args.m_min < 2 or args.m_max < args.m_min:
        raise SystemExit("Require m_max >= m_min >= 2")
    if args.q_max < 2:
        raise SystemExit("Require q_max >= 2")

    prog = Progress("renyi-moddp-q20", every_seconds=20.0)

    qs = list(range(2, args.q_max + 1))
    S: Dict[int, Dict[int, int]] = {q: {} for q in qs}

    # Compute S_q(m) on the DP window.
    for m in range(args.m_min, args.m_max + 1):
        c = counts_mod_fib(m, prog=prog)
        mom = moments_from_counts(c, q_max=args.q_max)
        for q in qs:
            S[q][m] = mom[q]
        print(f"[renyi-moddp-q20] m={m} mod=F_{{m+2}}={len(c)}", flush=True)

    rows: List[Row] = []
    for q in qs:
        ms = sorted(S[q].keys())
        # Need last 4 points for ratios.
        if len(ms) < 4:
            raise SystemExit(f"Not enough m points for q={q}")
        m2, m1, m0, m_ = ms[-4], ms[-3], ms[-2], ms[-1]
        r0 = S[q][m0] / S[q][m1]
        r1 = S[q][m_] / S[q][m0]
        r2 = S[q][m1] / S[q][m2]
        # Use last three ratios in chronological order: (m2->m1),(m1->m0),(m0->m_)
        ait = aitken_limit(float(r2), float(r0), float(r1))
        rq_est = float(ait) if (ait is not None and ait > 0) else float(r1)
        hq = q * math.log(2.0) - math.log(rq_est)
        rows.append(
            Row(
                q=q,
                m_max=int(args.m_max),
                r_q_est=rq_est,
                r_q_ratio_last=float(r1),
                h_q=hq,
                h_over_q=hq / q,
                rq_pow_1_over_q=rq_est ** (1.0 / q),
                note=f"DP m<={args.m_max}",
            )
        )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    payload = {"m_min": int(args.m_min), "m_max": int(args.m_max), "q_max": int(args.q_max), "rows": [asdict(r) for r in rows]}
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[renyi-moddp-q20] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[renyi-moddp-q20] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

