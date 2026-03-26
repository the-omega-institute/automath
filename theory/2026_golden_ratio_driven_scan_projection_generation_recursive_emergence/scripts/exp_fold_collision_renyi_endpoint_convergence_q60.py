#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Endpoint convergence experiment for the Fold_m Renyi fingerprint (q up to 60).

We reuse the modular DP residue counts:
  c_m(r) = #{ omega in {0,1}^m : N(omega) ≡ r (mod F_{m+2}) },
then
  S_q(m) = sum_r c_m(r)^q.

To avoid huge integers for large q, we compute log S_q(m) via scaling by D_m=max_r c_m(r):
  log S_q(m) = q log D_m + log sum_r (c_m(r)/D_m)^q,
where the inner sum is in [1, F_{m+2}] and numerically stable in float64.

We estimate log r_q from a linear regression of log S_q(m) vs m on a fixed window of m values.
Then
  h_q/q = log 2 - (log r_q)/q
and we compare to the endpoint constant log(2/sqrt(phi)).

Outputs:
  - artifacts/export/fold_collision_renyi_endpoint_convergence_q60.json
  - sections/generated/tab_fold_collision_renyi_endpoint_convergence_q60.tex

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

from common_mod_fib_dp import counts_mod_fib
from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


def log_Sq_from_counts(c: np.ndarray, q: int) -> float:
    if q < 2:
        raise ValueError("q must be >= 2")
    D = int(np.max(c))
    if D <= 0:
        raise ValueError("max count must be positive")
    # scaled sum in float
    x = (c.astype(np.float64) / float(D)) ** float(q)
    s = float(np.sum(x))
    return float(q) * math.log(float(D)) + math.log(s)


@dataclass(frozen=True)
class Row:
    q: int
    m_min: int
    m_max: int
    log_rq_est: float
    h_over_q: float
    endpoint: float
    gap: float


def write_table_tex(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Endpoint convergence of $h_q/q$ for Fold$_m$ using modular DP moments $S_q(m)=\\sum_r c_m(r)^q$. "
        "We estimate $\\log r_q$ by a linear regression of $\\log S_q(m)$ versus $m$ on a fixed window, "
        "then report $h_q/q=\\log 2-(\\log r_q)/q$ and its gap to $\\log(2/\\sqrt{\\varphi})$.}"
    )
    lines.append("\\label{tab:fold_collision_renyi_endpoint_convergence_q60}")
    lines.append("\\begin{tabular}{r r r r r}")
    lines.append("\\toprule")
    lines.append("$q$ & window $m$ & $h_q/q$ (est.) & $\\log(2/\\sqrt{\\varphi})$ & gap\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.q} & $[{r.m_min},{r.m_max}]$ & {r.h_over_q:.10f} & {r.endpoint:.10f} & {r.gap:.2e}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Endpoint convergence for Fold Renyi spectrum (q up to 60).")
    parser.add_argument("--m-min", type=int, default=24)
    parser.add_argument("--m-max", type=int, default=30)
    parser.add_argument("--q-list", type=str, default="20,30,40,60")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_renyi_endpoint_convergence_q60.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_renyi_endpoint_convergence_q60.tex"),
    )
    args = parser.parse_args()

    if args.m_min < 2 or args.m_max < args.m_min:
        raise SystemExit("Require m_max >= m_min >= 2")

    qs = [int(s.strip()) for s in args.q_list.split(",") if s.strip()]
    if any(q < 2 for q in qs):
        raise SystemExit("All q must be >= 2")

    phi = (1.0 + 5.0**0.5) / 2.0
    endpoint = math.log(2.0 / math.sqrt(phi))

    prog = Progress("renyi-endpoint-q60", every_seconds=20.0)

    ms = list(range(int(args.m_min), int(args.m_max) + 1))
    # Cache log S_q(m) values.
    logS: Dict[int, Dict[int, float]] = {q: {} for q in qs}

    for m in ms:
        c = counts_mod_fib(m, prog=prog)
        for q in qs:
            logS[q][m] = log_Sq_from_counts(c, q=q)
        print(f"[renyi-endpoint-q60] m={m} done (mod={len(c)})", flush=True)

    rows: List[Row] = []
    for q in qs:
        xs = np.array(ms, dtype=np.float64)
        ys = np.array([logS[q][m] for m in ms], dtype=np.float64)
        slope, _intercept = np.polyfit(xs, ys, deg=1)
        log_rq = float(slope)
        h_over_q = math.log(2.0) - log_rq / float(q)
        rows.append(
            Row(
                q=int(q),
                m_min=int(args.m_min),
                m_max=int(args.m_max),
                log_rq_est=log_rq,
                h_over_q=h_over_q,
                endpoint=endpoint,
                gap=float(endpoint - h_over_q),
            )
        )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "m_min": int(args.m_min),
        "m_max": int(args.m_max),
        "q_list": qs,
        "endpoint": endpoint,
        "rows": [asdict(r) for r in rows],
    }
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[renyi-endpoint-q60] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[renyi-endpoint-q60] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

