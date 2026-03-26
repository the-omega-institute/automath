#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Compute exact q-breakpoints for the Chernoff tail-quantile certificate.

Given audited Perron roots (r_q), define the q-candidate certificate:

  gamma_m^(q)(eps) = ( log r_q - log 2 + (1/m) log(1/eps) ) / (q-1).

The tie point between the q-candidate and (q+1)-candidate is the unique m>0
solving gamma_m^(q)(eps) = gamma_m^(q+1)(eps), namely:

  m_{q->q+1}(eps) = log(1/eps) / A_q

where

  A_q := (q-1)(log r_{q+1} - log 2) - q(log r_q - log 2).

Outputs:
  - artifacts/export/fold_collision_qstar_breakpoints_eps1e6_q2_20.json
  - sections/generated/tab_fold_collision_qstar_breakpoints_eps1e6_q2_20.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class Row:
    q: int
    q_next: int
    A_q: float
    m_break: float


def _load_rq_from_json(path: Path, *, q_max: int) -> Dict[int, float]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    rows = payload.get("rows", [])
    out: Dict[int, float] = {}
    for r in rows:
        q = int(r.get("q"))
        if q < 2 or q > int(q_max):
            continue
        # Prefer the naming used by exp_fold_collision_renyi_spectrum_mod_dp_q20.py.
        if "r_q_est" in r:
            out[q] = float(r["r_q_est"])
        elif "r_q" in r:
            out[q] = float(r["r_q"])
        elif "rq" in r:
            out[q] = float(r["rq"])
    return out


def _load_rq_from_tex(path: Path, *, q_max: int) -> Dict[int, float]:
    # Matches rows like:
    #   2 & 2.481194304092 & ... \\
    row_re = re.compile(r"^\s*(\d+)\s*&\s*([0-9]+(?:\.[0-9]+)?)\s*&")
    out: Dict[int, float] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        m = row_re.match(line)
        if not m:
            continue
        q = int(m.group(1))
        if q < 2 or q > int(q_max):
            continue
        out[q] = float(m.group(2))
    return out


def _load_rq(*, q_max: int) -> Tuple[Dict[int, float], str]:
    # Primary source: JSON exported by the DP r_q audit step.
    jpath = export_dir() / "fold_collision_renyi_spectrum_mod_dp_q20.json"
    if jpath.is_file():
        rq = _load_rq_from_json(jpath, q_max=q_max)
        if len(rq) >= 2:
            return rq, str(jpath)

    # Fallback: parse the generated TeX table (committed in many worktrees).
    tpath = generated_dir() / "tab_fold_collision_renyi_spectrum_mod_dp_q20.tex"
    if tpath.is_file():
        rq = _load_rq_from_tex(tpath, q_max=q_max)
        if len(rq) >= 2:
            return rq, str(tpath)

    raise FileNotFoundError(
        "Could not load r_q: missing "
        f"{jpath} and {tpath} (or both were empty/unparseable)."
    )


def _write_table_tex(path: Path, *, rows: List[Row], eps: float, q_max: int) -> None:
    def latex_eps(x: float) -> str:
        if not (x > 0.0) or (not math.isfinite(x)):
            return str(x)
        lg10 = math.log10(x)
        k = int(round(lg10))
        if abs(lg10 - float(k)) < 1e-12:
            return f"10^{{{k}}}"
        # Avoid scientific notation inside TeX math mode.
        s = f"{x:.12f}".rstrip("0").rstrip(".")
        return s if s else "0"

    eps_tex = latex_eps(eps)

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Exact breakpoints for the Chernoff-optimal $q^\\star(m,\\varepsilon)$ "
        f"at $\\varepsilon={eps_tex}$, computed solely from the audited $r_q$ table (DP, $q\\le {q_max}$)."
        "}"
    )
    lines.append("\\label{tab:fold_collision_qstar_breakpoints_eps1e6_q2_20}")
    lines.append("\\begin{tabular}{c r}")
    lines.append("\\toprule")
    lines.append(f"tie between $q$ and $q{{+}}1$ & $m_{{q\\to q+1}}({eps_tex})$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(f"${r.q}\\leftrightarrow {r.q_next}$ & {r.m_break:.2f}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Compute exact q-breakpoints m_{q->q+1}(eps) from audited r_q.")
    ap.add_argument("--eps", type=float, default=1e-6)
    ap.add_argument("--q-max", type=int, default=20)
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_qstar_breakpoints_eps1e6_q2_20.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_qstar_breakpoints_eps1e6_q2_20.tex"),
    )
    args = ap.parse_args()

    eps = float(args.eps)
    q_max = int(args.q_max)
    if not (0.0 < eps < 1.0):
        raise SystemExit("Require --eps in (0,1)")
    if q_max < 3:
        raise SystemExit("Require --q-max >= 3 (need at least q=2,3)")

    rq_by_q, rq_source = _load_rq(q_max=q_max)
    if 2 not in rq_by_q:
        raise SystemExit("Missing r_2 in audited table")
    if any(q not in rq_by_q for q in range(2, q_max + 1)):
        missing = [q for q in range(2, q_max + 1) if q not in rq_by_q]
        raise SystemExit(f"Missing r_q entries: {missing}")

    log2 = math.log(2.0)
    log1eps = math.log(1.0 / eps)

    rows: List[Row] = []
    for q in range(q_max - 1, 1, -1):
        rq = float(rq_by_q[q])
        rq_next = float(rq_by_q[q + 1])
        A_q = (q - 1) * (math.log(rq_next) - log2) - q * (math.log(rq) - log2)
        if not (A_q > 0.0) or (not math.isfinite(A_q)):
            raise SystemExit(f"Non-positive/invalid A_q for q={q}: {A_q}")
        m_break = log1eps / A_q
        rows.append(Row(q=int(q), q_next=int(q + 1), A_q=float(A_q), m_break=float(m_break)))

    # Write JSON payload.
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "params": {"eps": float(eps), "q_max": int(q_max), "rq_source": str(rq_source)},
        "rq_by_q": {str(q): float(rq_by_q[q]) for q in range(2, q_max + 1)},
        "rows": [asdict(r) for r in rows],
    }
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[qstar-breakpoints] wrote {jout}", flush=True)

    # Write TeX table.
    tout = Path(args.tex_out)
    _write_table_tex(tout, rows=rows, eps=eps, q_max=q_max)
    print(f"[qstar-breakpoints] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

